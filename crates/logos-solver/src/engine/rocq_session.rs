//! Disposable, incremental *negative* diagnostics. A REPL can reject a candidate,
//! but can never publish an object, advance a checkpoint, or certify success.
//! Full checks still require the ordinary compiler. Explicit prefix probes
//! return advisory goals only and never fall through to compilation.
//!
//! The launcher supplies the existing empty-root Rocq sandbox. One session is
//! retained per broker, keyed by logical module and immutable dependency manifest.
//! Protocol ambiguity falls back only for full checks; timeout destroys the session.

use std::io::{self, Read, Write};
use std::os::fd::OwnedFd;
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;
use std::process::{Child, Command, Stdio};
use std::sync::Arc;
use std::time::{Duration, Instant};

const MAX_RESPONSE_BYTES: usize = 4 * 1024 * 1024;
const MAX_SENTENCE_BYTES: usize = 64 * 1024;

/// Process-local identity, never serialized as proof evidence. Compare exact
/// manifest bytes rather than hashing an already content-bound manifest again.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct SessionKey {
    manifest: Arc<[u8]>,
    logical_name: String,
}

impl SessionKey {
    pub fn new(manifest: Vec<u8>, logical_name: String) -> Self {
        Self {
            manifest: manifest.into(),
            logical_name,
        }
    }
}

#[derive(Default)]
pub(super) struct IncrementalDiagnostics {
    session: Option<Session>,
    retry_key: Option<SessionKey>,
}

pub(super) struct Diagnostic {
    pub rejection: Option<String>,
    pub goals: Option<String>,
    pub reused: usize,
    pub executed: usize,
}

impl IncrementalDiagnostics {
    /// First-try successes need only one ordinary compilation. Start a REPL
    /// only after a failed compilation in this exact dependency/module context.
    pub fn prepare(&mut self, key: &SessionKey) -> bool {
        if self.session.as_ref().is_some_and(|s| s.key != *key) {
            self.session = None;
        }
        self.session.is_some() || self.retry_key.as_ref() == Some(key)
    }

    pub fn observe_compiler(&mut self, key: &SessionKey, exit_code: Option<i32>) {
        self.retry_key = (exit_code == Some(1)).then(|| key.to_owned());
        if !matches!(exit_code, Some(0 | 1)) {
            self.session = None;
        }
    }

    pub fn check(
        &mut self,
        key: &SessionKey,
        source: &str,
        command: &mut Command,
        deadline: Instant,
    ) -> io::Result<Diagnostic> {
        self.run(key, source, command, deadline, false)
    }

    pub fn probe(
        &mut self,
        key: &SessionKey,
        source: &str,
        command: &mut Command,
        deadline: Instant,
    ) -> io::Result<Diagnostic> {
        self.run(key, source, command, deadline, true)
    }

    fn run(
        &mut self,
        key: &SessionKey,
        source: &str,
        command: &mut Command,
        deadline: Instant,
        show_goals: bool,
    ) -> io::Result<Diagnostic> {
        self.retry_key = None;
        let Some(sentences) = sentences(source) else {
            // Unsupported syntax must not become a spurious proof failure.
            self.session = None;
            return Err(io::Error::other(
                "source requires ordinary compiler parsing",
            ));
        };
        if self
            .session
            .as_ref()
            .is_none_or(|s| s.key != *key || s.rewind_crosses_closed_proof(&sentences))
        {
            self.session = None;
            self.session = Some(Session::start(key, command, deadline)?);
        }
        let result = self
            .session
            .as_mut()
            .unwrap()
            .check(&sentences, deadline, show_goals);
        if result.is_err() {
            self.session = None;
            self.retry_key = None;
        }
        result
    }
}

struct Session {
    key: SessionKey,
    child: Child,
    input: UnixStream,
    output: UnixStream,
    initial: u64,
    in_proof: bool,
    // Only successfully executed sentences enter the reusable prefix.
    history: Vec<VerifiedSentence>,
}

struct VerifiedSentence {
    source: String,
    state: u64,
    closes_proof: bool,
}

struct Reply {
    text: String,
    state: u64,
    in_proof: bool,
}

impl Reply {
    fn failed(&self) -> bool {
        self.text
            .lines()
            .any(|line| line.starts_with("Error:") || line.starts_with("Anomaly:"))
    }
}

fn remaining(deadline: Instant) -> io::Result<Duration> {
    let remaining = deadline.saturating_duration_since(Instant::now());
    if remaining.is_zero() {
        Err(io::Error::new(
            io::ErrorKind::TimedOut,
            "incremental Rocq deadline exceeded",
        ))
    } else {
        Ok(remaining)
    }
}

fn timeout_error(error: io::Error) -> io::Error {
    if error.kind() == io::ErrorKind::WouldBlock {
        io::Error::new(
            io::ErrorKind::TimedOut,
            "incremental Rocq deadline exceeded",
        )
    } else {
        error
    }
}

impl Session {
    fn common_prefix(&self, sentences: &[&str]) -> usize {
        self.history
            .iter()
            .zip(sentences)
            .take_while(|(previous, current)| previous.source == **current)
            .count()
    }

    fn rewind_crosses_closed_proof(&self, sentences: &[&str]) -> bool {
        // Rocq can acknowledge BackTo into a closed proof with its old prompt
        // while Show still reports "requires an open proof". Rebuild instead
        // of trusting that state number across a proof-closing transition.
        self.history[self.common_prefix(sentences)..]
            .iter()
            .any(|s| s.closes_proof)
    }

    fn start(key: &SessionKey, command: &mut Command, deadline: Instant) -> io::Result<Self> {
        let (input, child_input) = UnixStream::pair()?;
        let (output, child_output) = UnixStream::pair()?;
        command
            .stdin(Stdio::from(OwnedFd::from(child_input)))
            .stdout(Stdio::from(OwnedFd::from(child_output.try_clone()?)))
            .stderr(Stdio::from(OwnedFd::from(child_output)))
            .process_group(0);
        // A killed solver must not leave a shell and an infinite Rocq tactic
        // behind. The launcher's bwrap --die-with-parent covers its descendants.
        let parent = std::process::id() as libc::pid_t;
        unsafe {
            command.pre_exec(move || {
                if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL) == -1 {
                    return Err(io::Error::last_os_error());
                }
                if libc::getppid() != parent {
                    return Err(io::Error::from_raw_os_error(libc::ESRCH));
                }
                Ok(())
            });
        }
        let child = command.spawn()?;
        // Command retains its Stdio handles after spawn. Drop those copies so
        // child exit produces EOF instead of an artificial read timeout.
        command
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let mut session = Self {
            key: key.to_owned(),
            child,
            input,
            output,
            initial: 0,
            in_proof: false,
            history: Vec::new(),
        };
        let reply = session.read_reply(deadline)?;
        if reply.failed() || reply.in_proof {
            return Err(io::Error::other("invalid initial Rocq prompt"));
        }
        session.initial = reply.state;
        Ok(session)
    }

    fn read_reply(&mut self, deadline: Instant) -> io::Result<Reply> {
        let mut bytes = Vec::new();
        let mut chunk = [0_u8; 8192];
        loop {
            self.output.set_read_timeout(Some(remaining(deadline)?))?;
            let count = self.output.read(&mut chunk).map_err(timeout_error)?;
            if count == 0 {
                return Err(io::Error::other("Rocq exited before its next prompt"));
            }
            bytes.extend_from_slice(&chunk[..count]);
            if bytes.len() > MAX_RESPONSE_BYTES {
                return Err(io::Error::other("incremental Rocq response limit exceeded"));
            }
            if bytes.windows(b"</prompt>".len()).any(|w| w == b"</prompt>") {
                let text = String::from_utf8(bytes)
                    .map_err(|_| io::Error::other("non-UTF-8 Rocq response"))?;
                return parse_reply(&text);
            }
        }
    }

    fn execute(&mut self, sentence: &str, deadline: Instant) -> io::Result<Reply> {
        self.input.set_write_timeout(Some(remaining(deadline)?))?;
        self.input
            .write_all(sentence.as_bytes())
            .map_err(timeout_error)?;
        self.input.write_all(b"\n").map_err(timeout_error)?;
        let reply = self.read_reply(deadline)?;
        self.in_proof = reply.in_proof;
        Ok(reply)
    }

    fn check(
        &mut self,
        sentences: &[&str],
        deadline: Instant,
        show_goals: bool,
    ) -> io::Result<Diagnostic> {
        let common = self.common_prefix(sentences);
        if common < self.history.len() {
            let target = if common == 0 {
                self.initial
            } else {
                self.history[common - 1].state
            };
            let reply = self.execute(&format!("BackTo {target}."), deadline)?;
            if reply.failed() || reply.state != target {
                return Err(io::Error::other(
                    "Rocq could not restore the exact prefix state",
                ));
            }
            self.history.truncate(common);
        }
        for (index, sentence) in sentences.iter().enumerate().skip(common) {
            let was_in_proof = self.in_proof;
            let reply = self.execute(sentence, deadline)?;
            if reply.failed() {
                let previous = self
                    .history
                    .last()
                    .map_or(self.initial, |entry| entry.state);
                if reply.state != previous {
                    // For example, `idtac "Error: ..."` is user output, not a
                    // rejected tactic. Never turn ambiguous output into failure.
                    return Err(io::Error::other(
                        "error-like output advanced the Rocq state",
                    ));
                }
                let line = 1 + sentences[..index]
                    .iter()
                    .map(|s| s.bytes().filter(|b| *b == b'\n').count())
                    .sum::<usize>();
                let mut rejection = format!(
                    "Incremental Rocq diagnostic near source line {line}:\n{}",
                    reply.text
                );
                // Querying the state is advisory only. A failed query must not
                // hide the actual tactic error or turn a failure into success.
                if reply.in_proof {
                    let goals = self.execute("Show.", deadline)?;
                    if !goals.failed() {
                        rejection.push_str("\nCurrent goals:\n");
                        rejection.push_str(&goals.text);
                    }
                }
                return Ok(Diagnostic {
                    rejection: Some(rejection),
                    goals: None,
                    reused: common,
                    executed: index + 1 - common,
                });
            }
            self.history.push(VerifiedSentence {
                source: (*sentence).to_owned(),
                state: reply.state,
                closes_proof: was_in_proof && !reply.in_proof,
            });
        }
        let goals = if show_goals && self.in_proof {
            let previous = self
                .history
                .last()
                .map_or(self.initial, |entry| entry.state);
            let reply = self.execute("Show.", deadline)?;
            if reply.failed() || reply.state != previous {
                return Err(io::Error::other("could not inspect the exact prefix goals"));
            }
            Some(reply.text)
        } else {
            None
        };
        Ok(Diagnostic {
            rejection: None,
            goals,
            reused: common,
            executed: sentences.len() - common,
        })
    }
}

impl Drop for Session {
    fn drop(&mut self) {
        // EOF normally lets Rocq and the shell's scratch-cleanup trap exit.
        // A stuck tactic also receives TERM as a process group; KILL is bounded.
        let _ = self.input.shutdown(std::net::Shutdown::Write);
        unsafe {
            libc::kill(-(self.child.id() as i32), libc::SIGTERM);
        }
        let until = Instant::now() + Duration::from_millis(200);
        while Instant::now() < until {
            if matches!(self.child.try_wait(), Ok(Some(_))) {
                return;
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        unsafe {
            libc::kill(-(self.child.id() as i32), libc::SIGKILL);
        }
        let _ = self.child.wait();
    }
}

fn parse_reply(text: &str) -> io::Result<Reply> {
    let bad = || io::Error::other("ambiguous Rocq emacs protocol; use ordinary compiler");
    let (body, prompt) = text.split_once("<prompt>").ok_or_else(bad)?;
    let prompt = prompt.strip_suffix("</prompt>").ok_or_else(bad)?;
    let (_, state_and_proofs) = prompt.split_once(" < ").ok_or_else(bad)?;
    let (state, proofs) = state_and_proofs.split_once(" |").ok_or_else(bad)?;
    let (proofs, depth) = proofs.rsplit_once("| ").ok_or_else(bad)?;
    depth
        .strip_suffix(" < ")
        .ok_or_else(bad)?
        .parse::<u64>()
        .map_err(|_| bad())?;
    Ok(Reply {
        text: body.to_owned(),
        state: state.parse().map_err(|_| bad())?,
        in_proof: !proofs.is_empty(),
    })
}

/// Conservative lexical framing, not a second Rocq parser. Respect strings,
/// nested comments, qualified names, decimals, and standalone proof bullets.
/// Anything incomplete/unsupported returns None; only full checks may fall back.
fn sentences(source: &str) -> Option<Vec<&str>> {
    sentences_through(source, None)
}

/// Stop framing at the requested complete sentence; never inspect the suffix.
pub(super) fn prefix_through(source: &str, count: usize) -> Option<&str> {
    if count == 0 {
        return None;
    }
    let prefix = sentences_through(source, Some(count))?;
    (prefix.len() == count).then(|| &source[..prefix.iter().map(|s| s.len()).sum()])
}

fn sentences_through(source: &str, limit: Option<usize>) -> Option<Vec<&str>> {
    let bytes = source.as_bytes();
    let mut result = Vec::new();
    let (mut start, mut i, mut depth) = (0, 0, 0_usize);
    let (mut quoted, mut comment_quoted, mut substantive) = (false, false, false);
    while i < bytes.len() {
        let pair = bytes.get(i..i + 2);
        if depth > 0 {
            // Rocq also recognizes strings inside comments: a quoted "*)"
            // must not terminate the comment and expose fake sentence breaks.
            if comment_quoted {
                if pair == Some(b"\"\"") {
                    i += 2;
                    continue;
                }
                if bytes[i] == b'"' {
                    comment_quoted = false;
                }
                i += 1;
            } else if bytes[i] == b'"' {
                comment_quoted = true;
                i += 1;
            } else if pair == Some(b"(*") {
                depth += 1;
                i += 2;
            } else if pair == Some(b"*)") {
                depth -= 1;
                i += 2;
            } else {
                i += 1;
            }
            continue;
        }
        if quoted {
            if pair == Some(b"\"\"") {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                quoted = false;
            }
            i += 1;
            continue;
        }
        if pair == Some(b"(*") {
            depth = 1;
            i += 2;
            continue;
        }
        if bytes[i] == b'"' {
            quoted = true;
            substantive = true;
            i += 1;
            continue;
        }
        if bytes[i].is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if substantive && matches!(bytes[i], b'{' | b'}') {
            // Goal-selector braces (e.g. `all: {`) are commands, but term
            // braces are not. Leave these grammar-dependent cases to Rocq.
            return None;
        }
        if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' {
            let word = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            if matches!(
                &source[word..i],
                "Back" | "BackTo" | "Reset" | "Restart" | "Undo" | "Quit" | "Drop" | "Load"
            ) {
                return None;
            }
            substantive = true;
            continue;
        }
        let boundary = if !substantive && matches!(bytes[i], b'-' | b'+' | b'*' | b'{' | b'}') {
            let bullet = bytes[i];
            i += 1;
            if !matches!(bullet, b'{' | b'}') {
                while bytes.get(i) == Some(&bullet) {
                    i += 1;
                }
            }
            true
        } else if bytes[i] == b'.' {
            if pair == Some(b"..") {
                return None;
            }
            i += 1;
            i == bytes.len() || bytes[i].is_ascii_whitespace() || bytes.get(i..i + 2) == Some(b"(*")
        } else {
            substantive = true;
            i += 1;
            false
        };
        if boundary {
            if i - start > MAX_SENTENCE_BYTES {
                return None;
            }
            result.push(&source[start..i]);
            if limit == Some(result.len()) {
                return Some(result);
            }
            start = i;
            substantive = false;
        }
    }
    if quoted || depth > 0 || substantive {
        return None;
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prefix_framing_does_not_parse_or_include_the_suffix() {
        let prefix = "Lemma p : True. Proof.";
        for suffix in [
            " exact I. Qed.",
            " all: {",
            " (* unfinished",
            " Load evil.",
            " ..",
        ] {
            let source = format!("{prefix}{suffix}");
            assert_eq!(prefix_through(&source, 2), Some(prefix));
        }
        assert_eq!(prefix_through(prefix, 0), None);
        assert_eq!(prefix_through(prefix, 3), None);
        assert_eq!(prefix_through("Lemma p : { n : nat | True }.", 1), None);
        assert_eq!(
            prefix_through(
                "Check Nat.add. (* nested (* . *) *) Check \".\". unfinished",
                2
            ),
            Some("Check Nat.add. (* nested (* . *) *) Check \".\".")
        );
        assert_eq!(
            prefix_through("Goal True. Proof. - { exact I. } Qed.", 4),
            Some("Goal True. Proof. - {")
        );
        assert_eq!(prefix_through("Check 1.2. Check 3.", 1), Some("Check 1.2."));
    }

    fn key(manifest: &str) -> SessionKey {
        SessionKey::new(
            manifest.as_bytes().to_vec(),
            "LogosGenerated.Problem".to_owned(),
        )
    }

    #[test]
    fn session_identity_compares_exact_manifest_bytes_and_module() {
        let mut session = IncrementalDiagnostics::default();
        let original = key("manifest-a");
        session.observe_compiler(&original, Some(1));
        // Equal bytes from a separate allocation are the same environment.
        assert!(session.prepare(&key("manifest-a")));
        assert!(!session.prepare(&key("manifest-b")));
        let other_module = SessionKey::new(
            b"manifest-a".to_vec(),
            "LogosGenerated.ProofModules.Helper".to_owned(),
        );
        assert!(!session.prepare(&other_module));
        assert!(session.prepare(&original.clone()));
    }

    #[test]
    fn frames_comments_strings_names_bullets_and_braces() {
        let text = "(* outer (* nested. *) *) From A.B Require Import C.\nLemma x : True /\\ True. Proof. split.\n- { exact I. }\n- idtac \"a. \"\"b\". exact I. Qed. (* tail *)";
        let parts = sentences(text).unwrap();
        assert_eq!(parts.len(), 12);
        assert_eq!(
            parts[0],
            "(* outer (* nested. *) *) From A.B Require Import C."
        );
        assert_eq!(parts[4], "\n-");
        assert_eq!(parts[5], " {");
        assert_eq!(parts[9], " idtac \"a. \"\"b\".");
        assert_eq!(sentences("Check 1.25."), Some(vec!["Check 1.25."]));
        assert_eq!(
            sentences("Qed.(* comment *) Check nat."),
            Some(vec!["Qed.", "(* comment *) Check nat."])
        );
        assert_eq!(
            sentences("(* \"*)\" Check False. *) Check True."),
            Some(vec!["(* \"*)\" Check False. *) Check True."])
        );
    }

    #[test]
    fn unsupported_input_uses_compiler() {
        for text in [
            "exact I",
            "(*",
            "Check \"x",
            "BackTo 3.",
            "Reset Initial.",
            "exact I...",
            "all: { exact I. }",
        ] {
            assert!(sentences(text).is_none(), "{text}");
        }
        assert!(sentences("idtac \"BackTo\". (* Reset *)").is_some());
    }

    #[test]
    fn cold_successes_do_not_start_a_session() {
        let mut session = IncrementalDiagnostics::default();
        assert!(!session.prepare(&key("a")));
        session.observe_compiler(&key("a"), Some(0));
        assert!(!session.prepare(&key("a")));
        session.observe_compiler(&key("a"), Some(1));
        assert!(session.prepare(&key("a")));
        assert!(!session.prepare(&key("b")));
        session.observe_compiler(&key("a"), Some(124));
        assert!(!session.prepare(&key("a")));
    }

    #[test]
    fn reads_prompt_and_rejects_ambiguous_framing() {
        let reply = parse_reply("Error: bad tactic\n<prompt>x < 12 |x| 0 < </prompt>").unwrap();
        assert!(reply.failed());
        assert!(reply.in_proof);
        assert_eq!(reply.state, 12);
        assert!(parse_reply("<prompt>Rocq < 1 || 0 < </prompt>junk").is_err());
        assert!(parse_reply("<prompt>Rocq < nope || 0 < </prompt>").is_err());
    }

    fn real_command() -> Command {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let binary = std::env::var_os("LOGOS_TEST_ROCQ")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| root.join(".opam-rocq/_opam/bin/rocq"));
        let mut command = Command::new(binary);
        command.args(["repl", "-q", "-emacs", "-async-proofs", "off"]);
        command
    }

    #[test]
    #[ignore = "requires a local Rocq installation"]
    fn real_rocq_reuses_failed_prefix_rolls_back_and_invalidates() {
        let mut session = IncrementalDiagnostics::default();
        let mut command = real_command();
        let deadline = Instant::now() + Duration::from_secs(20);
        let first = session
            .check(
                &key("env1"),
                "Lemma x : True. Proof. exact 0. Qed.",
                &mut command,
                deadline,
            )
            .unwrap();
        assert!(first.rejection.unwrap().contains("True"));
        let repaired = session
            .check(
                &key("env1"),
                "Lemma x : True. Proof. exact I. Qed.",
                &mut command,
                deadline,
            )
            .unwrap();
        assert!(repaired.rejection.is_none());
        assert_eq!(repaired.reused, 2);
        let changed = session
            .check(
                &key("env1"),
                "Lemma x : True. Proof. apply I. Qed.",
                &mut command,
                deadline,
            )
            .unwrap();
        assert!(changed.rejection.is_none());
        assert_eq!(
            changed.reused, 0,
            "rewind across Qed must rebuild the session"
        );
        let fresh = session
            .check(
                &key("env2"),
                "Lemma x : True. Proof. exact I. Qed.",
                &mut command,
                deadline,
            )
            .unwrap();
        assert!(fresh.rejection.is_none());
        assert_eq!(fresh.reused, 0);
    }

    #[test]
    #[ignore = "requires a local Rocq installation"]
    fn real_rocq_timeout_discards_state() {
        let mut session = IncrementalDiagnostics::default();
        let mut command = real_command();
        let error = session
            .check(
                &key("env"),
                "Lemma x : True. Proof. repeat (pose proof I). Qed.",
                &mut command,
                Instant::now() + Duration::from_millis(200),
            )
            .err()
            .unwrap();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
        assert!(session.session.is_none());
        let repaired = session
            .check(
                &key("env"),
                "Lemma x : True. Proof. exact I. Qed.",
                &mut command,
                Instant::now() + Duration::from_secs(10),
            )
            .unwrap();
        assert!(repaired.rejection.is_none());
        assert_eq!(repaired.reused, 0);
    }

    #[test]
    #[ignore = "requires a local Rocq installation"]
    fn real_rocq_ambiguous_output_falls_back_and_complex_proofs_replay() {
        let mut session = IncrementalDiagnostics::default();
        let mut command = real_command();
        let deadline = Instant::now() + Duration::from_secs(20);
        let ambiguous = session.check(
            &key("env"),
            "Lemma x : True. Proof. idtac \"Error: just text\". exact I. Qed.",
            &mut command,
            deadline,
        );
        if let Ok(diagnostic) = ambiguous {
            // Rocq versions may wrap idtac output in <infomsg>, in which case
            // it is already unambiguous. It must never be a negative verdict.
            assert!(diagnostic.rejection.is_none());
        }
        let proof =
            "(* \"*)\" *) Lemma x : True /\\ True. Proof. split. - { exact I. } - exact I. Qed.";
        let initial = session
            .check(
                &key("env"),
                proof.trim_end_matches(" Qed."),
                &mut command,
                deadline,
            )
            .unwrap();
        assert!(initial.rejection.is_none());
        let revised = proof.replace("- exact I.", "- apply I.");
        let revised = session
            .check(&key("env"), &revised, &mut command, deadline)
            .unwrap();
        assert!(revised.rejection.is_none());
        assert!(revised.reused > 5);
    }
}
