//! Disposable, incremental *negative* diagnostics. A REPL can reject a candidate,
//! but can never publish an object, advance a checkpoint, or certify success.
//! Full checks still require the ordinary compiler. Explicit prefix probes
//! return advisory goals only and never fall through to compilation.
//!
//! The launcher supplies the existing empty-root Rocq sandbox. A bounded LRU
//! pool per broker separates candidates under the immutable dependency manifest.
//! Protocol ambiguity falls back only for full checks; timeout destroys the session.

use std::collections::VecDeque;
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
    candidate_path: String,
}

impl SessionKey {
    pub fn new(manifest: Vec<u8>, logical_name: String) -> Self {
        Self {
            manifest: manifest.into(),
            candidate_path: logical_name.clone(),
            logical_name,
        }
    }

    pub fn for_candidate(mut self, path: &str) -> Self {
        self.candidate_path = path.to_owned();
        self
    }
}

/// Per-broker retention limits, independent of benchmark worker count. The RSS
/// limit is enforced between requests, not a hard limit on an executing tactic.
#[derive(Clone, Copy, Debug)]
pub(crate) struct SessionLimits {
    pub max_sessions: usize,
    pub retained_rss_mib: u64,
}

impl Default for SessionLimits {
    fn default() -> Self {
        Self {
            max_sessions: 0,
            retained_rss_mib: 1024,
        }
    }
}

pub(super) struct IncrementalDiagnostics {
    // Least recently used first; requests still execute strictly sequentially.
    sessions: VecDeque<Session>,
    retry_key: Option<SessionKey>,
    limits: SessionLimits,
}

impl Default for IncrementalDiagnostics {
    fn default() -> Self {
        Self::new(SessionLimits::default())
    }
}

pub(super) struct Diagnostic {
    pub rejection: Option<String>,
    pub goals: Option<String>,
    pub reused: usize,
    pub executed: usize,
}

impl IncrementalDiagnostics {
    pub fn new(limits: SessionLimits) -> Self {
        Self {
            sessions: VecDeque::new(),
            retry_key: None,
            limits,
        }
    }

    pub fn clear(&mut self) {
        self.sessions.clear();
        self.retry_key = None;
    }

    fn synchronize(&mut self, key: &SessionKey) {
        // Do not guess a smaller dependency closure. Every cached process saw
        // a snapshot of the entire manifest; any change invalidates that view.
        self.sessions.retain(|s| s.key.manifest == key.manifest);
        if self
            .retry_key
            .as_ref()
            .is_some_and(|k| k.manifest != key.manifest)
        {
            self.retry_key = None;
        }
        self.enforce_retention();
    }

    fn discard(&mut self, key: &SessionKey) {
        self.sessions.retain(|s| s.key != *key);
        if self.retry_key.as_ref() == Some(key) {
            self.retry_key = None;
        }
    }

    fn enforce_retention(&mut self) {
        let budget = self.limits.retained_rss_mib.saturating_mul(1024 * 1024);
        // A dead/unmeasurable process is not useful reusable state. Count the
        // shell/bwrap/Rocq tree, not just the tiny launcher process.
        let mut sizes = VecDeque::new();
        self.sessions.retain_mut(|s| {
            if matches!(s.child.try_wait(), Ok(None))
                && let Some(bytes) = process_tree_rss(s.child.id())
            {
                sizes.push_back(bytes);
                true
            } else {
                false
            }
        });
        let mut total: u64 = sizes.iter().sum();
        while self.sessions.len() > self.limits.max_sessions || total > budget {
            self.sessions.pop_front();
            total = total.saturating_sub(sizes.pop_front().unwrap_or(0));
        }
    }

    /// First-try successes need only one ordinary compilation. Start a REPL
    /// only after a failed compilation in this exact dependency/module context.
    pub fn prepare(&mut self, key: &SessionKey) -> bool {
        self.synchronize(key);
        self.sessions.iter().any(|s| s.key == *key) || self.retry_key.as_ref() == Some(key)
    }

    pub fn observe_compiler(&mut self, key: &SessionKey, exit_code: Option<i32>) {
        self.synchronize(key);
        // Retaining *live* sessions pays off; retaining old cold-failure hints
        // across other compiler calls speculatively adds a REPL before success.
        self.retry_key =
            (exit_code == Some(1) && self.limits.max_sessions > 0).then(|| key.to_owned());
        if !matches!(exit_code, Some(0 | 1)) {
            self.discard(key);
        }
        self.enforce_retention();
    }

    /// Ordinary compilation needs its own Rocq process. Do not keep a duplicate
    /// full-candidate REPL, and reserve one slot instead of growing to N+1
    /// heavyweight processes per worker while the compiler is running.
    pub fn reserve_compiler_slot(&mut self, key: &SessionKey) {
        self.sessions.retain(|s| s.key != *key);
        while !self.sessions.is_empty() && self.sessions.len() >= self.limits.max_sessions {
            self.sessions.pop_front();
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
        self.synchronize(key);
        self.retry_key = None;
        let Some(sentences) = sentences(source) else {
            // Unsupported syntax must not become a spurious proof failure.
            self.discard(key);
            return Err(io::Error::other(
                "source requires ordinary compiler parsing",
            ));
        };
        let mut saved = self
            .sessions
            .iter()
            .position(|s| s.key == *key)
            .and_then(|index| self.sessions.remove(index));
        if saved
            .as_ref()
            .is_some_and(|s| s.rewind_crosses_closed_proof(&sentences))
        {
            saved = None;
        }
        // Evict before launching, so the count bound also holds during startup.
        if saved.is_none() {
            while !self.sessions.is_empty() && self.sessions.len() >= self.limits.max_sessions {
                self.sessions.pop_front();
            }
        }
        let mut session = match saved {
            Some(session) => session,
            None => Session::start(key, command, deadline)?,
        };
        let result = session.check(&sentences, deadline, show_goals);
        if result.is_ok() {
            self.sessions.push_back(session);
        }
        self.enforce_retention();
        result
    }
}

fn process_tree_rss(pid: u32) -> Option<u64> {
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    if page_size <= 0 {
        return None;
    }
    let statm = std::fs::read_to_string(format!("/proc/{pid}/statm")).ok()?;
    let mut bytes = statm
        .split_whitespace()
        .nth(1)?
        .parse::<u64>()
        .ok()?
        .checked_mul(page_size as u64)?;
    let children = std::fs::read_to_string(format!("/proc/{pid}/task/{pid}/children")).ok()?;
    for child in children.split_whitespace() {
        bytes = bytes.checked_add(process_tree_rss(child.parse().ok()?)?)?;
    }
    Some(bytes)
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

    fn enabled_pool() -> IncrementalDiagnostics {
        IncrementalDiagnostics::new(SessionLimits {
            max_sessions: 2,
            ..SessionLimits::default()
        })
    }

    #[test]
    fn default_disables_retention_and_automatic_repl_retries() {
        let mut pool = IncrementalDiagnostics::default();
        assert_eq!(pool.limits.max_sessions, 0);
        pool.observe_compiler(&key("env"), Some(1));
        assert!(!pool.prepare(&key("env")));
        assert!(pool.sessions.is_empty());
    }

    #[test]
    #[ignore = "requires a local Rocq installation"]
    fn real_default_probes_work_without_retaining_sessions() {
        let mut pool = IncrementalDiagnostics::default();
        for _ in 0..2 {
            let diagnostic = pool
                .probe(
                    &key("env"),
                    "Lemma x : True. Proof.",
                    &mut real_command(),
                    Instant::now() + Duration::from_secs(10),
                )
                .unwrap();
            assert_eq!(diagnostic.reused, 0);
            assert_eq!(diagnostic.executed, 2);
            assert!(diagnostic.goals.unwrap().contains("True"));
            assert!(pool.sessions.is_empty());
        }
    }

    #[test]
    #[ignore = "requires a local Rocq installation"]
    fn real_pool_reuses_candidates_evicts_lru_and_invalidates_dependencies() {
        let mut pool = IncrementalDiagnostics::new(SessionLimits {
            max_sessions: 2,
            retained_rss_mib: 512,
        });
        let source = "Lemma x : True. Proof.";
        let a = key("env").for_candidate("scratch/a.v");
        let b = key("env").for_candidate("scratch/b.v");
        let c = key("env").for_candidate("scratch/c.v");
        let probe = |pool: &mut IncrementalDiagnostics, key: &SessionKey| {
            pool.probe(
                key,
                source,
                &mut real_command(),
                Instant::now() + Duration::from_secs(10),
            )
            .unwrap()
        };
        assert_eq!(probe(&mut pool, &a).reused, 0);
        assert_eq!(probe(&mut pool, &b).reused, 0);
        assert_eq!(probe(&mut pool, &a).reused, 2);
        assert_eq!(pool.sessions.len(), 2);
        assert_eq!(probe(&mut pool, &c).reused, 0);
        assert_eq!(probe(&mut pool, &a).reused, 2);
        assert_eq!(probe(&mut pool, &b).reused, 0, "B was least recently used");
        assert_eq!(
            probe(&mut pool, &key("new-env").for_candidate("scratch/b.v")).reused,
            0
        );
        assert_eq!(
            pool.sessions.len(),
            1,
            "dependency change invalidates every old snapshot"
        );
        pool.limits.retained_rss_mib = 0;
        pool.enforce_retention();
        assert!(pool.sessions.is_empty());
        assert_eq!(probe(&mut pool, &a).reused, 0);
        assert!(
            pool.sessions.is_empty(),
            "over-budget state must not be retained"
        );
        pool.limits = SessionLimits {
            max_sessions: 0,
            retained_rss_mib: 512,
        };
        assert_eq!(probe(&mut pool, &a).reused, 0);
        assert!(
            pool.sessions.is_empty(),
            "zero capacity still permits transient probes"
        );
        pool.limits = enabled_pool().limits;
        probe(&mut pool, &a);
        probe(&mut pool, &b);
        pool.reserve_compiler_slot(&a);
        assert_eq!(pool.sessions.len(), 1);
        assert_eq!(
            pool.sessions[0].key, b,
            "compiler releases its duplicate session"
        );
        probe(&mut pool, &a);
        pool.reserve_compiler_slot(&c);
        assert_eq!(pool.sessions.len(), 1, "cold compiler also reserves a slot");
        assert_eq!(
            pool.sessions[0].key, a,
            "cold compiler evicts the LRU entry"
        );
    }

    #[test]
    #[ignore = "requires a local Rocq installation"]
    fn real_pool_timeout_discards_only_the_failed_candidate() {
        let mut pool = enabled_pool();
        let a = key("env").for_candidate("scratch/a.v");
        let b = key("env").for_candidate("scratch/b.v");
        let prefix = "Lemma x : True. Proof.";
        for key in [&a, &b] {
            pool.probe(
                key,
                prefix,
                &mut real_command(),
                Instant::now() + Duration::from_secs(10),
            )
            .unwrap();
        }
        assert!(
            pool.probe(
                &a,
                &format!("{prefix} repeat (pose proof I)."),
                &mut real_command(),
                Instant::now() + Duration::from_millis(100)
            )
            .is_err()
        );
        let good = pool
            .probe(
                &b,
                prefix,
                &mut real_command(),
                Instant::now() + Duration::from_secs(10),
            )
            .unwrap();
        assert_eq!(good.reused, 2);
        assert!(good.goals.unwrap().contains("True"));
        assert_eq!(pool.sessions.len(), 1);
    }

    #[test]
    fn pool_does_not_speculatively_warm_old_cold_failures() {
        let mut pool = enabled_pool();
        let a = key("env").for_candidate("scratch/a.v");
        let b = key("env").for_candidate("scratch/b.v");
        pool.observe_compiler(&a, Some(1));
        pool.observe_compiler(&b, Some(0));
        assert!(!pool.prepare(&a));
        assert!(!pool.prepare(&b));
        assert!(!pool.prepare(&key("changed")));
        assert!(!pool.prepare(&a));
        pool.limits.max_sessions = 0;
        pool.clear();
        assert_eq!(
            pool.limits.max_sessions, 0,
            "failure cleanup preserves configured limits"
        );
    }

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
        let mut session = enabled_pool();
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
        assert!(
            !session.prepare(&original.clone()),
            "manifest changes invalidate retry eligibility too"
        );
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
        let mut session = enabled_pool();
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
        let mut session = enabled_pool();
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
        let mut session = enabled_pool();
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
        assert!(session.sessions.is_empty());
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
        let mut session = enabled_pool();
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
