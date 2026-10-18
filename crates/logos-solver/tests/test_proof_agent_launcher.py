"""Run the unmodified launcher in a local container; no model or credentials.

Set LOGOS_TEST_DOCKER_IMAGE to an already built image to enable these tests.
Rocq compilation/kernel acceptance is exercised separately by the sandbox suite.
"""

import json
import os
from pathlib import Path
import shlex
import shutil
import socket
import subprocess
import tempfile
import unittest


SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
IMAGE = os.environ.get("LOGOS_TEST_DOCKER_IMAGE")
PROBLEM = "Lemma initial : True. Proof. exact I. Qed.\n"
REVISED = "Lemma revised : True. Proof. exact I. Qed.\n"


@unittest.skipUnless(IMAGE, "set LOGOS_TEST_DOCKER_IMAGE for real launcher integration")
class ProofAgentLauncherTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="logos-launcher-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.workspace = self.root / "workspace"
        self.stage = self.root / "round/stage"
        self.home = self.root / "session"
        self.credentials = self.root / "fixture-credentials"
        self.authority = self.root / "authority"
        self.launcher = self.root / "launcher"
        for path in (self.workspace, self.stage / "scratch", self.home,
                     self.credentials, self.launcher):
            path.mkdir(parents=True)
        for name in ("run-proof-agent-docker.sh", "lemma-ablation.py", "search-rocq-declarations.py"):
            shutil.copyfile(SCRIPTS / name, self.launcher / name)
        for name in (
            "Problem.v", "Schema.v", "Queries.v", "WitnessData.v", "Witness.v", "Goal.v",
            "source.sql", "target.sql", "query-shape.json", "ordered-signatures.json",
            "observation-certificates.json", "semantic-primer.md", "search-rocq-declarations.py",
            "context-manifest.json", "proof-agent-prompt.md", "run-rocq-check.sh",
            "lemma-availability.json",
        ):
            (self.workspace / name).write_text(PROBLEM)
        for name in ("WitnessModules", "ProofModules"):
            (self.workspace / name).mkdir()
        (self.workspace / "WitnessModules/ORDER").write_text("")
        (self.workspace / "ProofModules/Core.v").write_text(PROBLEM)
        for name in ("vendor/FormalSQL/src/Library.v", "theories/FormalSQL/Library.v"):
            source = self.authority / name
            source.parent.mkdir(parents=True)
            source.write_text("Lemma bag_fact : True. Proof. exact I. Qed.\n")
            # Launcher tests bind bytes; they do not pretend these are Rocq certificates.
            source.with_suffix(".vo").write_bytes(b"opaque fixture object")
            source.chmod(0o444)
            source.with_suffix(".vo").chmod(0o444)
        (self.credentials / "config.toml").write_text('# frozen fixture config\n')
        (self.credentials / "auth.json").write_text('{"fixture": true}\n')
        (self.home / "auth.json").mkdir()  # Prior agent state must not override host credentials.
        (self.stage / "scratch/old").write_text("prior WIP")
        broker_dir = self.root / "logos-pds-1-fixture"
        broker_dir.mkdir(mode=0o700)
        self.broker = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.addCleanup(self.broker.close)
        self.broker.bind(str(broker_dir / "socket"))
        self.environment = {
            "PATH": "/usr/bin:/bin", "HOME": str(self.root),
            "LOGOS_REPO_ROOT": str(self.authority), "LOGOS_SOLVER_IMAGE": IMAGE,
            "LOGOS_PROOF_WORKDIR": str(self.workspace),
            "LOGOS_PROOF_AGENT_STAGE": str(self.stage),
            "LOGOS_PROOF_AGENT_CODEX_HOME": str(self.home),
            "LOGOS_SOLVER_CODEX_HOME": str(self.credentials),
            "LOGOS_SOLVER_CODEX_CONFIG": str(self.credentials / "config.toml"),
            "LOGOS_PROOF_DIAGNOSTIC_SOCKET": str(broker_dir / "socket"),
            "LOGOS_PROOF_DIAGNOSTIC_NONCE": "a" * 64,
            "LOGOS_PROOF_AGENT_TIMEOUT": "15",
            "LOGOS_PROOF_AGENT_MEMORY_LIMIT": "256m",
            "LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES": str(8 * 1024 * 1024),
        }

    def run_agent(self, code):
        return subprocess.run(
            ["bash", str(self.launcher / "run-proof-agent-docker.sh")],
            env={**self.environment, "LOGOS_PROOF_AGENT_COMMAND": "python3 -c " + shlex.quote(code)},
            capture_output=True, text=True, timeout=60,
        )

    def test_read_only_inputs_and_publication_are_separate_from_certification(self):
        result = self.run_agent(f"""
import json, os
from pathlib import Path
p = Path('/workspace/problem')
read_only = []
for name in ('/workspace/logos/theories/FormalSQL/Library.v', str(p / 'Schema.v'), '/etc/launcher-probe', '/handoff-export'):
    try:
        Path(name).write_text('tamper')
        read_only.append(False)
    except PermissionError:
        read_only.append(True)
    except OSError as error:
        import errno
        if error.errno != errno.EROFS:
            raise
        read_only.append(True)
assert os.getuid() != 0
assert sum(os.statvfs(path).f_blocks * os.statvfs(path).f_frsize for path in ('/workspace', '/dev/shm')) <= 8 * 1024 * 1024
memory = Path('/sys/fs/cgroup/memory.max')
if not memory.exists():
    memory = Path('/sys/fs/cgroup/memory/memory.limit_in_bytes')
assert int(memory.read_text()) == 256 * 1024 * 1024
assert not (p / 'run-trusted-rocq-check.sh').exists()
assert json.loads(Path('/workspace/codex-home/auth.json').read_text()) == {{'fixture': True}}
(p / 'ProofModules/Core.v').write_text('forged module')
(p / 'ProofModules/Unchecked.v').write_text('unchecked module')
(p / 'Problem.v').write_text({REVISED!r})
(p / 'scratch/old').unlink()
(p / 'scratch/observed.json').write_text(json.dumps(read_only))
sessions = Path('/workspace/codex-home/sessions')
sessions.mkdir(exist_ok=True)
(sessions / 'round.jsonl').write_text('session marker')
print('agent output marker')
raise SystemExit(7)
""")
        self.assertEqual(result.returncode, 7, result.stderr)
        self.assertEqual((self.workspace / "Problem.v").read_text(), REVISED)
        self.assertEqual((self.workspace / "ProofModules/Core.v").read_text(), PROBLEM)
        self.assertFalse((self.workspace / "ProofModules/Unchecked.v").exists())
        self.assertEqual(json.loads((self.stage / "scratch/observed.json").read_text()), [True] * 4)
        self.assertFalse((self.stage / "scratch/old").exists())
        self.assertEqual((self.home / "sessions/round.jsonl").read_text(), "session marker")
        self.assertIn("agent output marker", (self.stage / "agent-stdout").read_text())
        self.assertNotIn("agent output marker", result.stdout)
        self.assertFalse(list(self.workspace.rglob("*.vo")))
        self.assertTrue((self.workspace / "authority-closure.txt").is_file())
        self.assertEqual(list(self.stage.parent.iterdir()), [self.stage])

    def test_invalid_export_never_publishes_candidate_or_session_output(self):
        result = self.run_agent(f"""
from pathlib import Path
p = Path('/workspace/problem')
(p / 'Problem.v').write_text({REVISED!r})
(p / 'scratch/escape').symlink_to('/etc/passwd')
print('unpublishable session')
""")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual((self.workspace / "Problem.v").read_text(), PROBLEM)
        self.assertFalse((self.stage / "agent-stdout").exists())
        self.assertTrue((self.stage / "scratch/old").is_file())
        self.assertFalse((self.stage / "scratch/escape").exists())
        self.assertTrue((self.workspace / "authority-closure.txt").is_file())

    def test_ablation_mount_contains_no_objects_or_disabled_facts(self):
        subprocess.run([
            "python3", str(self.launcher / "lemma-ablation.py"), "prepare",
            "--authority", str(self.authority), "--output", str(self.launcher),
            "--baseline", str(self.workspace / "Problem.v"), "--bag", "off", "--other", "off",
        ], check=True, capture_output=True, text=True, timeout=15)
        result = self.run_agent("""
from pathlib import Path
root = Path('/workspace/logos')
assert not list(root.rglob('*.vo'))
sources = list(root.rglob('*.v'))
assert sources
assert all('bag_fact' not in source.read_text() for source in sources)
assert 'exact I' not in Path('/workspace/problem/Schema.v').read_text()
print('filtered authority observed')
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("filtered authority observed", (self.stage / "agent-stdout").read_text())


if __name__ == "__main__":
    unittest.main()
