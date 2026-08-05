#!/usr/bin/env python3
"""Focused tests for repository-local machine configuration."""

from __future__ import annotations

import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from logos_env import LogosEnvironmentError, configured_path, load_logos_env


class LogosEnvironmentTests(unittest.TestCase):
    def test_explicit_environment_wins_over_dotenv(self) -> None:
        with tempfile.TemporaryDirectory(prefix="logos-env-test-") as temporary:
            root = Path(temporary)
            (root / ".env").write_text(
                "LOGOS_TEST_PATH=from-dotenv\nQUOTED_VALUE='two words'\n",
                encoding="utf-8",
            )
            with mock.patch.dict(
                os.environ, {"LOGOS_TEST_PATH": "from-process"}, clear=False
            ):
                os.environ.pop("QUOTED_VALUE", None)
                load_logos_env(root)
                self.assertEqual(os.environ["LOGOS_TEST_PATH"], "from-process")
                self.assertEqual(os.environ["QUOTED_VALUE"], "two words")
                os.environ.pop("QUOTED_VALUE", None)

    def test_relative_configured_path_is_root_relative(self) -> None:
        with tempfile.TemporaryDirectory(prefix="logos-env-path-test-") as temporary:
            root = Path(temporary)
            with mock.patch.dict(
                os.environ, {"LOGOS_TEST_PATH": "../external/tool"}, clear=False
            ):
                self.assertEqual(
                    configured_path(root, "LOGOS_TEST_PATH"),
                    (root / "../external/tool").resolve(),
                )

    def test_malformed_dotenv_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory(prefix="logos-env-invalid-test-") as temporary:
            root = Path(temporary)
            (root / ".env").write_text("not-an-assignment\n", encoding="utf-8")
            with self.assertRaises(LogosEnvironmentError):
                load_logos_env(root)


if __name__ == "__main__":
    unittest.main()
