import io
import json
import os
import unittest
from argparse import Namespace
from contextlib import redirect_stdout
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from . import __main__ as cli


class CompileOutputsTests(unittest.TestCase):
    def setUp(self):
        scratch = TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.dir = Path(scratch.name)
        self.statement = self.dir / "statement.json"
        self.statement.write_text("{}")
        self.rows = self.dir / "rows.jsonl"
        self.manifest = self.dir / "manifest.json"

    def compile(self, emit=None):
        def emit_rows(statement, proof, pairing, sink, arithmetic):
            sink.write(b"row\n")
            return None, {"constraints": 1}

        args = Namespace(
            statement=self.statement, rows=self.rows, manifest=self.manifest,
            pairing="ate", arithmetic=None,
        )
        with patch.object(cli, "emit", side_effect=emit or emit_rows), redirect_stdout(io.StringIO()):
            cli.compile_command(args)

    def test_encoder_failure_leaves_clean_paths_and_can_retry(self):
        def fail(statement, proof, pairing, sink, arithmetic):
            sink.write(b"partial")
            raise ValueError("invalid statement")

        for suffix in (".jsonl", ".jsonl.gz"):
            with self.subTest(suffix=suffix):
                self.rows = self.dir / ("rows" + suffix)
                with self.assertRaisesRegex(ValueError, "invalid statement"):
                    self.compile(fail)
                self.assertEqual(list(self.dir.iterdir()), [self.statement])
                self.compile()
                with cli.open_rows(self.rows, "rb") as stream:
                    self.assertEqual(stream.read(), b"row\n")
                self.assertEqual(json.loads(self.manifest.read_text()), {"constraints": 1})
                self.rows.unlink()
                self.manifest.unlink()

    def test_existing_manifest_is_preserved_before_encoding(self):
        self.manifest.write_text("existing manifest")
        with self.assertRaises(FileExistsError):
            self.compile(lambda *args: self.fail("encoder started"))
        self.assertFalse(self.rows.exists())
        self.assertEqual(self.manifest.read_text(), "existing manifest")

    def test_competing_writer_wins_manifest_without_orphaning_rows(self):
        link = os.link

        def race(source, destination):
            if destination == self.manifest:
                # Publish another writer's manifest between preflight and link().
                destination.write_text("other manifest")
            return link(source, destination)

        with patch.object(cli.os, "link", side_effect=race), self.assertRaises(FileExistsError):
            self.compile()
        self.assertFalse(self.rows.exists())
        self.assertEqual(self.manifest.read_text(), "other manifest")
        self.assertEqual(set(self.dir.iterdir()), {self.statement, self.manifest})

    def test_rollback_preserves_rows_replaced_by_another_writer(self):
        link = os.link

        def race(source, destination):
            if destination == self.manifest:
                self.rows.unlink()
                self.rows.write_text("other rows")
                raise OSError("cannot publish manifest")
            return link(source, destination)

        with patch.object(cli.os, "link", side_effect=race), self.assertRaises(OSError):
            self.compile()
        self.assertEqual(self.rows.read_text(), "other rows")
        self.assertFalse(self.manifest.exists())
