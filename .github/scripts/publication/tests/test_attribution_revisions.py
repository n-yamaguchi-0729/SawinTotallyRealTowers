"""Reviewed upstream notice pins remain closed to unknown revisions."""
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import public_extract_provenance as provenance

class ReviewedRevisionTests(unittest.TestCase):
    def test_each_reviewed_revision_and_mixed_headers(self):
        path = 'Nyll/AbelianVarieties/Tate/Representation.lean'
        revisions = sorted(provenance.ANTHROPIC_REVIEWED_REVISIONS)
        for selected in ([revision] for revision in revisions):
            self.check_header(path, selected)
        self.check_header(path, revisions)

    def check_header(self, path, revisions):
        header = '/-\nCopyright 2026 Anthropic, PBC.\n' + '\n'.join(
            provenance.ANTHROPIC + 'blob/' + revision + '/Definitions/Example.lean'
            for revision in revisions) + '\n-/\n'
        files = {path: header.encode(), provenance.PI1 + 'UPSTREAM.json':
                 json.dumps({'local_source_snapshot': {'files': []}}).encode()}
        _, _, records, _ = provenance.selected_records(files, {path})
        self.assertEqual(len(records['AbelianVarieties'][0]['upstream_sources']), len(revisions))
        self.assertEqual(files[path], header.encode())
        files[path] = header.replace(revisions[0], 'f' * 40).encode()
        with self.assertRaisesRegex(ValueError, 'new upstream-notice audit'):
            provenance.selected_records(files, {path})
