"""Saved evidence and CLI controls only; no random draws/native/compiler work."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from curveball_evaluation import study
from curveball_evaluation.cli import main


class EvidenceTests(unittest.TestCase):
    def test_exact_accepted_artifacts(self):
        e=study.load_pwr002()
        self.assertEqual(e['review']['review'],'050')
        self.assertEqual(e['analysis']['status'],'censored_formal_claims_withheld')
        self.assertEqual(e['analysis']['administrative_recovery']['interrupted_candidate_charges'],61)
        self.assertEqual(e['review']['independent_audit_counts']['scheduled_jobs'],9018)
        self.assertEqual(e['review']['independent_audit_counts']['completed_jobs'],9017)
        self.assertEqual(sum(g['N']-g['completed'] for g in e['analysis']['groups']),1)
        self.assertEqual(e['analysis']['missing_jobs'],0)

    def test_original_censor_sensitivity_and_paired_negative_result(self):
        e=study.load_pwr002();a=e['analysis']
        g=next(g for g in a['groups'] if (g['case'],g['condition'],g['method'])==('bcspwr01','null','pairing'))
        self.assertEqual(g['missing_outcome_sensitivity_fraction'],['89/3000','3/100'])
        self.assertEqual((a['paired']['reference_only_detections'],a['paired']['global20_only_detections']),(31,38))
        self.assertFalse(a['reference_advantage_gate_pass']);self.assertFalse(a['matched605_cost_label_valid'])

    def test_practical_summary_no_held_authorization(self):
        e=study.load_pwr002()
        for key in ('complete_reviewed_empirical_scope','original_confirmatory_status_restored',
                    'scientific_runtime_authorization_promoted','tv_assurance_authorized','ideal_randomness_claim','graph_refinement_binary_claim'):
            self.assertIs(e[key],False,key)
        self.assertTrue(all(g['formal_gate_eligible'] is False for g in e['analysis']['groups']))

    def test_fresh_objects_do_not_mutate_bundled_evidence(self):
        a=study.load_pwr002();a['analysis']['groups'].clear();a['provenance'].clear()
        b=study.load_pwr002();self.assertEqual(len(b['analysis']['groups']),38);self.assertTrue(b['provenance'])

    def test_cli_json_and_markdown_no_sampling(self):
        out=io.StringIO()
        with contextlib.redirect_stdout(out):self.assertEqual(main(['--format','json']),0)
        self.assertFalse(json.loads(out.getvalue())['complete_reviewed_empirical_scope'])
        out=io.StringIO()
        with contextlib.redirect_stdout(out):self.assertEqual(main([]),0)
        self.assertIn('95.500%',out.getvalue());self.assertIn('unknown partial',out.getvalue())
        self.assertIn('not this wheel',out.getvalue())
        self.assertNotIn('networkit',sys.modules);self.assertNotIn('degree_null.kernel',sys.modules)

    def test_malformed_cli_rejected(self):
        with contextlib.redirect_stderr(io.StringIO()),self.assertRaises(SystemExit) as caught:main(['--format','sample'])
        self.assertEqual(caught.exception.code,2)

    def test_markdown_platform_newline_translation_once(self):
        accepted=study.load_pwr002()
        preserved=accepted['accepted_report_markdown']
        out=io.StringIO(newline='\r\n')
        with contextlib.redirect_stdout(out):self.assertEqual(main(['--format','markdown']),0)
        self.assertNotIn('\r\r\n',out.getvalue())
        self.assertEqual(out.getvalue().replace('\r\n','\n'),study.render_pwr002(accepted).replace('\r\n','\n'))
        self.assertEqual(study.load_pwr002()['accepted_report_markdown'],preserved)

    def test_artifact_tampering_blocked(self):
        original=study._read
        def corrupt(name):return b'{}' if name=='analysis.json' else original(name)
        with patch.object(study,'_read',side_effect=corrupt),self.assertRaises(KeyError):study.load_pwr002()
        class Fake:
            def joinpath(self,*args):return self
            def read_bytes(self):return b'{}'
        with patch.object(study.resources,'files',return_value=Fake()),self.assertRaises(ValueError):study.load_pwr002()

    def test_public_artifacts_contain_no_private_paths_or_ids(self):
        raw=json.dumps(study.load_pwr002()).lower()
        for token in ('c:\\users\\','c:/users/','libfile_','file_000000','source_thread_id','access_token'):
            self.assertNotIn(token,raw)


if __name__=='__main__':unittest.main()
