"""Pure stdlib controls for the NEW portable helper; no Lean or source execution."""
from pathlib import Path
import copy
import json
import time
import unittest
import capture_to_lean as tool

ROOT=Path(__file__).resolve().parent

class CaptureControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.base=json.loads((ROOT/'examples/triangle_repeated_owners.json').read_bytes())
        cls.artifacts=ROOT/'test-artifacts'/str(time.time_ns())
        cls.artifacts.mkdir(parents=True,exist_ok=False)

    def test_all_public_examples(self):
        names=list((ROOT/'examples').glob('*.json'));self.assertEqual(len(names),3)
        identifiers=[]
        for path in names:
            with self.subTest(example=path.name):
                checked=tool.load_capture(path)
                source=tool.emit_lean(checked)
                self.assertIn('import ConfigurationOwnerCertificate\n',source)
                self.assertIn(':= by decide',source)
                self.assertNotIn('native_decide',source)
                self.assertNotIn('sorry',source)
                self.assertNotIn('admit',source)
                self.assertNotIn('C:\\',source)
                self.assertNotIn('/Users/',source)
                for value in checked[0]['source_binding'].values():self.assertNotIn(value,source)
                identifiers.append(tool.module_identifier(checked))
        self.assertEqual(len(set(identifiers)),3)

    def test_type_bounds_and_schema_refusals(self):
        changes=[('schema_version',True),('schema_version',2),('n',True),('n',0),('n',9),
                 ('target_degrees',[True,2,2]),('target_degrees',[3,2,2]),
                 ('owners',[0]*18),('owners',[0,1,0,2,1]),('owners',[True,1,0,2,1,2]),
                 ('owners',['0; axiom injected : False',1,0,2,1,2]),
                 ('fixed_edges',[[1,0]]),('fixed_edges',[[0,0]]),('fixed_edges',[[0,1],[0,1]])]
        for key,value in changes:
            with self.subTest(key=key,value=value):
                data=copy.deepcopy(self.base);data[key]=value
                with self.assertRaises(tool.InvalidCapture):tool.validate_capture(data)
        data=copy.deepcopy(self.base);data['output_path']='unexpected'
        with self.assertRaises(tool.InvalidCapture):tool.validate_capture(data)

    def test_pairing_and_adjacency_refusals(self):
        changes=[('owners',[0,0,1,2,1,2]),('owners',[0,1,1,0,2,2]),
                 ('owners',[0,1,0,2,2,2]),('returned_adjacency',[[1],[0,2],[1]]),
                 ('returned_adjacency',[[1,2],[2],[0,1]]),
                 ('returned_adjacency',[[1,1],[0,2],[0,1]]),
                 ('returned_adjacency',[[0,1],[0,2],[0,1]])]
        for key,value in changes:
            with self.subTest(key=key,value=value):
                data=copy.deepcopy(self.base);data[key]=value
                with self.assertRaises(tool.InvalidCapture):tool.validate_capture(data)
        retained=json.loads((ROOT/'examples/retained_edge.json').read_bytes())
        retained['owners']=[0,1,2,3]
        with self.assertRaisesRegex(tool.InvalidCapture,'retained-edge collision'):tool.validate_capture(retained)

    def test_source_metadata_is_not_code_or_authentication(self):
        for value in ['g'*64,'a'*63,'ab\nimport Fake',42]:
            data=copy.deepcopy(self.base);data['source_binding']['reference_sha256']=value
            with self.assertRaises(tool.InvalidCapture):tool.validate_capture(data)
        data=copy.deepcopy(self.base);data['source_binding']['reference_sha256']='0'*64
        # Syntax validation deliberately does not authenticate the claimed source.
        self.assertEqual(tool.validate_capture(data)[0]['source_binding']['reference_sha256'],'0'*64)

    def test_duplicate_keys_nonfinite_invalid_utf8_and_byte_bound(self):
        payloads=[b'{"schema_version":1,"schema_version":1}',b'{"n":NaN}',b'\xff',b' '*65537]
        for i,raw in enumerate(payloads):
            path=self.artifacts/('invalid-'+str(i)+'.json');path.write_bytes(raw)
            with self.subTest(control=i),self.assertRaises(tool.InvalidCapture):tool.load_capture(path)

    def test_output_preserves_existing_directory(self):
        path=self.artifacts/'existing';path.mkdir();marker=path/'marker.txt';marker.write_bytes(b'preserve')
        with self.assertRaisesRegex(tool.InvalidCapture,'must not exist'):
            tool.write_new_directory(path,tool.validate_capture(self.base))
        self.assertEqual(marker.read_bytes(),b'preserve')
        self.assertEqual([p.name for p in path.iterdir()],['marker.txt'])

    def test_deterministic_emission_and_distinct_modules(self):
        for file in sorted((ROOT/'examples').glob('*.json')):
            checked=tool.load_capture(file);a=tool.emit_lean(checked);b=tool.emit_lean(checked)
            self.assertEqual(a,b)
            path=self.artifacts/file.stem
            result=tool.write_new_directory(path,checked)
            self.assertEqual((path/result['lean_source_file']).read_bytes(),a.encode('utf-8'))
            self.assertEqual(tool.load_capture(path/'capture.normalized.json'),checked)
            self.assertRegex(result['lean_source_file'],r'^OwnerCapture_[0-9a-f]{64}\.lean$')

    def test_literal_occurrence_labels_and_zero_residual_case(self):
        checked=tool.validate_capture(self.base)
        self.assertEqual(checked[1],[2,2,2])
        self.assertEqual(checked[2],[[0,0],[1,0],[0,1],[2,0],[1,1],[2,1]])
        self.assertEqual(checked[3],[[0,1],[0,2],[1,2]])
        empty=tool.load_capture(ROOT/'examples/fixed_only_zero_residual.json')
        self.assertEqual(empty[1],[0,0,0]);self.assertEqual(empty[2],[])
        self.assertIn('fun z => Fin.elim0 z.1',tool.emit_lean(empty))

if __name__=='__main__':
    unittest.main(verbosity=2)
