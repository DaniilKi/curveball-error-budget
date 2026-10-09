"""Synthetic evidence only: no sampler, native backend, random draw or compiler."""
from dataclasses import FrozenInstanceError
import copy
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from curveball_evaluation import FrozenStudy, StudyHistory, build_report, render_markdown
from curveball_evaluation.report import digest


def blob(value):
    return json.dumps(value,sort_keys=True).encode()


class EvaluationTests(unittest.TestCase):
    def setUp(self):
        self.obs=[{'id':'o0','seed':1,'case':'fixture','condition':'null'},
                  {'id':'o1','seed':2,'case':'fixture','condition':'moderate'}]
        self.jobs=[{'id':'j0','observation_id':'o0','case':'fixture','condition':'null','method':'pairing','seeds':[10,11]},
                   {'id':'j1','observation_id':'o1','case':'fixture','condition':'moderate','method':'pairing','seeds':[12,13]}]
        self.schedule=self.freeze()
        self.resource={'exit_code':0,'stop_reason':None,'child_terminal':True,'unit_ledger_known':True,
                       'cleanup_notes':[],'unknown_ledger_conservative_all_caps':False,
                       'all_phase_reserved':{'ordinary_attempts':100,'global_rounds':20,'pairing_candidates':8}}
        self.raw=blob(self.resource);self.pin=digest(self.raw)
        self.history=StudyHistory(self.schedule).transition('planned',self.pin).transition('running',self.pin).transition('completed',self.pin)
        self.analysis={'status':'fully_audited','scientific_runtime_authorization_promoted':False,
                       'missing_jobs':0,'missing_observations':0,'jobs_missing_corresponding_observation':0,
                       'truncated':False,'errors':[],
                       'paired':{'N':1,'reference_only_detections':1,'global20_only_detections':0,
                                 'reference_minus_global20_power_gain_lower':-0.9,'gain_gate':False,
                                 'precision_claim':'confirmatory_conditional_IID'},'groups':[
            {'case':'fixture','condition':'null','method':'pairing','N':1,'completed':1,'detected':0,'rate':0,
             'primary':True,'formal_gate_eligible':True,'precision_claim':'confirmatory_conditional_IID',
             'one_sided_005_bounds':[0,.995],'completion_bounds':[.005,1]},
            {'case':'fixture','condition':'moderate','method':'pairing','N':1,'completed':1,'detected':1,'rate':1,
             'primary':True,'formal_gate_eligible':True,'precision_claim':'confirmatory_conditional_IID',
             'one_sided_005_bounds':[.005,1],'completion_bounds':[.005,1]}]}
        self.prior=[{'id':'original-classroom-negative','sha256':'a'*64,'status':'failed_power_gate'},
                    {'id':'PWR-002-original','sha256':'b'*64,'status':'interrupted_guard_failure'}]

    def freeze(self,obs=None,jobs=None):
        a=blob(self.obs if obs is None else obs);b=blob(self.jobs if jobs is None else jobs)
        return FrozenStudy.from_json('synthetic-PWR-adapter','f'*64,a,b,
            observations_sha256=digest(a),jobs_sha256=digest(b),outputs_per_job=2)

    def report(self,analysis=None,history=None,resources=None,**kw):
        raw=blob(self.analysis if analysis is None else analysis)
        return build_report(self.history if history is None else history,raw,analysis_sha256=digest(raw),
            analyzer_sha256='c'*64,resources=[(self.raw,self.pin)] if resources is None else resources,
            prior_evidence=self.prior,**kw)

    def test_completed_measurements_remain_unaccepted_without_review(self):
        r=self.report();self.assertEqual(r['state'],'completed');self.assertFalse(r['complete_reviewed_empirical_scope'])
        self.assertEqual(r['scheduled_jobs'],2);self.assertEqual(r['groups'][0]['scheduled'],1)
        self.assertEqual(r['groups'][1]['measurement'],'power_under_specified_alternative')
        self.assertFalse(r['scientific_runtime_authorization_promoted']);self.assertFalse(r['tv_assurance_authorized'])

    def test_accepted_exact_binding_still_does_not_promote_runtime(self):
        provisional=self.report()
        review={'bindings':provisional['bindings'],'disposition':'accepted_empirical_scope','review_sha256':'d'*64}
        r=self.report(review=review);self.assertTrue(r['complete_reviewed_empirical_scope'])
        self.assertFalse(r['graph_refinement_binary_claim']);self.assertFalse(r['ideal_randomness_claim'])
        self.assertFalse(r['scientific_runtime_authorization_promoted'])

    def test_review_stale_after_history_or_analysis_change(self):
        review={'bindings':self.report()['bindings'],'disposition':'accepted_empirical_scope','review_sha256':'d'*64}
        a=copy.deepcopy(self.analysis);a['scope']='different'
        with self.assertRaises(ValueError):self.report(analysis=a,review=review)
        h=StudyHistory(self.schedule).transition('planned',self.pin).transition('running',self.pin).transition('censored',self.pin)
        with self.assertRaises(ValueError):self.report(history=h,review=review)

    def test_seed_and_snapshot_immutability(self):
        self.jobs[0]['seeds'][0]=999
        self.assertEqual(self.schedule.jobs[0].seeds,(10,11))
        with self.assertRaises(FrozenInstanceError):self.schedule.protocol_id='altered'
        with self.assertRaises(TypeError):self.schedule.jobs[0].seeds[0]=999

    def test_seed_replacement_requires_different_frozen_schedule(self):
        jobs=copy.deepcopy(self.jobs);jobs[0]['seeds'][0]=999
        other=self.freeze(jobs=jobs)
        self.assertNotEqual(other.jobs_sha256,self.schedule.jobs_sha256)

    def test_canonical_decimal_string_seed_compatibility(self):
        obs=copy.deepcopy(self.obs);jobs=copy.deepcopy(self.jobs)
        for row in obs:row['seed']=str(row['seed'])
        for row in jobs:row['seeds']=list(map(str,row['seeds']))
        frozen=self.freeze(obs=obs,jobs=jobs)
        self.assertEqual(frozen.observation_seeds,self.schedule.observation_seeds)
        self.assertEqual(frozen.jobs,self.schedule.jobs)
        self.assertNotEqual(frozen.jobs_sha256,self.schedule.jobs_sha256)
        for bad in ['01','-1','+1',' 10','1.0','1e2','\u0661','18446744073709551616']:
            broken=copy.deepcopy(jobs);broken[0]['seeds'][0]=bad
            with self.subTest(bad=bad),self.assertRaises(ValueError):self.freeze(obs=obs,jobs=broken)

    def test_mixed_encoding_duplicate_seeds_refused(self):
        jobs=copy.deepcopy(self.jobs);jobs[0]['seeds'][0]='12'
        with self.assertRaises(ValueError):self.freeze(jobs=jobs)

    def test_duplicate_boolean_and_out_of_range_seeds_refused(self):
        for value in [1,12,True,-1,2**64]:
            jobs=copy.deepcopy(self.jobs);jobs[0]['seeds'][0]=value
            with self.subTest(value=value),self.assertRaises(ValueError):self.freeze(jobs=jobs)

    def test_group_observation_and_batch_denominators_refused(self):
        for key,value in [('observation_id','absent'),('condition','weak'),('seeds',[10])]:
            jobs=copy.deepcopy(self.jobs);jobs[0][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):self.freeze(jobs=jobs)

    def test_digest_and_duplicate_json_keys_refused(self):
        a=blob(self.obs);b=blob(self.jobs)
        with self.assertRaises(ValueError):FrozenStudy.from_json('x','f'*64,a,b,observations_sha256='0'*64,jobs_sha256=digest(b),outputs_per_job=2)
        raw=b'{"status":"fully_audited","status":"other","groups":[]}'
        with self.assertRaises(ValueError):build_report(self.history,raw,analysis_sha256=digest(raw),analyzer_sha256='c'*64,resources=[(self.raw,self.pin)],prior_evidence=self.prior)

    def test_interrupted_and_censored_denominators_retained(self):
        a=copy.deepcopy(self.analysis);a['status']='censored_formal_claims_withheld'
        a['groups'][1].update(completed=0,detected=0,rate=0,one_sided_005_bounds=[0,.995],completion_bounds=[0,.995])
        for state in ('censored','interrupted','failed'):
            h=StudyHistory(self.schedule).transition('planned',self.pin).transition('running',self.pin).transition(state,self.pin)
            r=self.report(analysis=a,history=h)
            self.assertEqual(r['state'],state);self.assertEqual(r['groups'][1]['scheduled'],1)
            self.assertEqual(r['groups'][1]['not_completed'],1);self.assertFalse(r['complete_reviewed_empirical_scope'])

    def test_resume_policy_required_and_original_seeds_retained(self):
        h=StudyHistory(self.schedule).transition('planned',self.pin).transition('running',self.pin).transition('interrupted',self.pin)
        with self.assertRaises(ValueError):h.transition('resumed',self.pin)
        approved=StudyHistory(self.schedule,h.events,'e'*64).transition('resumed',self.pin)
        self.assertEqual(approved.schedule.observation_seeds,h.schedule.observation_seeds)
        self.assertEqual(approved.schedule.jobs,h.schedule.jobs)
        r=self.report(history=approved);self.assertEqual(r['state'],'resumed');self.assertFalse(r['complete_reviewed_empirical_scope'])
        done=approved.transition('running',self.pin).transition('completed',self.pin)
        self.assertEqual([s for s,_ in done.events],['planned','running','interrupted','resumed','running','completed'])

    def test_completed_and_failed_runs_are_terminal(self):
        with self.assertRaises(ValueError):self.history.transition('resumed',self.pin)
        h=StudyHistory(self.schedule).transition('planned',self.pin).transition('running',self.pin).transition('failed',self.pin)
        with self.assertRaises(ValueError):h.transition('resumed',self.pin)
        with self.assertRaises(ValueError):StudyHistory(self.schedule).transition('completed',self.pin)

    def test_directly_forged_history_is_revalidated(self):
        for events in [(('completed',self.pin),),(('planned',self.pin),('resumed',self.pin))]:
            h=StudyHistory(self.schedule,events,'e'*64)
            with self.subTest(events=events),self.assertRaises(ValueError):self.report(history=h)

    def test_direct_mutable_schedule_refused(self):
        with self.assertRaises(ValueError):FrozenStudy('x','f'*64,'e'*64,'d'*64,list(self.schedule.observation_seeds),self.schedule.jobs,2)

    def test_no_selected_denominator_or_detection_from_failed_job(self):
        for change in [{'N':2},{'completed':0},{'detected':2},{'rate':.2}]:
            a=copy.deepcopy(self.analysis);a['groups'][1].update(change)
            with self.subTest(change=change),self.assertRaises(ValueError):self.report(analysis=a)
        a=copy.deepcopy(self.analysis);a['groups'].pop()
        with self.assertRaises(ValueError):self.report(analysis=a)

    def test_intervals_nonfinite_and_relabeling_refused(self):
        for endpoints in [[1,0],[.1,.9],[float('nan'),1],[0,2]]:
            a=copy.deepcopy(self.analysis);a['groups'][0]['one_sided_005_bounds']=endpoints
            with self.subTest(endpoints=endpoints),self.assertRaises(ValueError):self.report(analysis=a)
        with self.assertRaises(ValueError):self.report(interval_tail='1/20')
        with self.assertRaises(ValueError):self.report(family_size=8)

    def test_failed_guard_withholds_even_reviewed_complete_claim(self):
        resource={**self.resource,'exit_code':1,'stop_reason':'counter failure'}
        raw=blob(resource);pin=digest(raw)
        h=StudyHistory(self.schedule).transition('planned',pin).transition('running',pin).transition('completed',pin)
        r=self.report(history=h,resources=[(raw,pin)])
        review={'bindings':r['bindings'],'disposition':'accepted_empirical_scope','review_sha256':'d'*64}
        accepted=self.report(history=h,resources=[(raw,pin)],review=review)
        self.assertFalse(accepted['complete_reviewed_empirical_scope'])

    def accept(self,analysis=None,history=None,resources=None):
        r=self.report(analysis=analysis,history=history,resources=resources)
        review={'bindings':r['bindings'],'disposition':'accepted_empirical_scope','review_sha256':'d'*64}
        return self.report(analysis=analysis,history=history,resources=resources,review=review)

    def test_each_analyzer_administrative_hold_overrides_review(self):
        for key,value in [('missing_jobs',1),('missing_observations',1),('jobs_missing_corresponding_observation',1),
                          ('truncated',True),('errors',['audit error']),
                          ('administrative_recovery',{'original_confirmatory_status_restored':False})]:
            a=copy.deepcopy(self.analysis);a[key]=value
            with self.subTest(key=key):
                r=self.accept(analysis=a);self.assertFalse(r['complete_reviewed_empirical_scope'])
                self.assertTrue(r['formal_hold_reasons'])
        for key in ['missing_jobs','missing_observations','truncated','errors','paired']:
            a=copy.deepcopy(self.analysis);a.pop(key)
            with self.subTest(missing=key):self.assertFalse(self.accept(analysis=a)['complete_reviewed_empirical_scope'])

    def test_primary_precision_holds_not_lost(self):
        for key,value in [('formal_gate_eligible',False),('precision_claim','descriptive_only'),('primary',None)]:
            a=copy.deepcopy(self.analysis);a['groups'][0][key]=value
            with self.subTest(key=key):self.assertFalse(self.accept(analysis=a)['complete_reviewed_empirical_scope'])
        a=copy.deepcopy(self.analysis);a['paired']['precision_claim']='descriptive_only'
        self.assertFalse(self.accept(analysis=a)['complete_reviewed_empirical_scope'])

    def test_each_guard_hold_overrides_review(self):
        for key,value in [('cleanup_notes',['UNCONTAINED measurement error']),('unknown_ledger_conservative_all_caps',True),
                          ('unit_ledger_known',1),('child_terminal',False),('receipt_persistence_error','failed')]:
            resource={**self.resource,key:value};raw=blob(resource);pin=digest(raw)
            h=StudyHistory(self.schedule).transition('planned',pin).transition('running',pin).transition('completed',pin)
            with self.subTest(key=key):self.assertFalse(self.accept(history=h,resources=[(raw,pin)])['complete_reviewed_empirical_scope'])
        resource=copy.deepcopy(self.resource);resource.pop('cleanup_notes');raw=blob(resource);pin=digest(raw)
        h=StudyHistory(self.schedule).transition('planned',pin).transition('running',pin).transition('completed',pin)
        self.assertFalse(self.accept(history=h,resources=[(raw,pin)])['complete_reviewed_empirical_scope'])

    def test_resumed_original_failure_does_not_restore_confirmatory_label(self):
        failed={**self.resource,'exit_code':1,'stop_reason':'counter race'};raw=blob(failed);pin=digest(raw)
        h=StudyHistory(self.schedule,(),'e'*64).transition('planned',pin).transition('running',pin).transition('interrupted',pin)
        h=h.transition('resumed',self.pin).transition('running',self.pin).transition('completed',self.pin)
        r=self.accept(history=h,resources=[(raw,pin),(self.raw,self.pin)])
        self.assertFalse(r['complete_reviewed_empirical_scope'])
        self.assertEqual(len(r['resource_receipts']),2)

    def test_missing_outcome_ranges_and_paired_audit_details_retained(self):
        a=copy.deepcopy(self.analysis);a['groups'][1].update(completed=0,detected=0,rate=0,one_sided_005_bounds=[0,.995],completion_bounds=[0,.995])
        a['errors']=['retained audit issue'];a['reference_advantage_gate_pass']=False
        r=self.report(analysis=a)
        self.assertEqual(r['groups'][1]['missing_outcome_sensitivity_fraction'],['0','1'])
        self.assertEqual(r['groups'][0]['missing_outcome_sensitivity_fraction'],['0','0'])
        self.assertEqual(r['paired'],a['paired']);self.assertEqual(r['errors'],a['errors'])
        text=render_markdown(r);self.assertIn('Missing-outcome range',text);self.assertIn('retained audit issue',text)
        self.assertIn('reference_minus_global20_power_gain_lower',text)

    def test_missing_or_duplicate_resource_receipt_refused(self):
        with self.assertRaises(ValueError):self.report(resources=[])
        with self.assertRaises(ValueError):self.report(resources=[(self.raw,self.pin),(self.raw,self.pin)])
        other=blob({'exit_code':0})
        with self.assertRaises(ValueError):self.report(resources=[(other,digest(other))])

    def test_resource_snapshots_not_double_summed(self):
        extra=blob({**self.resource,'phase':'prior','all_phase_reserved':{'ordinary_attempts':50}})
        r=self.report(resources=[(extra,digest(extra)),(self.raw,self.pin)])
        self.assertEqual(len(r['resource_receipts']),2);self.assertNotIn('total_ordinary_attempts',r)
        self.assertEqual(r['resource_receipts'][1]['receipt']['all_phase_reserved']['ordinary_attempts'],100)

    def test_history_retained_and_report_rendered_without_guarantee(self):
        text=render_markdown(self.report())
        self.assertIn('original-classroom-negative',text);self.assertIn('PWR-002-original',text)
        self.assertIn('descriptive only',text);self.assertIn('not measured zero power',text)
        self.assertNotIn('networkit',sys.modules);self.assertNotIn('degree_null.kernel',sys.modules)

    def test_analyzer_cannot_promote_authorization(self):
        a=copy.deepcopy(self.analysis);a['scientific_runtime_authorization_promoted']=True
        with self.assertRaises(ValueError):self.report(analysis=a)


if __name__=='__main__':unittest.main()
