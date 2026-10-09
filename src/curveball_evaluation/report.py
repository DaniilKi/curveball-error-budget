"""Bind an existing study analyzer to frozen schedules and retained run history.

This module performs no sampling, graph-law audit, interval calculation or proof.
The maintained producer/analyzer owns those operations. Digests bind bytes, not
reviewer identity. Reports are private until separately reviewed for publication.
Copyright 2026 DaniilKi contributors. SPDX-License-Identifier: Apache-2.0
"""
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
import math

LIMIT = 32 * 2**20
STATES = {'planned', 'running', 'completed', 'censored', 'interrupted', 'resumed', 'failed'}
TRANSITIONS = {
    'planned': {'running'},
    'running': {'completed', 'censored', 'interrupted', 'failed'},
    'resumed': {'running', 'completed', 'censored', 'interrupted', 'failed'},
    'interrupted': {'resumed'}, 'censored': {'resumed'}, 'completed': set(), 'failed': set(),
}


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def _pin(value):
    if not isinstance(value, str) or len(value) != 64 or any(c not in '0123456789abcdef' for c in value):
        raise ValueError('expected a lowercase SHA256 digest')
    return value


def _text(value):
    if not isinstance(value, str) or not value or len(value) > 200 or any(ord(c) < 32 for c in value):
        raise ValueError('expected bounded nonempty text')
    return value


def _nat(value, maximum=2**64-1):
    if type(value) is not int or not 0 <= value <= maximum:
        raise ValueError('expected a bounded nonnegative integer')
    return value


def _seed(value):
    # The maintained schedule serializes uint64 seeds as canonical decimals.
    # Normalize the value, while the original JSON digest preserves its bytes.
    if type(value) is str:
        if not 1 <= len(value) <= 20 or not value.isascii() or not value.isdecimal() or (len(value)>1 and value[0]=='0'):
            raise ValueError('expected canonical unsigned decimal seed')
        value=int(value)
    return _nat(value)


def _json(raw, expected):
    if not isinstance(raw, bytes) or len(raw) > LIMIT or digest(raw) != _pin(expected):
        raise ValueError('artifact size or digest mismatch')
    def unique(pairs):
        out = {}
        for key, value in pairs:
            if key in out:
                raise ValueError('duplicate JSON key')
            out[key] = value
        return out
    return json.loads(raw, object_pairs_hook=unique,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))


@dataclass(frozen=True)
class Job:
    id: str
    observation_id: str
    case: str
    condition: str
    method: str
    seeds: tuple[int, ...]


@dataclass(frozen=True)
class FrozenStudy:
    protocol_id: str
    protocol_sha256: str
    observations_sha256: str
    jobs_sha256: str
    observation_seeds: tuple[tuple[str, int], ...]
    jobs: tuple[Job, ...]
    outputs_per_job: int

    def __post_init__(self):
        _text(self.protocol_id)
        for value in (self.protocol_sha256,self.observations_sha256,self.jobs_sha256):
            _pin(value)
        if type(self.observation_seeds) is not tuple or type(self.jobs) is not tuple:
            raise ValueError('frozen schedule must use immutable tuples')
        if not 1 <= _nat(self.outputs_per_job,1000) or not self.jobs or len(self.jobs)>50000:
            raise ValueError('invalid frozen job/output count')
        ids=set(); seeds=set(); observations=set()
        for item in self.observation_seeds:
            if type(item) is not tuple or len(item)!=2:
                raise ValueError('invalid frozen observation')
            oid,seed=item;_text(oid);_nat(seed)
            if oid in observations or seed in seeds:
                raise ValueError('duplicate frozen observation/seed')
            observations.add(oid);seeds.add(seed)
        linked=set()
        for job in self.jobs:
            if type(job) is not Job or type(job.seeds) is not tuple or len(job.seeds)!=self.outputs_per_job:
                raise ValueError('invalid immutable job')
            for value in (job.id,job.observation_id,job.case,job.condition,job.method):_text(value)
            if job.id in ids or job.observation_id not in observations:
                raise ValueError('invalid frozen job identity')
            ids.add(job.id);linked.add(job.observation_id)
            for seed in job.seeds:
                _nat(seed)
                if seed in seeds:raise ValueError('duplicate frozen seed')
                seeds.add(seed)
        if linked!=observations:raise ValueError('unlinked frozen observation')

    @classmethod
    def from_json(cls, protocol_id, protocol_sha256, observations, jobs, *,
                  observations_sha256, jobs_sha256, outputs_per_job):
        """Freeze the original producer schedule, including every seed and job."""
        b = _nat(outputs_per_job, 1000)
        if b == 0:
            raise ValueError('positive output count required')
        obs = _json(observations, observations_sha256)
        rows = _json(jobs, jobs_sha256)
        if not isinstance(obs, list) or not isinstance(rows, list) or not obs or not rows or len(rows) > 50000:
            raise ValueError('expected nonempty bounded schedules')
        index = {}; seen_seeds = set(); obs_seeds = []
        for row in obs:
            oid = _text(row['id']); seed = _seed(row['seed'])
            case = _text(row['case']); condition = _text(row['condition'])
            if oid in index or seed in seen_seeds:
                raise ValueError('duplicate observation identity or seed')
            index[oid] = (case, condition); seen_seeds.add(seed); obs_seeds.append((oid, seed))
        frozen = []; ids = set(); linked = set()
        for row in rows:
            jid = _text(row['id']); oid = _text(row['observation_id'])
            case = _text(row['case']); condition = _text(row['condition']); method = _text(row['method'])
            seeds = row['seeds']
            if jid in ids or oid not in index or index[oid] != (case, condition):
                raise ValueError('job identity or observation/group mismatch')
            if not isinstance(seeds, list) or len(seeds) != b:
                raise ValueError('output denominator mismatch')
            normalized=[]
            for raw_seed in seeds:
                seed=_seed(raw_seed)
                if seed in seen_seeds:
                    raise ValueError('duplicate original seed')
                seen_seeds.add(seed)
                normalized.append(seed)
            ids.add(jid); linked.add(oid)
            frozen.append(Job(jid, oid, case, condition, method, tuple(normalized)))
        if linked != set(index):
            raise ValueError('scheduled observation has no job')
        return cls(_text(protocol_id), _pin(protocol_sha256), observations_sha256, jobs_sha256,
                   tuple(obs_seeds), tuple(frozen), b)

    @property
    def identity(self):
        return {'protocol_id': self.protocol_id, 'protocol_sha256': self.protocol_sha256,
                'observations_sha256': self.observations_sha256, 'jobs_sha256': self.jobs_sha256}


@dataclass(frozen=True)
class StudyHistory:
    """Immutable administrative states. Recording resume never runs a job."""
    schedule: FrozenStudy
    # Entries: state, receipt hash. Original receipts stay external and immutable.
    events: tuple[tuple[str, str], ...] = ()
    resume_policy_sha256: str | None = None

    def transition(self, state, receipt_sha256):
        _pin(receipt_sha256)
        previous = self.events[-1][0] if self.events else None
        if state not in STATES or (previous is None and state != 'planned') or (
                previous is not None and state not in TRANSITIONS[previous]):
            raise ValueError('invalid study state transition')
        if state == 'resumed' and self.resume_policy_sha256 is None:
            raise ValueError('resume requires a separately reviewed protocol policy')
        if self.resume_policy_sha256 is not None:
            _pin(self.resume_policy_sha256)
        return StudyHistory(self.schedule, self.events + ((state, receipt_sha256),), self.resume_policy_sha256)


def _interval(value, count, n):
    if not isinstance(value, list) or len(value) != 2:
        raise ValueError('expected a two-endpoint analyzer interval')
    if any(type(x) not in (int, float) or not math.isfinite(x) for x in value):
        raise ValueError('invalid interval endpoint')
    lo, hi = value
    if not 0 <= lo <= count/n <= hi <= 1:
        raise ValueError('interval does not contain its measured rate')
    return list(value)


def build_report(history, analysis, *, analysis_sha256, analyzer_sha256,
                 resources, prior_evidence, interval_tail='1/200', family_size=10,
                 review=None):
    """Render existing analyzer measurements without changing their denominators.

    resources: sequence of (raw JSON receipt bytes, expected SHA256) pairs.
    prior_evidence: retained negative/failed artifact identities, never replaced.
    review: optional externally authenticated review binding to these exact pins;
    this API checks binding only. It grants no scientific runtime authorization.
    Existing analyzer computes and audits graph/rank/interval results; this layer
    validates grouping/counts and copies intervals, without another analyzer.
    """
    if type(history) is not StudyHistory or type(history.schedule) is not FrozenStudy or type(history.events) is not tuple or not history.events:
        raise ValueError('missing study history')
    checked = StudyHistory(history.schedule,(),history.resume_policy_sha256)
    for state,pin in history.events:
        checked = checked.transition(state,pin)
    schedule = history.schedule; a = _json(analysis, analysis_sha256)
    _pin(analyzer_sha256)
    if not isinstance(a, dict) or not isinstance(a.get('groups'), list):
        raise ValueError('missing analyzer groups')
    if a.get('scientific_runtime_authorization_promoted') is not False:
        raise ValueError('analyzer must explicitly retain authorization hold')
    tail = Fraction(interval_tail); family = _nat(family_size, 1000)
    # This adapter consumes the maintained PWR-002 analyzer's fixed fields.
    # A different interval contract needs an explicit adapter/review, not relabeling.
    if tail != Fraction(1, 200) or family != 10:
        raise ValueError('unsupported analyzer interval contract')
    denominators = Counter((j.case, j.condition, j.method) for j in schedule.jobs)
    groups = []; seen = set(); holds=[]
    for key in ('missing_jobs','missing_observations','jobs_missing_corresponding_observation'):
        if type(a.get(key)) is not int or a[key]!=0:
            holds.append('analyzer '+key+' is missing or nonzero')
    if a.get('truncated') is not False:holds.append('analyzer stream not explicitly untruncated')
    if a.get('errors') != []:holds.append('analyzer errors missing or present')
    recovery=a.get('administrative_recovery',{})
    if not isinstance(recovery,dict):holds.append('invalid administrative recovery metadata')
    elif recovery.get('original_confirmatory_status_restored') is False:
        holds.append('original confirmatory status remains withdrawn')
    for row in a['groups']:
        key = tuple(_text(row[k]) for k in ('case', 'condition', 'method'))
        if key in seen or key not in denominators:
            raise ValueError('duplicate or unscheduled analyzer group')
        seen.add(key); n = _nat(row['N']); complete = _nat(row['completed']); detected = _nat(row['detected'])
        if n != denominators[key] or not 0 <= detected <= complete <= n:
            raise ValueError('scheduled denominator/completion/detection mismatch')
        rate = row['rate']
        if type(rate) not in (int, float) or not math.isfinite(rate) or abs(rate-detected/n) > 1e-12:
            raise ValueError('rate differs from immutable denominator')
        if type(row.get('primary')) is not bool:
            holds.append('group primary status missing: '+str(key))
        elif row['primary']:
            if row.get('formal_gate_eligible') is not True or row.get('precision_claim')!='confirmatory_conditional_IID':
                holds.append('primary group formal hold: '+str(key))
        elif row.get('precision_claim')!='descriptive_only' or row.get('formal_gate_eligible') is not False:
            holds.append('nonprimary group precision scope inconsistent: '+str(key))
        groups.append({'case':key[0], 'condition':key[1], 'method':key[2],
                       'scheduled':n, 'completed':complete, 'not_completed':n-complete,
                       'detections':detected, 'rate_fraction':str(Fraction(detected,n)),
                       'measurement':'calibration' if key[1]=='null' else 'power_under_specified_alternative',
                       'primary':row.get('primary'),
                       'analyzer_formal_gate_eligible':row.get('formal_gate_eligible'),
                       'analyzer_precision_claim':row.get('precision_claim'),
                       'missing_outcome_sensitivity_fraction':[str(Fraction(detected,n)),str(Fraction(detected+n-complete,n))],
                       'sensitivity_scope':'all missing outcomes assigned non-detection versus detection; not a confidence interval',
                       'rate_bounds':_interval(row['one_sided_005_bounds'],detected,n),
                       'completion_bounds':_interval(row['completion_bounds'],complete,n)})
    if seen != set(denominators):
        raise ValueError('missing scheduled analyzer group')
    if not any(g['primary'] is True for g in groups):holds.append('no explicitly primary analyzer group')
    receipts = []
    for raw, pin in resources:
        value = _json(raw,pin)
        if not isinstance(value, dict):
            raise ValueError('expected resource receipt object')
        receipts.append({'sha256':pin,'receipt':value})
    if not receipts:
        raise ValueError('resource receipts required, including failures')
    receipt_map = {r['sha256']:r['receipt'] for r in receipts}
    if len(receipt_map) != len(receipts) or any(p not in receipt_map for _,p in history.events):
        raise ValueError('duplicate receipt or missing history receipt')
    # Retaining an earlier failed/censored execution never silently restores
    # the original confirmatory experiment, even if a continuation finishes.
    for pin,value in receipt_map.items():
        if 'exit_code' not in value:continue  # protocol/design receipt
        for key,clean in [('exit_code',0),('stop_reason',None),('cleanup_notes',[]),
                          ('unit_ledger_known',True),('unknown_ledger_conservative_all_caps',False)]:
            wrong_type=(key=='exit_code' and type(value.get(key)) is not int) or (type(clean) is bool and type(value.get(key)) is not bool)
            if key not in value or value[key]!=clean or wrong_type:
                holds.append('execution receipt hold '+key+': '+pin)
        if value.get('child_terminal') is not True:holds.append('execution child not terminal: '+pin)
        if value.get('receipt_persistence_error') is not None:holds.append('execution receipt persistence failure: '+pin)
    retained = []
    for item in prior_evidence:
        retained.append({'id':_text(item['id']),'sha256':_pin(item['sha256']),'status':_text(item['status'])})
    if len({x['id'] for x in retained}) != len(retained):
        raise ValueError('duplicate historical artifact id')
    if not retained:
        raise ValueError('retained historical evidence required')
    def object_pin(value):
        return digest(json.dumps(value,sort_keys=True,separators=(',',':')).encode())
    bindings = {**schedule.identity,'analysis_sha256':analysis_sha256,'analyzer_sha256':analyzer_sha256,
                'history_sha256':object_pin({'events':history.events,'resume_policy_sha256':history.resume_policy_sha256}),
                'resources_sha256':object_pin([r['sha256'] for r in receipts]),
                'prior_evidence_sha256':object_pin(retained)}
    accepted = False; review_identity = None
    if review is not None:
        if review.get('bindings') != bindings or review.get('disposition') != 'accepted_empirical_scope':
            raise ValueError('review does not bind exact empirical artifacts')
        review_identity = _pin(review['review_sha256']); accepted = True
    terminal = history.events[-1][0]
    all_complete = all(g['not_completed']==0 for g in groups)
    final_receipt = receipt_map[history.events[-1][1]]
    guard_complete = (type(final_receipt.get('exit_code')) is int and final_receipt['exit_code']==0
                      and final_receipt.get('stop_reason') is None
                      and final_receipt.get('child_terminal') is True
                      and final_receipt.get('unit_ledger_known') is True)
    paired=a.get('paired')
    if not isinstance(paired,dict) or paired.get('precision_claim')!='confirmatory_conditional_IID':
        holds.append('paired analysis missing or under formal hold')
    formal_eligible = accepted and terminal=='completed' and all_complete and guard_complete and a.get('status')=='fully_audited' and not holds
    return {'schema_version':1,'kind':'research_evaluation_report','bindings':bindings,
            'history':[{'state':s,'receipt_sha256':p} for s,p in history.events],
            'state':terminal,'resume_policy_sha256':history.resume_policy_sha256,
            'scheduled_observations':len(schedule.observation_seeds),'scheduled_jobs':len(schedule.jobs),
            'outputs_per_job':schedule.outputs_per_job,
            'seed_policy':'original frozen seeds; no replacement or denominator deletion',
            'groups':groups,'resource_receipts':receipts,'resource_aggregation':'cumulative reservations are retained per receipt; never summed as disjoint costs',
            'prior_evidence':retained,'external_review_binding_matched':accepted,'review_sha256':review_identity,
            'complete_reviewed_empirical_scope':formal_eligible,
            'formal_hold_reasons':holds,
            'errors':a.get('errors'),
            'audit':{k:a.get(k) for k in ('missing_jobs','missing_observations','jobs_missing_corresponding_observation',
                      'truncated','audited_graphs','audited_accepted_stub_vectors','unattributed_reservations','administrative_recovery')},
            'paired':paired,
            'analyzer_gain_and_gate_diagnostics':{k:a.get(k) for k in ('reliability_gates_pass','reference_advantage_gate_pass',
                           'matched605_realized_ratio','matched605_cost_label_valid')},
            'diagnostic_scope':'copied analyzer diagnostics; hold reasons override labels; no restored claim for an administratively interrupted experiment',
            'intervals':{'source':'maintained analyzer; endpoints copied, not recomputed here',
                         'one_sided_tail':str(tail),'family_size':family,
                         'assumptions':'binomial intervals require the protocol IID operational-job assumptions; finite deterministic seeds do not prove them',
                         'claim_status':'reviewed conditional empirical scope' if formal_eligible else 'descriptive only; accepted complete empirical conclusions withheld'},
            'mathematical_guarantees':'Only separately bound operator/native results under their stated hypotheses; measured outcomes establish no theorem or backend refinement.',
            'fast_backend_verification_status':'unchanged; no end-to-end verification established by this report',
            'scientific_runtime_authorization_promoted':False,'tv_assurance_authorized':False,
            'ideal_randomness_claim':False,'graph_refinement_binary_claim':False}


def render_markdown(report):
    """Private human-readable summary, with the full machine report alongside."""
    def escape(value):
        return str(value).replace('&','&amp;').replace('<','&lt;').replace('>','&gt;').replace('\\','\\\\').replace('|','\\|').replace('\n',' ').replace('`','\\`')
    lines=['# Research evaluation evidence', '',
           'Study: '+escape(report['bindings']['protocol_id'])+'. State: '+escape(report['state'])+'.',
           '', report['intervals']['claim_status']+'.', '',
           '| Case | Condition | Method | Scheduled | Completed | Detections | Rate | Rate bounds | Completion bounds | Missing-outcome range |',
           '|---|---|---|---:|---:|---:|---|---|---|---|']
    for row in report['groups']:
        keys=('case','condition','method','scheduled','completed','detections','rate_fraction','rate_bounds','completion_bounds','missing_outcome_sensitivity_fraction')
        lines.append('| '+' | '.join(escape(row[k]) for k in keys)+' |')
    lines += ['', 'Failures, censoring and interruptions remain in the scheduled denominator. They are not measured zero power or completed non-rejections.',
              '', 'Missing-outcome ranges assign every missing outcome either non-detection or detection; these ranges are not confidence intervals.',
              '', 'Formal holds: '+escape(report['formal_hold_reasons'])+'.',
              '', 'Audit errors: '+escape(report['errors'])+'.',
              '', 'Audit coverage: '+escape(report['audit'])+'.',
              '', 'Paired/gain diagnostics (copied from analyzer; subject to the holds above): '+escape(report['paired'])+'.',
              '', 'Other analyzer gate/cost diagnostics: '+escape(report['analyzer_gain_and_gate_diagnostics'])+'.',
              '', 'Intervals: one-sided tail '+report['intervals']['one_sided_tail']+'; family size '+str(report['intervals']['family_size'])+'. '+report['intervals']['assumptions']+'.',
              '', report['resource_aggregation']+'.', '', report['mathematical_guarantees'],
              '', report['fast_backend_verification_status']+'. Scientific runtime authorization remains unchanged.',
              '', 'Retained prior evidence: '+', '.join(escape(x['id']) for x in report['prior_evidence'])+'.']
    return '\n'.join(lines)+'\n'
