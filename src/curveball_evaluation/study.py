"""Read the exact reviewed PWR-002 descriptive evidence, without simulation.

Copyright 2026 DaniilKi contributors. SPDX-License-Identifier: Apache-2.0
"""
from fractions import Fraction
import hashlib
from importlib import resources
import json

PINS = {
    'provenance.json':'dd78c67760da5f77d3a4d9f577648580c373944df9dd81f58cfde64396fad4c7',
    'analysis.json':'f7e57937b122ca06f1191868d0306d8dafe69d594ca39b6b0e8951ce67257bf1',
    'review-050.json':'31f03e328d100083423845429c363dcbe9a03dbaf253a6fa3d3e0329c7d5c29d',
    'REPORT.md':'e3370a1f3d3437a1af120b19b6bea5cd5f4451baafb3f1fbbb4df57051042c5d',
}


def _read(name):
    raw=resources.files('curveball_evaluation').joinpath('data',name).read_bytes()
    if hashlib.sha256(raw).hexdigest()!=PINS[name]:
        raise ValueError('bundled accepted artifact digest mismatch: '+name)
    return raw


def load_pwr002():
    """Return a fresh evidence object; this is no sampling or assurance API.

    The accepted analyzer/report/review bytes are shipped unchanged. Provenance
    is a sanitized release projection of separately retained private evidence.
    Full raw seeds/graphs/guard paths are not distributed in this public package.
    """
    analysis=json.loads(_read('analysis.json'))
    review=json.loads(_read('review-050.json'))
    report=_read('REPORT.md').decode('utf-8')
    provenance=json.loads(_read('provenance.json'))
    if review['status']!='accepted_descriptive_result_evidence' or analysis['status']!='censored_formal_claims_withheld':
        raise ValueError('bundled evidence scope changed')
    if review['accepted_result_pins']['combined-run/ANALYSIS.json']!=PINS['analysis.json']:
        raise ValueError('accepted review/analysis binding mismatch')
    if analysis['scientific_runtime_authorization_promoted'] is not False or review['original_confirmatory_status_restored'] is not False:
        raise ValueError('bundled claim hold changed')
    if any(g['formal_gate_eligible'] is not False or g['precision_claim']!='descriptive_only' for g in analysis['groups']):
        raise ValueError('bundled group precision hold changed')
    if analysis['paired']['precision_claim']!='descriptive_only':
        raise ValueError('bundled paired precision hold changed')
    counts=review['independent_audit_counts']
    if sum(g['N'] for g in analysis['groups'])!=counts['scheduled_jobs'] or sum(g['completed'] for g in analysis['groups'])!=counts['completed_jobs']:
        raise ValueError('bundled denominator mismatch')
    for group in analysis['groups']:
        n=group['N'];d=group['detected'];missing=n-group['completed']
        group['missing_outcome_sensitivity_fraction']=[str(Fraction(d,n)),str(Fraction(d+missing,n))]
    return {'schema_version':1,'study':'PWR-002','status':'accepted_descriptive_evidence',
            'analysis':analysis,'review':review,'provenance':provenance,
            'accepted_report_markdown':report,
            'complete_reviewed_empirical_scope':False,
            'original_confirmatory_status_restored':False,
            'scientific_runtime_authorization_promoted':False,'tv_assurance_authorized':False,
            'ideal_randomness_claim':False,'graph_refinement_binary_claim':False,
            'fast_backend_verification_status':'unchanged; no end-to-end verification established',
            'scope':'prescribed topology-retention simulation; descriptive only; no real power-flow/fault-detection validation, reliable-power certification or new-mathematics speed advantage',
            'missing_outcome_scope':'all missing assigned non-detection versus detection; exact sensitivity range, not a confidence interval'}


def render_pwr002(evidence):
    """Show preserved accepted prose with explicit package/archive context."""
    prefix=('# Packaged descriptive evidence\n\n'
            'This command reads saved results and runs no sampler. Independent review 050 accepted the descriptive evidence; the original confirmatory status remains withdrawn.\n\n'
            'The original report below is preserved verbatim. Its references to an archive and retained seeds/graphs mean the private research archive, not this wheel. The wheel contains aggregate analysis, accepted prose, review receipt and sanitized provenance only.\n\n')
    return prefix+evidence['accepted_report_markdown']
