"""Local text/HTML explanation and conditional predeclared triangle rank test."""
import html,json,math
from fractions import Fraction
from pathlib import Path
from .kernel import validate_graph
from .jobs import atomic,load,digest,canonical

def triangles(graph):
    adj=validate_graph(graph)
    return sum(len(adj[a]&adj[b])for a in range(len(adj))for b in adj[a]if a<b)//3
def summarize(folder,plan,status):
    observed=triangles(plan['input']['graph']);counts=[]
    for index in range(status['completed_outputs']):
        result=load(folder/f'graph-{index:06d}.json')
        if result['certificate']!=plan['certificate_plan']or result['job_fingerprint']!=plan['job_fingerprint']:raise ValueError('report constituent certificate/job mismatch')
        graph=result['graph']
        if result['graph_sha256']!=digest(canonical(graph))or[len(a)for a in validate_graph(graph)]!=plan['certificate_plan']['degrees']:raise ValueError('report graph hash/degree mismatch')
        counts.append(triangles(graph))
    total=Fraction(plan['config']['joint_tv']);alpha=Fraction(plan['config']['overall_alpha_target']);cutoff=Fraction(plan['config']['raw_rank_cutoff']);B=plan['config']['samples']
    full=status['status']=='completed_conditional_certificate'and len(counts)==B
    summary={'tool_version':'0.1.0','status':status['status'],'requested_outputs':B,'completed_outputs':len(counts),
      'observed_triangles':observed,'randomized_triangles':counts,'descriptive_only':True,'inference':None,
      'input_sha256':plan['input']['normalized_input_sha256'],'job_fingerprint':plan['job_fingerprint'],
      'config':plan['config'],'source_hashes':plan['source_hashes'],'source_commit':plan['source_commit'],
      'environment':plan['environment'],'resources_this_invocation':status['resources'],
      'joint_tv_budget_planned':str(total),'whole_batch_certificate_available':full,
      'joint_tv_contract':str(total)if full else None,'assurance':plan['assurance'],
      'model_warning':'preserving degrees does not establish that this null model suits the scientific question; no causation or importance claim',
      'selection_warning':'contract concerns the originally specified complete batch; no inference from partial jobs, selected seeds, chosen batches or posthoc statistics'}
    if full and plan['config']['statistic_predeclared']=='triangles':
        k=sum(x>=observed for x in counts);p=Fraction(k+1,B+1)
        summary['descriptive_only']=False
        summary['inference']={'statistic':'predeclared upper-tail triangles','exceedances':k,'rank_score_fraction':str(p),'rank_score':float(p),
          'resolution':str(Fraction(1,B+1)),'overall_alpha_target':str(alpha),'raw_rank_cutoff':str(cutoff),
          'conservative_decision_score_fraction':str(min(Fraction(1),p+total)),'rejects_at_overall_alpha':p<=cutoff,
          'conditional_typeI_upper':str(cutoff+total),
          'scope':'observed graph is itself uniform under fixed-degree null conditional on degrees; source theorem and independent ideal draws; test chosen before inspecting statistic/results; no adaptive seed/batch/output selection',
          'interpretation':'approximate-sampler Monte Carlo rank score, not an exact p-value or confidence interval; no multiplicity correction supplied'}
    return summary

def write_report(folder,plan,status):
    folder=Path(folder);summary=summarize(folder,plan,status);atomic(folder/'certificate-report.json',summary)
    config=plan['config'];input=plan['input'];cert=plan['certificate_plan'];complete=summary['completed_outputs']==config['samples']and status['status']=='completed_conditional_certificate'
    lines=['Degree-preserving Network Comparisons — private research tool v0.1',
      f"Job status: {status['status']}. Saved {summary['completed_outputs']} of {config['samples']} requested networks.",
      f"Input: {input['graph']['n']} nodes, {len(input['graph']['edges'])} links. Every named node keeps its original number of links, including declared isolates.",
      input['isolates_notice'],
      'Think of a network as people and friendships. These comparison networks reshuffle who is linked while keeping how many links each person has. A pattern can be compared with what happens under that particular reshuffling model.',
      'The sampler already exists. This tool adds a conservative theorem-derived trade schedule, error budgeting, checks and an evidence trail. It is not a faster-sampler claim.',
      'The possible mathematical contribution concerns ordinary undirected graphs. Related row-pair binary-matrix Curveball theory already has a universal spectral-gap bound in Fu–Qin–Wang (June2026). This tool does not implement that matrix model or claim firstness across Curveball settings.',
      f"Planned total: {plan['total_attempted_pair_trades']:,} attempted trades. Seed base: {config['seed']}; one CPU thread. Per-output TV budget: {config['per_output_tv']}; whole-batch TV budget: {config['joint_tv']}.",
      'TV describes a bound on how much probabilities can differ from the ideal randomization model. It does not measure whether that model explains real life.',
      plan['assurance'],
      'Random numbers come from a deterministic seeded PRNG. Separate seeds make runs reproducible; they do not prove mathematically ideal independence or exact uniformity.',
      f"Sampling and checkpointing in this invocation took {status['resources']['seconds']:.3f} seconds and observed a peak process memory of {status['resources']['peak_process_MiB']:.2f} MiB. This internal timer excludes initial planning and final report generation; lifetime memory may include earlier activity. End-to-end CLI measurements, when available, are separate evidence.",
      f"Observed triangles: {summary['observed_triangles']}. Randomized counts are a descriptive comparison, not proof of meaningful structure.",
      'A triangle is three nodes with all three possible links. The displayed distribution is descriptive; a predeclared test is a separate calculation.']
    if plan.get('coarse_rank_warning'):lines+=['The smallest attainable raw rank score exceeds the cutoff after allowing for sampler error. This batch is too coarse to reject at the overall alpha target.']
    if not complete:lines+=['This job is incomplete. No whole-batch certificate or hypothesis-test conclusion is available. Finished graphs have individual conditional certificates. Resume uses the original input and full schedule for any unfinished graph.']
    if summary['inference']:
        test=summary['inference'];lines+=[
          f"Predeclared upper-tail triangle test: {test['exceedances']} of {config['samples']} randomized counts were at least the observed count. Monte Carlo rank score: {test['rank_score_fraction']}.",
          f"Overall alpha target: {test['overall_alpha_target']}. Raw rank cutoff: {test['raw_rank_cutoff']} (target minus whole-batch TV). Conservative decision score: {test['conservative_decision_score_fraction']}. Decision: {'reject'if test['rejects_at_overall_alpha']else'do not reject'}. Under all stated null/theorem/randomness/predeclaration assumptions, type-I error is at most {test['conditional_typeI_upper']}.",
          'This is not an exact p-value from a perfect sampler, nor a 95% confidence statement. A non-rejection does not prove the null model true.',
          'Declaring a statistic in the command records your claim of predeclaration; software cannot verify that you selected it before seeing data. Multiple tests need a separate correction.']
    else:lines+=['No inferential test is reported. To request the demo, specify --statistic triangles --predeclared when creating the job; it remains subject to the stated assumptions.']
    lines+=['This analysis does not prove causation, scientific importance, or that the chosen null model is correct. Repeatedly changing seeds, selecting interesting batches or testing after looking invalidates the advertised inferential interpretation.',
      f"Input hash: {summary['input_sha256']}",f"Source manuscript pin: {plan['source_commit']}",
      'Output graph JSON files use integer IDs. labels.json preserves the exact external labels, including isolates. Export creates a labeled CSV for a selected graph.',
      'Files: plan.json (immutable scientific configuration); graph-*.json (one fully finished graph per file); labels.json; status.json; attempts.jsonl; certificate-report.json; report.txt; report.html.']
    text='\n\n'.join(lines)+'\n';(folder/'report.txt').write_text(text,encoding='utf-8')
    histogram={}
    for x in summary['randomized_triangles']:histogram[x]=histogram.get(x,0)+1
    rows=''.join(f'<tr><td>{value}</td><td>{count}</td></tr>'for value,count in sorted(histogram.items()))
    label_rows=''.join(f'<tr><td>{i}</td><td>{html.escape(label)}</td><td>{input["degrees"][i]}</td></tr>'for i,label in enumerate(input['labels']))
    page='<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width"><title>Degree-preserving Network Comparisons</title><style>body{max-width:850px;margin:40px auto;padding:0 20px;font:17px/1.6 system-ui;color:#182b3a}h1{line-height:1.15}table{border-collapse:collapse;width:100%;margin:20px 0}th,td{text-align:left;border-bottom:1px solid #ddd;padding:7px}.note{background:#eef5f9;padding:16px}code{overflow-wrap:anywhere}</style><h1>Degree-preserving Network Comparisons</h1>'
    page+=''.join('<p>'+html.escape(line)+'</p>'for line in lines)
    page+='<h2>Descriptive triangle-count distribution</h2><p>Counts among completed outputs only. This table is not an inferential significance claim.</p><table><tr><th>Triangles</th><th>Networks</th></tr>'+rows+'</table>'
    page+='<h2>Label and degree audit</h2><table><tr><th>Integer ID</th><th>Original label</th><th>Links retained</th></tr>'+label_rows+'</table></html>'
    (folder/'report.html').write_text(page,encoding='utf-8');return summary
