"""Strict UTF-8 CSV/edge-list ingestion with explicit external-label mapping."""
import csv, hashlib, io, json
from pathlib import Path
from .kernel import validate_graph

INPUT_BYTE_LIMIT=20*1024*1024
def _bytes(path):
    p=Path(path)
    if p.stat().st_size>INPUT_BYTE_LIMIT:raise ValueError('input exceeds20MiB prototype limit')
    return p.read_bytes()
def _label(value):
    if not isinstance(value,str) or not value or '\0' in value or len(value)>512:
        raise ValueError('labels must be nonempty strings of at most512 characters without NUL')
    return value

def _rows(text,format):
    if format=='csv':
        reader=csv.reader(io.StringIO(text,newline=''))
        if next(reader,None)!=['source','target']:raise ValueError('CSV header must be exactly source,target; weights/direction/extra fields unsupported')
        for line,row in enumerate(reader,2):
            if len(row)!=2:raise ValueError(f'CSV record{line} must contain exactly two labels')
            yield(_label(row[0]),_label(row[1]))
    elif format=='edgelist':
        for line,record in enumerate(io.StringIO(text),1):
            if not record.strip():continue
            row=record.split()
            if len(row)!=2:raise ValueError(f'edge-list line{line} needs two whitespace-separated labels; useCSV for labels containing spaces')
            yield(_label(row[0]),_label(row[1]))
    else:raise ValueError('format must be csv or edgelist')

def read_network(path,format='csv',vertices=None,directed=False,weighted=False):
    """Return integer graph, bijective labels, raw input hashes and assumptions.

    Vertices, when supplied, declare the complete node universe, not just isolates.
    Their order fixes IDs. Otherwise labels follow first appearance in edges.
    """
    if directed or weighted:raise ValueError('directed/weighted input is unsupported; no automatic conversion')
    raw=_bytes(path);text=raw.decode('utf-8-sig')
    sources=[{'kind':'edges','path':str(Path(path).resolve()),'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw)}]
    labels=[];lookup={}
    if vertices is not None:
        vr=_bytes(vertices);vt=vr.decode('utf-8-sig')
        declared=json.loads(vt)if Path(vertices).suffix.lower()=='.json'else vt.splitlines()
        if not isinstance(declared,list):raise ValueError('vertices JSON must be an array of labels')
        for value in declared:
            label=_label(value)
            if label in lookup:raise ValueError('duplicate vertex label')
            if len(labels)>=1000:raise ValueError('prototype supports at most1000 nodes')
            lookup[label]=len(labels);labels.append(label)
        sources.append({'kind':'vertices','path':str(Path(vertices).resolve()),'sha256':hashlib.sha256(vr).hexdigest(),'bytes':len(vr)})
    edges=[];seen=set()
    for a,b in _rows(text,format):
        if a==b:raise ValueError(f'self-loop at label{a!r}; no silent deletion')
        for label in (a,b):
            if label not in lookup:
                if vertices is not None:raise ValueError(f'edge endpoint{label!r} absent from declared vertex universe')
                if len(labels)>=1000:raise ValueError('prototype supports at most1000 nodes')
                lookup[label]=len(labels);labels.append(label)
        pair=tuple(sorted((lookup[a],lookup[b])))
        if pair in seen:raise ValueError(f'duplicate undirected edge{a!r},{b!r}; reversed duplicates also rejected')
        seen.add(pair);edges.append(list(pair))
    graph={'n':len(labels),'edges':sorted(edges)}
    adj=validate_graph(graph)
    normalized={'graph':graph,'labels':labels}
    digest=hashlib.sha256(json.dumps(normalized,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    return {'graph':graph,'labels':labels,'degrees':[len(x)for x in adj],'input_sources':sources,'normalized_input_sha256':digest,
      'isolates_declared':vertices is not None,'isolates_notice':'complete declared vertex universe retained'if vertices is not None else'only edge endpoints are known; provide --vertices to include isolated nodes',
      'input_assumptions':'user declares input simple undirected unweighted; direction cannot be inferred from two columns'}

def labeled_csv(graph,labels):
    stream=io.StringIO(newline='');writer=csv.writer(stream);writer.writerow(['source','target'])
    for a,b in graph['edges']:writer.writerow([labels[a],labels[b]])
    return stream.getvalue()
