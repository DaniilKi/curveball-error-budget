"""Fail-closed invocation of the installed Lean arithmetic checker.

Hashes bind a request to locally trusted artifacts; they are not authentication.
Python validation, subprocess I/O, compiler, cached dependencies, OS and hardware
remain trusted. This API makes no graph-execution or sampling-law claim.
"""
from pathlib import Path
import hashlib
import json
import math
import os
import re
import subprocess
import time

ASSURANCE = 'checked_arithmetic'
GRAMMAR = re.compile(rb'CBARITH1 (budget|rank) (0|[1-9][0-9]*) (0|[1-9][0-9]*) '
                     rb'(0|[1-9][0-9]*) (0|[1-9][0-9]*) (0|[1-9][0-9]*) '
                     rb'(0|[1-9][0-9]*)\n\Z')
CAPS = {'budget': (104, 5356, 10**12, 10**12, 100000, 535600000),
        'rank': (1000000, 1000000, 10**12, 10**12, 10**12, 10**12)}

class InvocationError(RuntimeError):
    def __init__(self, code, detail='', evidence=None):
        super().__init__(code + (': '+detail if detail else ''))
        self.code, self.detail, self.evidence = code, detail, evidence or {}

def sha256(data):
    return hashlib.sha256(data).hexdigest()

def validate_request(wire):
    if not isinstance(wire, bytes) or len(wire) > 1024:
        raise InvocationError('malformed_request', 'expected at most 1024 bytes')
    match = GRAMMAR.fullmatch(wire)
    if match is None:
        raise InvocationError('malformed_request', 'noncanonical bytes')
    mode = match[1].decode('ascii')
    fields = tuple(int(x) for x in match.groups()[1:])
    if any(x > cap for x, cap in zip(fields, CAPS[mode])):
        raise InvocationError('resource_cap')
    if mode == 'budget' and fields[0] < 4:
        raise InvocationError('unsupported_graph_domain', 'n>=4 required by installation policy; graph provenance still unverified')
    return mode, fields

def read_installation(path, expected_sha256):
    try:
        with Path(path).open('rb') as stream:
            data = stream.read(262145)
    except (OSError, TypeError, ValueError) as exc:
        raise InvocationError('missing_installation', str(exc)) from exc
    if len(data) > 262144:
        raise InvocationError('invalid_installation', 'manifest exceeds 256 KiB')
    if not isinstance(expected_sha256, str) or sha256(data) != expected_sha256:
        raise InvocationError('installation_digest_mismatch')
    try:
        def unique_keys(pairs):
            result = {}
            for key, value in pairs:
                if key in result: raise ValueError('duplicate JSON key')
                result[key] = value
            return result
        manifest = json.loads(data, object_pairs_hook=unique_keys)
        if not isinstance(manifest,dict): raise ValueError('expected object')
        if type(manifest['schema']) is not int or manifest['schema'] not in (1,2) or manifest['assurance'] != ASSURANCE:
            raise ValueError('unknown schema or assurance')
        if type(manifest['max_request_bytes']) is not int or manifest['max_request_bytes'] != 1024:
            raise ValueError('unknown byte limit')
        def valid_path(path):
            return isinstance(path,str) and bool(path) and '\x00' not in path and Path(path).is_absolute()
        if not valid_path(manifest['entrypoint']) or not valid_path(manifest['lean']):
            raise ValueError('entrypoint/runtime must be absolute paths')
        paths=manifest['lean_path']
        if not isinstance(paths,list) or not paths or not all(valid_path(p) for p in paths):
            raise ValueError('lean_path must be a nonempty list of absolute paths')
        if not isinstance(manifest['artifacts'],list) or len(manifest['artifacts']) < 6:
            raise ValueError('incomplete artifact list')
        for item in manifest['artifacts']:
            if not isinstance(item,dict) or not valid_path(item['path']):
                raise ValueError('invalid artifact path')
            if not isinstance(item['sha256'],str) or not re.fullmatch('[0-9a-f]{64}',item['sha256']):
                raise ValueError('invalid artifact digest')
        pinned_paths = [item['path'] for item in manifest['artifacts']]
        if len({os.path.normcase(p) for p in pinned_paths}) != len(pinned_paths):
            raise ValueError('duplicate artifact')
        if manifest['entrypoint'] not in pinned_paths or manifest['lean'] not in pinned_paths:
            raise ValueError('entrypoint or runtime unpinned')
        if str(Path(manifest['entrypoint']).with_suffix('.olean')) not in pinned_paths:
            raise ValueError('entrypoint compiled artifact unpinned')
        if manifest['schema']==2:
            if manifest['execution']!='native' or not valid_path(manifest['native_executable']):
                raise ValueError('invalid native execution mode/path')
            if manifest['native_executable'] not in pinned_paths:
                raise ValueError('native executable unpinned')
    except (KeyError, TypeError, ValueError, UnicodeError) as exc:
        raise InvocationError('invalid_installation', str(exc)) from exc
    verify_artifacts(manifest)
    return manifest

def verify_artifacts(manifest):
    for item in manifest['artifacts']:
        try:
            h=hashlib.sha256()
            with Path(item['path']).open('rb') as stream:
                while block:=stream.read(1024*1024):h.update(block)
            actual=h.hexdigest()
        except OSError as exc:
            raise InvocationError('missing_artifact', item['path']) from exc
        if actual != item['sha256']:
            raise InvocationError('artifact_digest_mismatch', item['path'])

def parse_response(mode, stdout, stderr, code):
    evidence = {'exit_code':code,'stdout_hex':stdout.hex(),'stderr_hex':stderr.hex()}
    if code != 0:
        raise InvocationError('checker_failure', evidence=evidence)
    if stderr:
        raise InvocationError('unexpected_stderr', evidence=evidence)
    allowed = {f'CBARITH1 result {mode} true\n'.encode():True,
               f'CBARITH1 result {mode} false\n'.encode():False}
    if stdout not in allowed:
        raise InvocationError('noncanonical_response', evidence=evidence)
    return allowed[stdout]

def invoke(wire, installation, expected_sha256, *, backend='lean_arithmetic',
           resume=False, timeout_seconds=45):
    start = time.monotonic()
    evidence = {'request_sha256':sha256(wire) if isinstance(wire,bytes) else None,
                'request_hex':wire.hex() if isinstance(wire,bytes) else None,
                'installation_sha256':expected_sha256, 'backend':backend,
                'resume':resume}
    try:
        if backend != 'lean_arithmetic':
            raise InvocationError('unsupported_backend')
        if resume:
            raise InvocationError('verified_resume_disabled')
        if (isinstance(timeout_seconds,bool) or not isinstance(timeout_seconds,(int,float)) or
                not math.isfinite(timeout_seconds) or not 0 < timeout_seconds <= 60):
            raise InvocationError('invalid_timeout')
        mode, fields = validate_request(wire)
        manifest = read_installation(installation, expected_sha256)
        env = os.environ.copy()
        env['LEAN_PATH'] = os.pathsep.join(manifest['lean_path'])
        env['LEAN_NUM_THREADS'] = '1'
        if manifest['schema']==2:
            command=[manifest['native_executable'],wire.decode('ascii')]
        else:
            command = [manifest['lean'],'-j','1','--run',manifest['entrypoint'],wire.decode('ascii')]
        try:
            cp = subprocess.run(command, cwd=Path(manifest['entrypoint']).parent,
                                env=env, capture_output=True, timeout=timeout_seconds,
                                shell=False)
        except subprocess.TimeoutExpired as exc:
            raise InvocationError('checker_timeout', evidence={
                'stdout_hex':(exc.stdout or b'').hex(),'stderr_hex':(exc.stderr or b'').hex()}) from exc
        except OSError as exc:
            raise InvocationError('checker_launch_failure', str(exc)) from exc
        evidence.update({'exit_code':cp.returncode,'stdout_hex':cp.stdout.hex(),
                         'stderr_hex':cp.stderr.hex(),'command':command})
        passed = parse_response(mode, cp.stdout, cp.stderr, cp.returncode)
        verify_artifacts(manifest)
        # Detect manifest replacement as well as checker changes during execution.
        try:
            final_manifest = Path(installation).read_bytes()
        except OSError as exc:
            raise InvocationError('installation_changed', str(exc)) from exc
        if sha256(final_manifest) != expected_sha256:
            raise InvocationError('installation_changed')
        evidence.update({'status':'completed','assurance':ASSURANCE,'mode':mode,
                         'execution':'native' if manifest['schema']==2 else 'lean_interpreter',
                         'fields':fields,'predicate_passed':passed,
                         'scientific_rejection_authorized':False,
                         'ideal_randomness_claim':False,'tv_assurance_authorized':False,
                         'graph_degree_provenance_checked':False})
    except InvocationError as exc:
        evidence.update(exc.evidence)
        evidence.update({'status':'blocked','error':exc.code,'detail':exc.detail,
                         'assurance':None,'scientific_rejection_authorized':False})
    except (OSError, ValueError, TypeError, KeyError) as exc:
        evidence.update({'status':'blocked','error':'invocation_boundary_failure',
                         'detail':type(exc).__name__+': '+str(exc),
                         'assurance':None,'scientific_rejection_authorized':False})
    evidence['seconds'] = time.monotonic()-start
    return evidence
