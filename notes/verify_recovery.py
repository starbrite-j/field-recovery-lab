"""Build and check the local recovery proofs with the repository toolchain.

Run from any directory:
    python3 /Users/jj/NavierStokesAndEuler/notes/verify_recovery.py

Prerequisites: elan's pinned toolchain, locked dependencies, and Mathlib cache
are already installed. This script performs no package installation or update,
and leaves tracked source/configuration files alone. It compiles notes modules
outside the repository's default library targets in their dependency order.
Logs and a machine-readable report are written under notes/verification/.
The report distinguishes exact source-family core/calibration recovery from
practical numerical observation recovery. CoreFieldRecovery removes supplied
core metadata; the older FullFieldRecovery.EOnly marker definitions remain a
separate route with unproved identification hypotheses.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'notes' / 'verification'
MODULES = ['AxialFromAngular', 'ProfileReverseTrace', 'FullFieldRecovery',
           'SourceFieldRecovery', 'ObservedFieldRecovery', 'CoreFieldRecovery',
           'OriginalFieldReproduction', 'PrefixSampleCertificate', 'RecoveryAxiomAudit']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_report(report: dict) -> None:
    (OUTPUT / 'proof_verification.json').write_text(json.dumps(report, indent=2) + '\n')


def run_step(report: dict, label: str, command: list[str]) -> str:
    log_path = OUTPUT / f'{label}.log'
    print(f'[{label}] {" ".join(command)}', flush=True)
    started = time.monotonic()
    env = os.environ.copy()
    env.setdefault('LEAN_NUM_THREADS', '4')
    lines = []
    with log_path.open('w') as log:
        process = subprocess.Popen(command, cwd=ROOT, env=env,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, bufsize=1)
        assert process.stdout is not None
        for line in process.stdout:
            log.write(line)
            log.flush()
            lines.append(line)
            print(line, end='', flush=True)
        code = process.wait()
    result = {
        'label': label,
        'command': command,
        'exit_code': code,
        'seconds': round(time.monotonic() - started, 3),
        'log': str(log_path.relative_to(ROOT)),
    }
    report['steps'].append(result)
    write_report(report)
    if code:
        raise RuntimeError(f'{label} exited {code}; see {log_path}')
    return ''.join(lines)


def main() -> int:
    OUTPUT.mkdir(parents=True, exist_ok=True)
    olean_dir = ROOT / '.lake' / 'build' / 'lib' / 'lean' / 'notes'
    olean_dir.mkdir(parents=True, exist_ok=True)
    report = {
        'status': 'running',
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'lake_manifest_sha256': digest(ROOT / 'lake-manifest.json'),
        'proof_files_sha256': {f'notes/{name}.lean': digest(ROOT / 'notes' / f'{name}.lean') for name in MODULES},
        'calibration_identification_formally_proved': False,
        'calibration_identification_from_E_alone_formally_proved': False,
        'calibration_identification_with_retained_core_formally_proved': False,
        'core_identification_from_assembled_E_formally_proved': False,
        'legacy_EOnly_marker_identification_formally_proved': False,
        'actual_observed_E_dataset_recovered': False,
        'full_symbolic_original_reproduction_proved': False,
        'full_numerical_original_reproduced': False,
        'exact_normalized_prefix_samples_verified': 0,
        'steps': [],
    }
    write_report(report)
    try:
        locked_dependencies = []
        for package in json.loads((ROOT / 'lake-manifest.json').read_text())['packages']:
            actual = subprocess.check_output(
                ['git', '-C', str(ROOT / '.lake' / 'packages' / package['name']), 'rev-parse', 'HEAD'],
                text=True,
            ).strip()
            locked_dependencies.append({'name': package['name'], 'locked_revision': package['rev'],
                                        'actual_revision': actual, 'matches_lock': actual == package['rev']})
        report['dependencies'] = locked_dependencies
        if not all(package['matches_lock'] for package in locked_dependencies):
            raise RuntimeError('An installed dependency differs from its pinned revision.')
        run_step(report, 'prefix_export_consistency', [
            sys.executable, 'notes/reproduce_original_prefix.py', '--check',
        ])
        report['prefix_export_sha256'] = digest(ROOT / 'notes/original_field/prefix_samples.json')
        report['prefix_generator_sha256'] = digest(ROOT / 'notes/reproduce_original_prefix.py')
        run_step(report, 'lean_version', ['lean', '--version'])
        run_step(report, 'lake_version', ['lake', '--version'])
        run_step(report, 'source_dependencies', [
            'lake', '--no-cache', 'build', '+NavierStokes.ExtendedHeatedOutgoing:olean',
            '+NavierStokes.HeatSwitchHistoryDerivatives:olean', '+NavierStokes.PreparedOutgoing:olean',
        ])
        for name in MODULES:
            run_step(report, name, [
                'lake', 'env', 'lean', '-o', str(olean_dir / f'{name}.olean'),
                '-i', str(olean_dir / f'{name}.ilean'), f'notes/{name}.lean',
            ])
        audit_text = (OUTPUT / 'RecoveryAxiomAudit.log').read_text()
        blocks = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', audit_text)
        if len(blocks) != 45:
            raise RuntimeError(f'Expected forty-five axiom reports; found {len(blocks)}. Inspect the saved audit.')
        used = {part.strip() for block in blocks for part in block.split(',') if part.strip()}
        report['audited_theorems'] = len(blocks)
        report['axioms_used'] = sorted(used)
        report['unexpected_axioms'] = sorted(used - ALLOWED_AXIOMS)
        if report['unexpected_axioms']:
            raise RuntimeError(f'Unexpected proof dependencies: {report["unexpected_axioms"]}')
        if report['lake_manifest_sha256'] != digest(ROOT / 'lake-manifest.json'):
            raise RuntimeError('The dependency lock changed during verification.')
        for relative, expected in report['proof_files_sha256'].items():
            if digest(ROOT / relative) != expected:
                raise RuntimeError(f'A proof changed during verification: {relative}')
        if (digest(ROOT / 'notes/original_field/prefix_samples.json') != report['prefix_export_sha256']
                or digest(ROOT / 'notes/reproduce_original_prefix.py') != report['prefix_generator_sha256']):
            raise RuntimeError('The prefix exporter or its data changed during verification.')
        report['status'] = 'passed'
        report['compiled_modules'] = MODULES
        report['legacy_readers_require_supplied_calibration'] = True
        report['assembled_reader_requires_supplied_calibration'] = False
        report['assembled_reader_requires_retained_core'] = False
        report['calibration_identification_with_retained_core_formally_proved'] = True
        report['calibration_identification_formally_proved'] = True
        report['calibration_identification_from_E_alone_formally_proved'] = True
        report['core_identification_from_assembled_E_formally_proved'] = True
        report['calibration_identification_scope'] = 'CoreFieldRecovery: complete exact assembled E in the NominalProfile source family. Observable endpoint, rate, patch, scale, ramp, P, m, wait markers recover the core; the boundary tail supplies h and completes calibration. No supplied core or calibration. Legacy FullFieldRecovery.EOnly markers remain unproved.'
        report['finite_noisy_observation_recovery_proved'] = False
        report['source_profile_identified'] = 'PreparedOutgoing.prepared.profile'
        report['assembled_outgoing_prefix_completion_proved'] = True
        report['matching_source_instance_recovery_proved'] = True
        report['full_symbolic_original_reproduction_proved'] = True
        report['symbolic_observation_constructed_from_same_source'] = True
        report['exact_normalized_prefix_samples_verified'] = 45
        report['prefix_sample_scope'] = '0 < x <= 1, eta in [-1,1]; exact U and E/P, with source amplitude P unassigned. All samples checked against the symbolic reproduced original by Lean.'
        report['later_assembled_U_agreement_region'] = 'X > heatJoin, eta in [-1,1]'
    except (OSError, RuntimeError, subprocess.CalledProcessError) as error:
        report['status'] = 'failed'
        report['error'] = str(error)
        print(str(error), file=sys.stderr, flush=True)
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        write_report(report)
        archive = OUTPUT / 'runs' / report['started_utc'].replace(':', '-')
        archive.mkdir(parents=True, exist_ok=True)
        shutil.copy2(OUTPUT / 'proof_verification.json', archive / 'proof_verification.json')
        for step in report['steps']:
            path = ROOT / step['log']
            if path.is_file():
                shutil.copy2(path, archive / path.name)
    print(f'Verification {report["status"]}: {OUTPUT / "proof_verification.json"}', flush=True)
    return 0 if report['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
