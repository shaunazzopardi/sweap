import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

import pytest


@pytest.mark.parametrize('wrapper_name', ['strix_tlsf_file.sh', 'strix_tlsf.sh'])
def test_strix_wrapper_uses_bundled_converter(wrapper_name, tmp_path):
    """An older syfco on PATH must not replace the bundled, fixed converter."""
    binary_dir = tmp_path / 'bundled'
    foreign_dir = tmp_path / 'foreign'
    binary_dir.mkdir()
    foreign_dir.mkdir()
    wrapper = binary_dir / wrapper_name
    shutil.copy2(Path(__file__).resolve().parents[2] / 'binaries' / wrapper_name, wrapper)

    syfco = binary_dir / 'syfco'
    syfco.write_text(
        f'#!{sys.executable}\n'
        'import json, os, pathlib, sys\n'
        'args = sys.argv[1:]\n'
        'with open(os.environ["SYFCO_TRACE"], "a") as trace:\n'
        '    trace.write(json.dumps(args) + "\\n")\n'
        'if "--print-input-signals" in args: print("i")\n'
        'elif "--print-output-signals" in args: print("o")\n'
        'elif "-o" in args:\n'
        '    pathlib.Path(args[args.index("-o") + 1]).write_text("X(o)")\n'
        'else: print("X(o)")\n'
    )
    foreign_syfco = foreign_dir / 'syfco'
    foreign_syfco.write_text(
        '#!/bin/sh\necho "Unexpected syfco from PATH" >&2\nexit 99\n'
    )
    strix = foreign_dir / 'strix'
    strix.write_text(
        f'#!{sys.executable}\n'
        'import json, os, pathlib, sys\n'
        'args = sys.argv[1:]\n'
        'option = "--formula-file" if "--formula-file" in args else "-F"\n'
        'formula = pathlib.Path(args[args.index(option) + 1]).read_text().strip()\n'
        'pathlib.Path(os.environ["STRIX_TRACE"]).write_text(json.dumps('
        '{"args": args, "formula": formula}))\n'
        'print("REALIZABLE")\n'
    )
    for executable in (syfco, foreign_syfco, strix):
        executable.chmod(0o755)

    source = tmp_path / 'input.tlsf'
    source.write_text('Test input; the fake converter records its invocation.')
    syfco_trace = tmp_path / 'syfco.jsonl'
    strix_trace = tmp_path / 'strix.json'
    result = subprocess.run(
        [str(wrapper), str(source), '-m', 'both', '--onthefly', 'none'],
        cwd=tmp_path,
        env={
            **os.environ,
            'PATH': str(foreign_dir) + os.pathsep + os.environ['PATH'],
            'SYFCO_TRACE': str(syfco_trace),
            'STRIX_TRACE': str(strix_trace),
        },
        text=True,
        capture_output=True,
        check=True,
    )

    assert result.stdout.strip() == 'REALIZABLE'
    assert result.stderr == ''
    calls = [json.loads(line) for line in syfco_trace.read_text().splitlines()]
    assert len(calls) == 3
    assert calls[:2] == [
        ['-f', 'ltl', '--print-input-signals', str(source)],
        ['-f', 'ltl', '--print-output-signals', str(source)],
    ]
    assert calls[2][:7] == ['-f', 'ltl', '-q', 'double', '-m', 'fully', str(source)]
    solver = json.loads(strix_trace.read_text())
    assert solver['formula'] == 'X(o)'
    assert solver['args'][:4] == ['--ins', 'i', '--outs', 'o']
    assert solver['args'][-4:] == ['-m', 'both', '--onthefly', 'none']
