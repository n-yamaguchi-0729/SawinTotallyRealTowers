#!/usr/bin/env python3
"""Run the shared physical-source and exact public-root policy audit.

Copyright 2026 Naganori Yamaguchi.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
This lexical audit is not an independent proof checker.
"""
from pathlib import Path
import json
import sys
import generate_manifest as gm

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
config = gm.load_json(HERE / 'manifest-config.json')
manifest, report = gm.analyze(ROOT, config)
out = ROOT / 'tmp/ci-libraries'
out.mkdir(parents=True, exist_ok=True)
(out / 'source-audit.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'staticPassed': report['staticPassed'], 'moduleCount': report['moduleCount'],
                 'errors': report['errors']}, ensure_ascii=False, indent=2))
sys.exit(0 if report['staticPassed'] else 1)
