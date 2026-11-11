#!/usr/bin/env python3
"""Render legacy verification callers while preserving their proof checks.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
"""
from __future__ import annotations
import re


def legacy_workflow(existing, libraries):
    """Replace only build jobs; retain each repository's audited verification tail."""
    prefix, separator, body = existing.partition("jobs:\n")
    if not separator or "\n  verify:\n" not in body:
        raise ValueError("Missing legacy workflow build/verify boundary")
    verify = "  verify:\n" + body.split("\n  verify:\n", 1)[1]
    verify = verify.split("\n  publish-cache:\n", 1)[0].rstrip() + "\n"
    selectors = list(libraries) + ["EntryPoint"]
    if len(selectors) < 2 or len(selectors) != len(set(selectors)):
        raise ValueError("Expected unique library selectors")
    jobs = []
    ids = []
    for selector in selectors:
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9]*(?:\.[A-Za-z][A-Za-z0-9]*)*", selector):
            raise ValueError("Invalid library selector")
        job = "library-" + selector.replace(".", "-").lower()
        if job in ids:
            raise ValueError("Library job identifier collision")
        block = f"  {job}:\n    name: {selector}\n"
        block += "    if: github.event.repository.private == false\n"
        if ids:
            block += f"    needs: {ids[-1]}\n"
        block += "    uses: ./.github/workflows/build-library.yml\n    with:\n"
        block += f"      library: {selector}\n"
        jobs.append(block)
        ids.append(job)
    verify, count = re.subn(r"(?m)^    needs:.*$", "    needs: [" + ", ".join(ids) + "]", verify, count=1)
    if count != 1:
        raise ValueError("Missing legacy verification build dependency")
    publish = """
  publish-cache:
    name: Publish verified proof cache
    needs: verify
    if: github.event.repository.private == false && github.ref == 'refs/heads/main' && github.event_name != 'pull_request'
    permissions:
      contents: write
    uses: ./.github/workflows/cache-release.yml
    with:
      cache-kind: legacy
"""
    return prefix + separator + "\n".join(jobs) + "\n" + verify + publish
