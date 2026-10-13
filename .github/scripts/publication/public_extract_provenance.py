"""Pure publication provenance/README transformations; no writes, builds or Git commands.

Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Apache-2.0. Authors: Naganori Yamaguchi (assisted by OpenAI Codex).

Use canonical files at the exact source commit and the selected Lean path set.
Upstream license/NOTICE/ATTRIBUTION bytes are kept intact when relevant; local
indexes and source manifests describe only this extract. Source headers are never
changed. This module is deliberately independent of the module-closure algorithm.
"""
from __future__ import annotations

from copy import deepcopy
import hashlib
import json
import posixpath
import re
from urllib.parse import unquote, urlsplit

PI1 = 'Nyll/EtaleFundamentalGroups/Pi1/'
ANTHROPIC = 'https://github.com/anthropics/fermats-last-theorem/'
ANTHROPIC_REV = 'aa2d8b34692b16c70f699536de0d8e75b9a3e9ef'
SHA = re.compile(r'[0-9a-f]{40}')
FAMILIES = ('SchemeTheory', 'AlgebraicCurves', 'JacobianVarieties')
METADATA_NAMES = ('LICENSE', 'README.md', 'ATTRIBUTION.md', 'UPSTREAM.json')


def require(test, message):
    if not test:
        raise ValueError(message)


def encoded(text):
    return (text.rstrip() + '\n').encode('utf-8')


def header(data):
    text = data.decode('utf-8')
    match = re.match(r'\s*/-(?!!)(.*?)\-/', text, flags=re.S)
    require(match is not None, 'Missing source attribution header')
    return match.group(1).strip()


def urls(text):
    return sorted(set(re.findall(r'https?://[^\s<>\)\]]+', text)))


def selected_records(files, selected_paths):
    selected = sorted(p for p in selected_paths if p.endswith('.lean'))
    require(all(p in files for p in selected), 'Selected source missing from canonical snapshot')
    manifest = json.loads(files[PI1 + 'UPSTREAM.json'])
    indexed = {r['path']: r for r in manifest['local_source_snapshot']['files']}
    pi1, anthropic, other = [], {}, []
    for path in selected:
        notice = header(files[path])
        source_urls = urls(notice)
        base = {'path': path, 'header': notice, 'source_urls': source_urls,
                'sha256': hashlib.sha256(files[path]).hexdigest(),
                'byte_count': len(files[path])}
        if path in indexed and indexed[path]['role'] != 'aggregate':
            entry = deepcopy(indexed[path])
            entry['canonical_record_sha256'] = entry.get('sha256')
            entry.update(base)
            pi1.append(entry)
        elif any('github.com/chrisflav/pi1/' in u for u in source_urls):
            raise ValueError('pi1 source absent from reviewed manifest: ' + path)
        if any(u.startswith(ANTHROPIC) for u in source_urls):
            owner = path.split('/')[1]
            revisions = re.findall(re.escape(ANTHROPIC) + r'blob/([0-9a-f]{40})/', notice)
            require(revisions and set(revisions) == {ANTHROPIC_REV},
                    'Anthropic revision requires a new upstream-notice audit: ' + path)
            base['upstream_sources'] = [u for u in source_urls
                                        if u.startswith(ANTHROPIC) and urlsplit(u).path.endswith('.lean')]
            if base['upstream_sources']:
                base['attribution_kind'] = 'exact_source'
            elif 'source material is identified by code comparison' in notice:
                base['attribution_kind'] = 'identified_source_unresolved'
            elif 'no direct Anthropic source-file match is established' in notice:
                # A library-wide historical remark is not evidence this file was copied.
                # The unchanged source header retains that context and its links.
                continue
            else:
                raise ValueError('Unclassified Anthropic attribution header: ' + path)
            anthropic.setdefault(owner, []).append(base)
        elif path not in indexed:
            credit_lines = [line for line in notice.splitlines()
                            if re.search(r'Copyright|^Authors?:', line) and 'http' not in line]
            if any('Naganori Yamaguchi' not in line for line in credit_lines):
                other.append(base)
    return manifest, pi1, anthropic, other


def managed_provenance_paths(files):
    """Only these exact metadata paths may be removed if absent from the new result."""
    candidates = {PI1 + n for n in METADATA_NAMES} | {'NOTICE'}
    families = set(FAMILIES) | {p.split('/')[1] for p in files if p.startswith('Nyll/') and len(p.split('/')) > 2}
    candidates.update(f'Nyll/{f}/ANTHROPIC_FLT_{n}' for f in families
                      for n in ('SOURCE.md', 'NOTICE', 'ATTRIBUTION.md'))
    return candidates


def source_link(path, base):
    return posixpath.relpath(path, base.rstrip('/'))


def provenance_files(files, selected_paths, source_sha=None):
    """Return exact retained/generated attribution documents, never Lean sources."""
    require(source_sha is None or SHA.fullmatch(source_sha), 'Invalid canonical source SHA')
    manifest, pi1, anthropic, other = selected_records(files, selected_paths)
    result = {}
    notice = ['COPYRIGHT AND THIRD-PARTY NOTICES', '',
              'Apache License, Version 2.0. See LICENSE.',
              'The following notices apply only to the Lean files included in this extract.',
              'Source-specific copyright and author notices remain in those files.', '']
    if pi1:
        license_path = PI1 + 'LICENSE'
        result[license_path] = files[license_path]
        require(hashlib.sha256(result[license_path]).hexdigest() == manifest['license']['sha256'],
                'pi1 upstream license does not match its reviewed manifest')
        upstream = manifest['upstream']
        revision = upstream['comparison_commit']
        preamble = [
            '# pi1 attribution for this extract', '',
            f'Upstream: [chrisflav/pi1]({upstream["repository"]}); Apache-2.0.',
            f'Comparison revision: `{revision}`. [Upstream license](LICENSE).',
            'The exact commit historically copied into NYLL remains unverified; the',
            'comparison revision is not asserted to be the original import revision.',
            'Missing upstream copyright notices do not establish a copyright holder.',
            'The entries below retain the current source headers and distinguish local',
            'NYLL extensions from adapted upstream ports. Only included files are listed.', '']
        attribution = list(preamble)
        for entry in pi1:
            path = entry['path']
            attribution += [f'## [{path}]({source_link(path, PI1)})', '',
                            f'Role: `{entry["role"]}`.', '',
                            entry.get('local_change_description', ''), '',
                            '```text', entry['header'], '```', '']
            for upstream_path in entry['upstream_paths']:
                attribution += [f'- [Upstream `{upstream_path}`]'
                    f'({upstream["repository"]}/blob/{revision}/{upstream_path})']
            attribution.append('')
        result[PI1 + 'ATTRIBUTION.md'] = encoded('\n'.join(attribution))
        result[PI1 + 'README.md'] = encoded('\n'.join([
            '# pi1 adaptations included in this extract', '',
            f'{len(pi1)} adapted or related NYLL source files are recorded in',
            '[ATTRIBUTION.md](ATTRIBUTION.md) and [UPSTREAM.json](UPSTREAM.json).',
            '[LICENSE](LICENSE) retains the exact upstream Apache-2.0 license.',
            'The source files retain their original copyright and author notices.',
            'The recorded upstream revision is a comparison pin; the original import',
            'commit remains unverified. This inventory is not a build certificate.']))
        extract = {'schema': 'nyll.pi1.provenance.public-extract.v1',
            'description': 'Included source evidence only; not a build-success certificate.',
            'upstream': {k: deepcopy(upstream[k]) for k in (
                'repository', 'comparison_commit', 'original_import_commit',
                'original_import_commit_status')},
            'license': deepcopy(manifest['license']),
            'attribution_policy': deepcopy(manifest.get('attribution_policy')),
            'local_source_snapshot': {'hash_algorithm': 'SHA-256 over raw bytes', 'files': pi1}}
        included = {r['path'] for r in pi1}
        mappings = []
        for record in manifest['original_to_current_mappings']:
            destinations = [d for d in record['destinations'] if d['path'] in included]
            if destinations:
                record = deepcopy(record)
                record['destinations'] = destinations
                mappings.append(record)
        extract['original_to_current_mappings'] = mappings
        result[PI1 + 'UPSTREAM.json'] = encoded(json.dumps(extract, indent=2, ensure_ascii=False))
        notice += ['pi1', '---', '', upstream['repository'],
                   'License: Apache License, Version 2.0.',
                   f'Comparison revision: {revision}. Original import commit unverified.',
                   'Included-file attribution and exact license:',
                   PI1 + 'ATTRIBUTION.md', license_path, '']
        for entry in pi1:
            notice += [entry['path'], f'Role: {entry["role"]}', entry['header'], '']
    for family, records in sorted(anthropic.items()):
        prefix = f'Nyll/{family}/ANTHROPIC_FLT_'
        for suffix in ('NOTICE', 'ATTRIBUTION.md'):
            if prefix + suffix in files:
                result[prefix + suffix] = files[prefix + suffix]
            else:
                # Relocated adaptations retain their source attribution. Where the new
                # owner has no copied notice yet, only reuse identical reviewed copies.
                copies = [files[f'Nyll/{f}/ANTHROPIC_FLT_{suffix}'] for f in FAMILIES
                          if f'Nyll/{f}/ANTHROPIC_FLT_{suffix}' in files]
                require(copies and all(c == copies[0] for c in copies),
                        'Cannot establish matching upstream attribution: ' + prefix + suffix)
                result[prefix + suffix] = copies[0]
        local = ['# Anthropic FLT sources included in this extract', '',
            '[ANTHROPIC_FLT_NOTICE](ANTHROPIC_FLT_NOTICE) and',
            '[ANTHROPIC_FLT_ATTRIBUTION.md](ANTHROPIC_FLT_ATTRIBUTION.md) preserve',
            'the upstream documents byte-for-byte, including earlier FLT and Mathlib',
            'credits. References to “this repository” in those copies mean the upstream',
            'repository, not this extract. The included local source files are listed below.', '',
            '| Included source | Upstream attribution |', '| --- | --- |']
        for entry in records:
            path = entry['path']
            local.append(f'| [{path}]({source_link(path, "Nyll/" + family)}) | ' +
                         ('<br>'.join(f'[{u.rsplit("/", 1)[-1]}]({u})'
                                     for u in entry['upstream_sources']) if entry['upstream_sources']
                          else 'Source identified by code comparison; exact upstream file unresolved.') + ' |')
        result[prefix + 'SOURCE.md'] = encoded('\n'.join(local))
        notice += ['Anthropic FLT: ' + family, '-' * (15 + len(family)), '',
                   'Copyright 2026 Anthropic, PBC.', 'License: Apache License, Version 2.0.',
                   'Included-file source mapping: ' + prefix + 'SOURCE.md',
                   'Preserved upstream NOTICE: ' + prefix + 'NOTICE',
                   'Preserved earlier-source attribution: ' + prefix + 'ATTRIBUTION.md',
                   'Earlier copyright holders and authors are not replaced by Anthropic.', '']
        notice += [r['path'] for r in records] + ['']
    if other:
        notice += ['Additional source-specific credits', '----------------------------------', '']
        for entry in other:
            notice += [entry['path'], entry['header'], '']
    if pi1 or anthropic or other:
        result['NOTICE'] = encoded('\n'.join(notice))
    return result


def managed_block(text, name, content, bootstrap=None):
    """Update one explicit generated region; preserve all text outside that region."""
    begin, end = '<!-- nyll-publication:' + name + ':begin -->', '<!-- nyll-publication:' + name + ':end -->'
    block = begin + '\n' + content.strip() + '\n' + end
    require(text.count(begin) == text.count(end) <= 1, 'Malformed managed block: ' + name)
    if begin in text:
        return re.sub(re.escape(begin) + r'.*?' + re.escape(end), lambda _: block, text, flags=re.S)
    require(bootstrap is not None, 'Missing managed block: ' + name)
    return bootstrap(text, block)



def branched_coverings_readme(text, files, selected_paths):
    """Publish reviewed paper endpoints only when their actual sources are selected."""
    prefix = 'Nyll/ShimizuYamaguchi26BranchedCoverings/'
    normal = prefix + 'Theorem2Dot3NormalCrossings.lean'
    multiplicity = prefix + 'Theorem2Dot3SpecialFiberMultiplicity.lean'
    quotient = prefix + 'Geometry/PadicNormalCrossingsQuotient.lean'
    example = prefix + 'Geometry/SquareTripleNormalCrossings.lean'
    complement = prefix + 'Geometry/RationalSectionComplementGeometry.lean'
    def included(path):
        return path in selected_paths and path in files
    nc, length, quadratic, triple = map(included, (normal, multiplicity, quotient, example))
    geometry = all(included(path) for path in (complement,
        'Nyll/SchemeTheory/ProjectiveSpace/Smooth.lean',
        'Nyll/SchemeTheory/ProjectiveSpace/GenericPoint.lean'))
    if not any((nc, length, quadratic, triple, geometry)):
        return text
    title = 'Branched coverings of the projective line over the integers'
    section = re.search(r'^### ' + re.escape(title) + r'\n(.*?)(?=^#{2,3} |\Z)',
                        text, flags=re.M | re.S)
    require(section is not None, 'Missing reviewed branched-coverings results section')
    rows = [line for line in section.group(1).splitlines() if line.startswith('| [')]
    def row(label):
        matches = [line for line in rows if line.startswith('| [' + label)]
        require(len(matches) == 1, 'Expected one reviewed paper result row: ' + label)
        return matches[0]
    lemma = row('Lemma 2.3')
    if nc:
        links = f'[Lemma 2.3: normal crossings]({normal})'
        content = ('The finite rational-section divisor has ordinary normal crossings over `Z_p` '
                   'exactly under the original special-fibre conditions.')
        if length:
            links += f'; [intersection multiplicity]({multiplicity})'
            content += ' The local intersection length is the determinant valuation.'
        lemma = f'| {links} | {content} |'
    elif length:
        lemma = (f'| [Lemma 2.3: intersection multiplicity]({multiplicity}) | '
                 'At any point of the original prime special fibre on a section, '
                 'the local intersection length is the determinant valuation. |')
    prop = row('Proposition 2.5')
    if quadratic:
        prop = (f'| [Proposition 2.5]({quotient}) | Failure of ordinary normal crossings '
                'over `Z_2` gives a continuous quotient of the original complement\'s '
                'etale fundamental group onto the cyclic group of order two, '
                'at every geometric base point. |')
    table = ['| Result | Mathematical content |', '| --- | --- |']
    if geometry:
        table.append(f'| [Observation 2.1: complement geometry]({complement}) | '
                     'The complement of finitely many rational sections is smooth over '
                     '`Spec Z` and has geometrically connected fibres. |')
    table += [lemma, row('Lemma 2.4'), prop, row('Corollary 2.7')]
    if triple:
        table.append(f'| [Example 2.8: geometry]({example}) | The boundary '
                     '`{0, p^2, infinity}` has ordinary normal crossings exactly away '
                     'from `p`. Fundamental-group triviality remains unfinished. |')
    def initial_results(text, block):
        pattern = r'(^### ' + re.escape(title) + r'\n).*?(?=^#{2,3} |\Z)'
        updated, count = re.subn(pattern, lambda m: m.group(1) + '\n' + block + '\n\n',
                                text, flags=re.M | re.S)
        require(count == 1, 'Expected one branched-coverings results section')
        return updated
    text = managed_block(text, 'branched-coverings-results', '\n'.join(table), initial_results)
    remaining = []
    if not nc:
        remaining.append('The full finite-divisor normal-crossing criterion over `Z_p` '
                         'is not yet included in this extract.')
    if not geometry:
        remaining.append('Observation 2.1\'s smoothness and geometric connectedness '
                         'are not yet included in this extract.')
    remaining.append('The geometric inertia inputs and the main solvable-quotient criterion '
                     'of Theorem 2.6 remain incomplete.')
    # The partial-example row already states its precise missing assertion.
    if not triple:
        remaining.append('The fundamental-group triviality in Example 2.8 remains unfinished.')
    def initial_remaining(text, block):
        pattern = (r'(^\*\*' + re.escape(title) + r'\*\*\n).*?'
                   r'(?=^\*\*[^*\n]+\*\*\n|^## |\Z)')
        updated, count = re.subn(pattern, lambda m: m.group(1) + '\n' + block + '\n\n',
                                text, flags=re.M | re.S)
        require(count == 1, 'Expected one branched-coverings remaining-work paragraph')
        return updated
    return managed_block(text, 'branched-coverings-remaining', '\n'.join(remaining),
                         initial_remaining)


def readme_for_extract(text, files, selected_paths, primary, source_sha=None):
    """Preserve prose outside reviewed distribution, credit and paper-status blocks.

    The first migration replaces the known legacy distribution sentence and the
    license-section body. Later runs replace only those explicit generated blocks.
    No commit SHA is embedded: unchanged selected source gives unchanged prose.
    """
    require(source_sha is None or SHA.fullmatch(source_sha), 'Invalid canonical source SHA')
    _, pi1, anthropic, other = selected_records(files, selected_paths)
    text = text.replace('\r\n', '\n')
    distribution = ('Only the module-level import closure of ' +
        ', '.join(f'`Nyll.{f}.All`' for f in primary) +
        ' is bundled. Dependencies retain their canonical `Nyll` imports.')
    def initial_distribution(text, block):
        old = 'Bundled dependencies use the same `Nyll` imports as the complete library.'
        if text.count(old) == 1:
            return text.replace(old, block)
        anchor = 'from [NYLL](https://github.com/n-yamaguchi-0729/NYLL).'
        require(text.count(old) == 0 and text.count(anchor) == 1,
                'Expected known extraction sentence for initial migration')
        return text.replace(anchor, anchor + '\n\n' + block)
    text = managed_block(text, 'distribution', distribution, initial_distribution)
    license_lines = ['Apache License 2.0. See [LICENSE](LICENSE).']
    credits = []
    if pi1:
        credits.append('[pi1](https://github.com/chrisflav/pi1)')
    if anthropic:
        credits.append("[Anthropic’s Fermat’s Last Theorem project](https://github.com/anthropics/fermats-last-theorem)")
    if credits:
        license_lines += ['', 'Included adaptations from ' + ' and '.join(credits) +
                          ' retain their source-specific copyrights and authors.',
                          'The included-file inventories and preserved upstream notices are in [NOTICE](NOTICE).']
    elif other:
        license_lines += ['', 'Additional source-specific credits are preserved in [NOTICE](NOTICE).']
    def initial_license(text, block):
        text, count = re.subn(r'(^## License(?: and acknowledgements)?\n).*?(?=^## |\Z)',
            lambda m: m.group(1) + '\n' + block + '\n', text, flags=re.M | re.S)
        require(count == 1, 'Expected exactly one README license section')
        return text
    text = managed_block(text, 'credits', '\n'.join(license_lines), initial_license)
    def fix_all(match):
        path = match.group(1)
        if path in selected_paths:
            return match.group(0)
        directory = path[:-len('All.lean')]
        require(any(p.startswith(directory) for p in selected_paths),
                'README references a removed dependency: ' + path)
        return '](' + directory + ')'
    text = re.sub(r'\]\((Nyll/[^)]+/All\.lean)\)', fix_all, text)
    if 'ShimizuYamaguchi26BranchedCoverings' in primary:
        text = branched_coverings_readme(text, files, selected_paths)
    return encoded(text)


def sawin_verification_readme(text):
    """Remove obsolete expanded-extract counts without changing historical evidence."""
    text = text.replace('\r\n', '\n')
    text = text.replace('`source-manifest.json`: the exact SHA-pinned 4,141-module closure.',
                        '`source-manifest.json`: the exact SHA-pinned module closure listed in `moduleRows`.')
    old = ('- `historical-partial-baseline.json`: 31 pre-existing compiler-generated recursion declarations\n'
           '  and their exact source, copyright-header, and body hashes. Seven belonged to\n'
           '  the previous extract; the expanded dependency families contribute another\n'
           '  eleven from ProCGroups and thirteen from SchemeTheory. The baseline records\n'
           '  each declaration and the immutable source commit used for the compiler audit.')
    new = ('- `historical-partial-baseline.json`: the pre-existing compiler-generated recursion\n'
           '  declarations in the current import closure, with exact source, copyright-header,\n'
           '  and body hashes. The original compiler-audit commits are retained as historical\n'
           '  evidence; the baseline membership matches the current source manifest.')
    return encoded(text.replace(old, new))


def local_markdown_links(document_path, data, available_paths):
    """Report broken relative Markdown paths; root/external/anchor URLs are distinguished."""
    missing = []
    for target in re.findall(r'\]\(([^\s)]+)(?:\s+"[^"]*")?\)', data.decode('utf-8')):
        parsed = urlsplit(target.strip('<>'))
        if parsed.scheme or parsed.netloc or not parsed.path:
            continue
        rel = unquote(parsed.path)
        path = posixpath.normpath(posixpath.join(posixpath.dirname(document_path), rel))
        if path in available_paths or any(p.startswith(path.rstrip('/') + '/') for p in available_paths):
            continue
        missing.append({'document': document_path, 'target': target, 'resolved': path})
    return missing
