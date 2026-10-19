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


def header(data, path=None):
    text = data.decode('utf-8')
    match = re.match(r'\s*/-(?!!)(.*?)\-/', text, flags=re.S)
    require(match is not None, 'Missing source attribution header' + (': ' + path if path else ''))
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
        notice = header(files[path], path)
        normalized_notice = ' '.join(notice.split())
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
            elif ('source material is identified by code comparison' in normalized_notice
                    or ('Anthropic FLT material was identified by code comparison' in normalized_notice
                        and 'exact source-file correspondence remains unresolved' in normalized_notice)):
                base['attribution_kind'] = 'identified_source_unresolved'
            elif ('no direct Anthropic source-file match is established' in normalized_notice
                    or 'no established direct Anthropic source-file match' in normalized_notice):
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


def readme_lean_link(files, selected_paths, path, declaration):
    """Link a reviewed endpoint only when its declaration is in this extract."""
    require(path in selected_paths and path in files, 'README endpoint is not included: ' + path)
    source = files[path].decode('utf-8')
    pattern = (r'^(?:(?:noncomputable|protected)\s+)?'
               r'(?:def|opaque|theorem|lemma|instance|abbrev|class|structure)\s+'
               + re.escape(declaration) + r'(?=[\s:{(])')
    matches = list(re.finditer(pattern, source, re.M))
    require(len(matches) == 1, 'README declaration is missing or ambiguous: ' + declaration)
    line = source.count('\n', 0, matches[0].start()) + 1
    return f'[`{declaration}`]({path}#L{line})'


def readme_section(text, title, name, content, before=None):
    """Manage a reviewed section body, preserving all other README sections."""
    def bootstrap(text, block):
        heading = '## ' + title + '\n'
        if heading in text:
            pattern = r'^' + re.escape(heading) + r'.*?(?=^## |\Z)'
            updated, count = re.subn(pattern, heading + '\n' + block + '\n\n',
                                     text, flags=re.M | re.S)
            require(count == 1, 'Ambiguous README section: ' + title)
            return updated
        anchor = '## ' + before + '\n' if before else None
        require(anchor is not None and text.count(anchor) == 1,
                'Missing README insertion point: ' + title)
        return text.replace(anchor, heading + '\n' + block + '\n\n' + anchor)
    return managed_block(text, name, content, bootstrap)


# Reviewed legacy README anchors. Names, rather than old line numbers, are the
# stable correspondence; subsequent output computes the current declaration line.
_STACKS_LEGACY_ENDPOINTS = {
    ('Nyll/EtaleFundamentalGroups/GeometricFiber/EtaleOverFieldEquivalence.lean', 1643): 'equivDiscreteContAction',
    ('Nyll/EtaleFundamentalGroups/GeometricFiber/CoveringFamilies.lean', 33): 'ofArrows_mem_smallEtaleTopology_iff_geometricFiber_jointlySurjective',
    ('Nyll/EtaleFundamentalGroups/GaloisCategories/AutomorphismProfiniteCompletion.lean', 459): 'profiniteCompletionEquivAutForget',
    ('Nyll/EtaleFundamentalGroups/GaloisCategories/FiberFunctorUniqueness.lean', 969): 'nonempty_iso_forget_of_exact',
    ('Nyll/EtaleFundamentalGroups/GaloisCategories/FiberFunctorComparison.lean', 73): 'nonempty_iso_comp_of_exact',
    ('Nyll/EtaleFundamentalGroups/GaloisCategories/Surjectivity.lean', 351): 'autHomOfCompIso_surjective_tfae',
    ('Nyll/EtaleFundamentalGroups/GaloisCategories/TrivialComposite.lean', 210): 'autHomOfCompIso_comp_eq_one_iff',
    ('Nyll/EtaleFundamentalGroups/GaloisCategories/ExactSequence.lean', 153): 'autHomOfCompIso_exact_sequence_tfae',
    ('Nyll/EtaleFundamentalGroups/GaloisCategories/Injectivity.lean', 145): 'autHomOfCompIso_injective_iff_exists_epi_mono_span',
    ('Nyll/EtaleFundamentalGroups/GaloisCategories/NormalImage.lean', 140): 'autHomOfCompIso_range_normal_iff_terminal_decomposition',
    ('Nyll/SchemeTheory/Pi1/FiniteEtale/Geometry.lean', 458): 'equivFintypeCat',
    ('Nyll/SchemeTheory/FiniteEtale/Forget/FiniteCoequalizers.lean', 2448): 'forgetPreservesFiniteColimits',
    ('Nyll/EtaleFundamentalGroups/FiniteEtale/InternalHom.lean', 36): 'exists_internalHom',
    ('Nyll/EtaleFundamentalGroups/Pi1/FiniteEtale/GaloisCategory.lean', 148): 'galoisCategory',
    ('Nyll/EtaleFundamentalGroups/GeometricFiber/BasePoint.lean', 38): 'nonempty_fiber_iso',
    ('Nyll/EtaleFundamentalGroups/GeometricFiber/AlgebraicClosure.lean', 146): 'absoluteGaloisEquivFundamentalGroup',
    ('Nyll/EtaleFundamentalGroups/GeometricFiber/PullbackEquivalence.lean', 48): 'fundamentalGroupEquivOfPullbackEquivalence',
    ('Nyll/EtaleFundamentalGroups/FiniteEtale/HenselianPair.lean', 37): 'pullback_isEquivalence_of_henselian',
    ('Nyll/EtaleFundamentalGroups/FiniteEtale/Thickening.lean', 37): 'pullback_isEquivalence_of_surjective_closedImmersion',
    ('Nyll/EtaleFundamentalGroups/FiniteEtale/UniversalHomeomorphism.lean', 89): 'pullback_isEquivalence_of_universalHomeomorphism',
    ('Nyll/EtaleFundamentalGroups/FiniteEtale/DensePullback.lean', 28): 'pullback_faithful_of_denseRange',
    ('Nyll/EtaleFundamentalGroups/Purity/PuncturedStrictStalk.lean', 45): 'puncturedSpectrumPullbackFullyFaithful_of_connected_geometricStalk',
    ('Nyll/EtaleFundamentalGroups/Purity/LocallyConnectedRestriction.lean', 134): 'denseOpenPullbackFullyFaithful_of_noetherianSpace',
    ('Nyll/EtaleFundamentalGroups/Purity/RetrocompactRestriction.lean', 39): 'denseOpenPullbackFullyFaithful_of_retrocompact_closed_complement',
    ('Nyll/EtaleFundamentalGroups/Purity/LocallyConnectedRestriction.lean', 43): 'denseOpenPullbackFullyFaithful_of_finite_components',
    ('Nyll/EtaleFundamentalGroups/GeometricFiber/UnibranchSurjective.lean', 31): 'irreducible_geometricallyUnibranch_fundamentalGroup_surjections',
    ('Nyll/EtaleFundamentalGroups/Normalization/UnramifiedNormalization.lean', 112): 'unramified_normalization_iff_etale_iff_finiteEtale',
    ('Nyll/EtaleFundamentalGroups/Purity/PuncturedSpectrumConnectedRestriction.lean', 230): 'connectedCoverGenericNormalizationDesc_isIso',
    ('Nyll/EtaleFundamentalGroups/Normalization/UnramifiedSubfield.lean', 77): 'mem_genericKernelFixedField_iff_exists_unramified_finite_subfield',
    ('Nyll/EtaleFundamentalGroups/StrictHenselian/NormalLocalExactSequence.lean', 143): 'geometricStalk_normalLocal_exactSequence',
    ('Nyll/EtaleFundamentalGroups/StrictHenselian/SeparablyClosedFractionResidue.lean', 109): 'isAlgClosed_primeResidueField_of_isSepClosed_fractionRing',
    ('Nyll/EtaleFundamentalGroups/StrictHenselian/SeparablyClosedFractionHenselian.lean', 150): 'henselianLocalRing_and_isSepClosed_residueField_of_isSepClosed_fractionRing',
    ('Nyll/EtaleFundamentalGroups/Inertia/InvariantBaseChange.lean', 122): 'inertia_invariantBaseChange',
    ('Nyll/EtaleFundamentalGroups/Inertia/InvariantEtaleNeighborhood.lean', 253): 'inertia_invariants_exists_etale_away',
    ('Nyll/EtaleFundamentalGroups/Inertia/FiniteLevelEtaleColimit.lean', 184): 'finiteLevelEtaleCoconeIsColimit',
    ('Nyll/EtaleFundamentalGroups/StrictHenselian/OriginalLocalHenselizationDiagram.lean', 44): 'originalLocalGaloisDiagram_of_actualHenselizations',
    ('Nyll/EtaleFundamentalGroups/Inertia/GenericKernelStrictNormalGeneration.lean', 165): 'genericAbsoluteGaloisHom_ker_eq_pointInertia_and_chosenStrictGalois',
    ('Nyll/EtaleFundamentalGroups/Normalization/UnramifiedCriteria.lean', 48): 'unramified_normalization_criteria_tfae',
    ('Nyll/EtaleFundamentalGroups/Inertia/NormalizationDVRRamification.lean', 49): 'normalizationDVR_ramification',
    ('Nyll/EtaleFundamentalGroups/Inertia/NormalizationDVRAbsoluteRamification.lean', 40): 'normalizationDVR_absolute_ramification',
    ('Nyll/EtaleFundamentalGroups/FiniteEtale/InverseLimitComparison.lean', 58): 'fundamentalGroupInverseLimitEquiv',
    ('Nyll/EtaleFundamentalGroups/GeometricFiber/Perfection.lean', 61): 'perfection_invariance',
    ('Nyll/EtaleFundamentalGroups/GeometricFiber/ArithmeticAlgebraicClosure.lean', 207): 'arithmetic_exactSequence_of_isAlgClosure',
    ('Nyll/EtaleFundamentalGroups/FiniteEtale/ProperNormalization.lean', 80): 'finite_etale_fromNormalization_of_proper_flat_geometricallyReduced',
    ('Nyll/EtaleFundamentalGroups/GeometricFiber/ProperHomotopyExact.lean', 36): 'fundamentalGroupHom_proper_geometricFiber_ker_eq_range',
    ('Nyll/EtaleFundamentalGroups/FiniteEtale/ConnectedComponentFaithful.lean', 38): 'pullback_faithful_of_meets_connectedComponents',
    ('Nyll/EtaleFundamentalGroups/Purity/PuncturedHypersurfaceFaithful.lean', 49): 'pullback_faithful_punctured_hypersurface_of_minimalPrime_dimension',
    ('Nyll/EtaleFundamentalGroups/Purity/Local/PuncturedCoverExtensionCriterion.lean', 31): 'exists_punctured_finiteEtale_extension_iff_sections_finiteEtale',
    ('Nyll/SchemeTheory/RingTheory/PrimeContainingAtHeightOne.lean', 170): 'exists_prime_containing_ringKrullDim_localization_eq_one',
    ('Nyll/EtaleFundamentalGroups/Purity/LocalToGlobalExtension.lean', 82): 'pullback_essSurj_of_isOpenImmersion_of_hasPuncturedPurity',
    ('Nyll/EtaleFundamentalGroups/Purity/PuncturedHypersurfaceNeighborhoodFaithful.lean', 90): 'pullback_faithful_punctured_hypersurface_neighborhood_of_minimalPrime_dimension',
    ('Nyll/EtaleFundamentalGroups/Purity/PuncturedHypersurfaceNeighborhoodExistence.lean', 106): 'exists_punctured_hypersurface_neighborhood_faithful',
    ('Nyll/EtaleFundamentalGroups/Purity/PuncturedHypersurfaceQuotientGerms.lean', 145): 'restrictionToQuotientPuncture_faithful',
    ('Nyll/EtaleCohomology/Classical/FieldHilbert90.lean', 195): 'etaleMultiplicativeGroup_H1_eq_zero_of_field',
    ('Nyll/EtaleCohomology/Classical/KummerSequence.lean', 141): 'etaleKummerComplex_shortExact',
    ('Nyll/EtaleCohomology/Constructible/FiniteLocallyConstantEquivalence.lean', 51): 'finiteEtaleEquivFiniteLocallyConstantSetSheaf',
    ('Nyll/EtaleCohomology/Sites/Localization.lean', 83): 'openClosedLocalization_shortExact',
    ('Nyll/EtaleCohomology/Sites/ProperHenselianH0.lean', 69): 'etaleClosedFiber_globalSections_bijective',
}


def refresh_stacks_lean_links(text, files, selected_paths):
    """Replace generic Lean labels and stale anchors with reviewed declaration names."""
    moved = 'Nyll/SchemeTheory/RingTheory/PrimeContainingAtHeightOne.lean'
    anonymous = {
        ('Nyll/SchemeTheory/Pi1/FiniteEtale/Basic.lean', 319):
            ('HasTerminal', 'instance : HasTerminal (FiniteEtale X)'),
        ('Nyll/EtaleFundamentalGroups/Pi1/FiniteEtale/GaloisCategory.lean', 160):
            ('π₁ᵉᵗ', 'notation:arg "π₁ᵉᵗ"'),
        ('Nyll/EtaleFundamentalGroups/Pi1/GeometricFiber/FieldPoints.lean', 89):
            ('MulAction', 'instance : MulAction (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma)')}
    def replace(match):
        label, path, old_line = match.groups()
        key = (path, int(old_line))
        if key in anonymous:
            name, pattern = anonymous[key]
            require(path in selected_paths and path in files, 'Missing README source: ' + path)
            source = files[path].decode('utf-8')
            require(source.count(pattern) == 1, 'Missing reviewed instance or notation: ' + name)
            line = source.count('\n', 0, source.index(pattern)) + 1
            return f'[`{name}`]({path}#L{line})'
        name = _STACKS_LEGACY_ENDPOINTS.get(key)
        if name is None and label.startswith('`') and label.endswith('`'):
            name = label[1:-1]
        if name is None:
            return match.group(0)
        if path == moved:
            path = 'Nyll/SchemeTheory/RingTheory/Dimension/PrimeContainingAtHeightOne.lean'
        return readme_lean_link(files, selected_paths, path, name)
    text = re.sub(r'\[([^]]+)\]\((Nyll/[^)#]+\.lean)#L(\d+)\)', replace, text)
    # These URLs identify immutable Mathlib source, inspected at the pinned revision.
    mathlib = {
        'CategoryTheory/Action/Continuous.lean#L150': 'DiscreteContAction',
        'CategoryTheory/Galois/Topology.lean#L103': 'autEmbedding_range_isClosed',
        'CategoryTheory/Action/Continuous.lean#L81': 'HasForget₂',
        'CategoryTheory/Galois/Equivalence.lean#L40': 'functorToContAction',
        'CategoryTheory/Galois/Basic.lean#L66': 'PreGaloisCategory',
        'CategoryTheory/Galois/Decomposition.lean#L314': 'exists_hom_from_galois_of_connected',
        'CategoryTheory/Galois/Prorepresentability.lean#L455': 'FiberFunctor.isPretransitive_of_isConnected',
        'CategoryTheory/Galois/Equivalence.lean#L90': 'IsEquivalence'}
    base = ('https://github.com/leanprover-community/mathlib4/blob/'
            '065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/')
    for suffix, name in mathlib.items():
        text = text.replace(f'[Mathlib]({base}{suffix})', f'[`{name}` (Mathlib)]({base}{suffix})')
    return text


def current_stacks_readme(text, files, selected_paths):
    """Keep the chapter inventory; update only explicitly reviewed correspondences."""
    def endpoint(family, relative, name):
        return readme_lean_link(files, selected_paths, f'Nyll/{family}/{relative}.lean', name)
    def efg(relative, name):
        return endpoint('EtaleFundamentalGroups', relative, name)
    def ec(relative, name):
        return endpoint('EtaleCohomology', relative, name)
    def entry(number, tag, evidence):
        return f'[{number}](https://stacks.math.columbia.edu/tag/{tag}) ({evidence})'
    def update(number, tag, evidence, complete):
        nonlocal text
        prefix = f'[{number}](https://stacks.math.columbia.edu/tag/{tag})'
        lines = text.splitlines()
        matches = [i for i, line in enumerate(lines) if line.startswith('| [') and prefix in line]
        require(len(matches) == 1, 'Expected exactly one Stacks inventory item: ' + number)
        i = matches[0]
        cells = lines[i].strip()[1:-1].strip().split(' | ')
        require(len(cells) == 3, 'Unexpected Stacks table row: ' + number)
        done, remaining = [], []
        for cell, destination in ((cells[1], done), (cells[2], remaining)):
            destination.extend(x for x in re.split(r';\s*(?=\[\d)', cell.strip())
                               if x != '—' and not x.startswith(prefix))
        (done if complete else remaining).append(entry(number, tag, evidence))
        def ordered(items):
            return '; '.join(sorted(items, key=lambda x: tuple(map(int,
                re.match(r'\[(\d+(?:\.\d+)+)', x)[1].split('.'))))) if items else '—'
        lines[i] = '| ' + cells[0] + ' | ' + ordered(done) + ' | ' + ordered(remaining) + ' |'
        text = '\n'.join(lines) + '\n'

    text = text.replace('Coverage below refers to the published source, checked on 2026-10-13.',
                        'Coverage below refers to the source included in this extract.')
    update('58.3.7', '0BN0', efg('GaloisCategories/MorphismComponents',
        'exists_component_maps_of_given_coproduct_decompositions') +
        '; component maps complete the existing Galois-category decomposition results', True)
    update('58.9.3', '0A49', efg('FiniteEtale/ProperAlgebraicallyClosedExtension',
        'pullback_isEquivalence_of_isProper_of_isAlgClosed_constant_extension'), True)
    update('58.31.4', '0EYF', efg('Kummer/AdjoinRoot/StandardTameCodimensionOne',
        'standardKummerCover_isTamelyRamifiedInCodimensionOne'), True)
    update('58.30.1', '0C0P', 'partial: geometric-fibre-to-total-space surjectivity over a '
        'strictly henselian local base for proper flat finitely presented families with '
        'geometrically reduced connected fibres; ' +
        efg('GeometricFiber/StrictHenselianProperFiberSurjective',
            'fundamentalGroupHom_proper_geometricFiber_surjective_of_strictHenselian') +
        '; the general specialization map is not yet constructed', False)
    update('59.55.1', '03QO', 'partial: strictly local exactness and positive-degree vanishing; ' +
        ec('Classical/HenselianLocal', 'etaleAbelianCohomology_succ_subsingleton_of_henselianLocalRing'), False)
    update('59.55.2', '03QP',
        ec('Sites/FinitePushforwardStalkSurjectivity', 'etalePushforwardStalkComparison_isIso') +
        '; ' + ec('Classical/FinitePushforward', 'etaleAbelianPushforwardFinite_rightDerived_succ_isZero'), True)
    update('59.55.3', '0959', 'module-sheaf case; ' +
        ec('Sites/FiniteBaseChange', 'finiteDirectImageBaseChange_app_isIso'), False)
    update('59.82.3', '0CAM', endpoint('SchemeTheory', 'Topology/SpectralClosedRestriction',
        'exists_clopen_partition_of_connected_closed_intersections'), True)
    update('59.82.4', '09ZG', endpoint('SchemeTheory', 'Topology/SpectralClosedSheafRestriction',
        'sheaf_globalSections_restriction_bijective'), True)
    update('59.91.4', '0A3T', 'degree zero over an affine base; ' +
        ec('Sites/ProperGeometricFiberSections', 'etalePushforwardGeometricFiberSections_bijective'), False)
    summary = ('Finite étale covers of a proper scheme are invariant under extension\n'
        'of separably closed fields (including transcendental extension): ' +
        efg('FiniteEtale/ProperSeparablyClosedExtension',
            'pullback_isEquivalence_of_isProper_of_isSepClosed_constant_extension') + '.\n'
        'The projection induces the actual continuous fundamental-group isomorphism ' +
        efg('GeometricFiber/ProperConstantExtensionFundamentalGroup',
            'fundamentalGroupEquivProperConstantExtension') + '. No smoothness, reducedness '
        'or connectedness assumption on the proper scheme is needed.\n\n'
        'For a proper scheme over a henselian local ring, closed-fibre restriction is\n'
        'fully faithful. Affine adic effectivity and compatible closed-projective\n'
        'generators and syzygy comparisons are constructed. Global algebraization\n'
        'and essential surjectivity for [58.9.1](https://stacks.math.columbia.edu/tag/0A48)\n'
        'and [58.9.2](https://stacks.math.columbia.edu/tag/0GS2), and the general\n'
        'specialization maps of [58.16](https://stacks.math.columbia.edu/tag/0BUP) and\n'
        '[58.30](https://stacks.math.columbia.edu/tag/0BUQ), remain unfinished.\n\n'
        'The cohomology library proves proper henselian H⁰ comparison and H¹\n'
        'injectivity for arbitrary commutative-ring coefficients: ' +
        ec('Sites/ProperHenselianH0', 'etaleClosedFiber_globalSections_bijective') + ' and ' +
        ec('Classical/ProperHenselianH1', 'etaleClosedFiber_cohomology_one_injective') +
        '. Finite direct image has no positive higher direct images and gives the\n'
        'coefficient-linear comparison Hⁿ(Y, f_*F) ≃ Hⁿ(X, F) for every n: ' +
        ec('Classical/FinitePushforward', 'etaleCohomologyFinitePushforwardEquiv') + '.\n'
        'It commutes with arbitrary base change for module sheaves, without a torsion, '
        'flatness or finite-presentation hypothesis.\n\n'
        'The trace of an endomorphism of a supplied perfect complex is defined by ' +
        ec('Trace/Perfect', 'perfectComplexTrace') +
        ', with model independence, cyclicity, shift signs and the proved cone formula.\n'
        'Constant-coefficient Frobenius actions and all positive iterates are compared in ' +
        ec('Frobenius/ModuleConstantFieldAction',
           'finiteFieldFrobeniusCohomology_pow_eq_constantFieldAction') + '.\n\n'
        'Higher proper base change, general Nagata compactification, compactly\n'
        'supported cohomology and its finiteness/perfectness, the nonconstant\n'
        'coefficient Frobenius comparison, and the geometric trace calculation\n'
        'remain open. The Grothendieck–Lefschetz formulas\n'
        '[64.20.4](https://stacks.math.columbia.edu/tag/03V3) and\n'
        '[64.20.5](https://stacks.math.columbia.edu/tag/03V2) are not yet proved.')
    text = readme_section(text, 'Current endpoints and remaining comparisons',
                          'etale-current-endpoints', summary,
                          before='Use and build' if '## Use and build\n' in text else 'Public API')
    return refresh_stacks_lean_links(text, files, selected_paths)


def current_mathematics_readme(text, files, selected_paths, primary):
    """Reviewed source-backed updates; partial endpoints never complete a chapter."""
    def link(family, relative, name):
        return readme_lean_link(files, selected_paths, f'Nyll/{family}/{relative}.lean', name)
    if primary == ['ClassFieldTheory']:
        text = readme_section(text, 'Scope', 'cft-scope',
            'Local class field theory covers nonarchimedean local fields. Global class field\n'
            'theory covers number fields and function fields over finite fields, including\n'
            'reciprocity, existence, norm subgroups, conductors and ray class fields.')
        text = text.replace('## Incomplete results\n', '## Function-field class field theory\n')
        prefix = 'AlgebraicFunctionFieldTheory/'
        rows = [
            ('Existence and classification', link('ClassFieldTheory', prefix +
                'GlobalClassFields/Classification', 'exists_classField_of_open') + ' and ' +
             link('ClassFieldTheory', prefix + 'GlobalClassFields/Classification',
                  'finiteAbelianFieldNormSubgroupOrderIso'),
             'Finite abelian extensions correspond, with reversed inclusion, to open '
             'finite-index subgroups in the ordinary idèle-class topology, through the actual norm image.'),
            ('Local–global compatibility', link('ClassFieldTheory', prefix +
                'Artin/LocalGlobalCompatibility', 'localArtin_eq_abelianFiniteArtin_placeIdele') + ' and ' +
             link('ClassFieldTheory', prefix + 'Artin/UnramifiedFrobenius',
                  'localDecompositionArtin_eq_unramifiedFrobenius_zpow'),
             'The actual local and global Artin maps agree on a one-place idèle. At an unramified '
             'place, the local value is arithmetic Frobenius to the power of the valuation.'),
            ('Profinite reciprocity', link('ClassFieldTheory', prefix +
                'Artin/ProfiniteReciprocity', 'profiniteReciprocity'),
             'The profinite completion for the ordinary idèle-class topology is isomorphic to the abelianized absolute Galois group.')]
        content = ('For function fields over a finite constant field, the following endpoints\n'
                   'use a chosen rational parameter. Their principal-divisor structure '
                   '(finite support of valuation orders and degree zero) is constructed from '
                   'the function-field hypotheses by ' + link('ClassFieldTheory', prefix +
                       'Fields/Curve', 'isCurveOver') + '. No class-field existence input '
                   'or norm-cofinality hypothesis is supplied.\n\n'
                   '| Result | Lean endpoint |\n| --- | --- |\n' + '\n'.join(
                       f'| {title}: {description} | {endpoint} |'
                       for title, endpoint, description in rows) + '\n\n'
                   'The development also includes arithmetic Frobenius normalization, conductors,\n'
                   'ray class fields, prescribed splitting, and the cyclic Hasse norm theorem.')
        text = readme_section(text, 'Function-field class field theory', 'cft-function-fields', content)
    if primary == ['JacobianVarieties']:
        text = text.replace('Nyll/JacobianVarieties/Picard/TorsionCardinality.lean',
                            'Nyll/JacobianVarieties/Picard/Torsion/TorsionCardinality.lean')
        rows = [
            ('A full ground-field modulus for the original open complement',
             'GeneralGeometricModulusExistence', 'exists_group_geometricRegularMapHasModulus'),
            ('A unique equivariant factor through the intrinsic Picard degree-one torsor',
             'GeneralGroupPicardOneFactorization', 'exists_modulus_unique_picardOneFactor'),
            ('A unique pointed group factor',
             'GeneralGroupPointedFactorization', 'exists_modulus_unique_pointedGroupFactor'),
            ('Least full conductor classifying all moduli over an algebraically closed field',
             'GeneralGroupLocalSymbolExistence', 'existsUnique_group_regularMap_modulus_classification'),
            ('The product conductor is the coefficientwise maximum of the two conductors',
             'GeneralGroupProductConductor', 'exists_group_regularMap_product_conductors')]
        content = ('For a smooth proper geometrically integral curve over an arbitrary field,\n'
                   'a morphism from a nonempty open subset to a separated commutative group\n'
                   'scheme locally of finite type constructs a modulus with its multiplicities.\n'
                   'The unpointed factorization does not require a rational point, a perfect\n'
                   'base field, or a smooth connected target.\n\n'
                   '| Result | Lean endpoint |\n| --- | --- |\n' + '\n'.join(
                       f'| {title} | {link("JacobianVarieties", "Generalized/" + path, name)} |'
                       for title, path, name in rows) + '\n\n'
                   'The pointed form assumes a rational point in the original open sent to the '
                   'identity. Uniqueness is for the factor attached to the constructed modulus.\n'
                   'Over an algebraically closed field in any characteristic, the conductor '
                   'classifies full moduli of the actual point-value function, extended by the '
                   'identity outside the open. Its support can be smaller than the original boundary. '
                   'The map also constructs its reciprocal local symbol: ' +
                   link('JacobianVarieties', 'Generalized/GeneralGroupLocalSymbolExistence',
                        'exists_group_regularMap_localSymbol') + '.\n'
                   'Lie and differential comparisons, the actual nonreduced kernel and its\n'
                   'Witt decomposition, symmetric powers, analytic uniformization, and\n'
                   'pinching comparisons remain unfinished.')
        text = readme_section(text, 'Generalized Jacobians', 'generalized-jacobians',
                              content, before='Incomplete results')
        text = text.replace('Import the curve library or the Jacobian library with:',
                            'Import the Jacobian library and its required curve modules with:')
        if 'Nyll/AlgebraicCurves/All.lean' not in selected_paths:
            text = text.replace('import Nyll.AlgebraicCurves.All\n', '')
    if primary == ['Yamaguchi26AbfaithfulGalois', 'Yamaguchi26SolvableCoverings']:
        # This paper moved to the private, unmaintained progress area. Its old
        # public prose and imports must not survive removal of the source tree.
        text = re.sub(r'The collection also includes an ongoing formalization of\n.*?\n\n',
                      '', text, flags=re.S)
        text = re.sub(r'^### Branched coverings of the projective line over the integers\n'
                      r'.*?(?=^## |\Z)', '', text, flags=re.M | re.S)
        text = re.sub(r'^\*\*Branched coverings of the projective line over the integers\*\*\n'
                      r'.*?(?=^## |\Z)', '', text, flags=re.M | re.S)
        text = text.replace('import Nyll.ShimizuYamaguchi26BranchedCoverings.All\n', '')
        absolute = 'Nyll/Yamaguchi26AbfaithfulGalois/Theorem6Dot6AbsoluteCenter.lean'
        examples = 'Nyll/Yamaguchi26AbfaithfulGalois/Theorem6Dot7FieldSlimExamples.lean'
        center = readme_lean_link(files, selected_paths, absolute,
            'absoluteGalois_finiteStepSolvable_centerfree')
        slim = readme_lean_link(files, selected_paths, absolute,
            'absoluteGalois_finiteStepSolvable_slim_of_cyclotomic_and_cyclic_extensions')
        fields = ' ; '.join(readme_lean_link(files, selected_paths, examples, name) for name in (
            'torallyKummerFaithful_finiteStepSolvable_slim',
            'finitelyGenerated_finiteStepSolvable_slim',
            'subpadic_finiteStepSolvable_slim', 'higherLocalField_finiteStepSolvable_slim'))
        rows = [
            (absolute, '| ' + center + ' ; ' + slim + ' | For every m ≥ 2, ab-faithfulness '
             'of the absolute Galois group implies center-freeness of its maximal m-step solvable '
             'quotient in any characteristic. Slimness additionally assumes infinite p-primary '
             'cyclotomic extensions for p different from the characteristic, and a cyclic '
             'degree-p extension in characteristic p. Formal Hilbert 90 is constructed from '
             'the field, not supplied as input. |'),
            (examples, '| ' + fields + ' | For every m ≥ 2, slimness is proved directly for '
             'infinite fields finitely generated over their prime field, fields embedding into '
             'a finitely generated extension of Q_p, and positive-dimensional higher local fields. '
             'The separate toral application assumes characteristic zero, toral '
             'Kummer-faithfulness and ab-faithfulness. Slimness means every open subgroup '
             'has trivial centralizer in the ambient quotient. |')]
        for path, row in rows:
            pattern = r'^\| [^\n]*' + re.escape(path) + r'[^\n]*\|$'
            text, count = re.subn(pattern, lambda _: row, text, flags=re.M)
            require(count == 1, 'Expected one research-paper result row: ' + path)
    if primary == ['AnabelianGeometry']:
        genus_zero = link('AnabelianGeometry', 'WeightFiltration/GenusZeroNakamura',
                         'exists_schemeIso_of_genusZero_arithmeticFundamentalGroupEquiv')
        rational = link('AnabelianGeometry', 'WeightFiltration/RationalConfigurationNakamura',
                       'exists_projectiveTransformation_with_inertia_of_arithmeticFundamentalGroupEquiv')
        text = text.replace(
            'A Lean 4 library **under development**, aiming to formalize the Grothendieck\n'
            'conjecture for hyperbolic curves. It currently develops geometric étale\n'
            'fundamental groups, their slimness, and explicit genus-zero calculations.',
            'A Lean 4 library proving genus-zero weak reconstruction over number fields,\n'
            'geometric fundamental-group slimness, and explicit genus-zero calculations.\n'
            'Weak reconstruction establishes a curve isomorphism; realizing the supplied\n'
            'group isomorphism and the full Grothendieck correspondence remain further goals.')
        text = readme_section(text, 'Scope', 'anabelian-scope',
            'The arithmetic results concern smooth geometrically integral genus-zero curves\n'
            'over number fields with at least three geometric punctures. The geometric\n'
            'slimness and fundamental-group calculations below concern algebraically closed\n'
            'fields of characteristic zero. All use the actual finite étale fiber functors.\n\n'
            'The broader target is the Grothendieck correspondence for hyperbolic curves:\n'
            'curve isomorphisms should correspond to arithmetic fundamental-group\n'
            'isomorphisms over the absolute Galois group, modulo geometric inner conjugation.')
        content = ('Let k be a number field and let U₁ and U₂ be opens in smooth proper\n'
                   'geometrically integral curves of geometric genus zero, each with at least\n'
                   'three geometric boundary points. A continuous isomorphism of their pointed\n'
                   'arithmetic fundamental groups commuting with the maps to G_k implies that\n'
                   'U₁ and U₂ are isomorphic over k: ' + genus_zero + '.\n\n'
                   'No rational point, split compactification, rational boundary, supplied\n'
                   'finite-cover model, or inertia correspondence is required as input.\n'
                   'The finite models and their descent are constructed in the proof.\n\n'
                   'For complements of finite sets of at least three k-rational points on\n'
                   'the projective line, ' + rational + ' also constructs a projective\n'
                   'linear transformation carrying one puncture set to the other, together\n'
                   'with the puncture bijection characterized by geometric inertia conjugacy.\n\n'
                   'These are weak reconstruction results in the direction of\n'
                   '[Nakamura’s genus-zero theorem](https://doi.org/10.1515/crll.1990.411.205):\n'
                   'the conclusion produces a curve isomorphism. It does not identify its\n'
                   'induced fundamental-group map with the supplied isomorphism.')
        text = readme_section(text, 'Genus-zero arithmetic reconstruction',
                              'anabelian-genus-zero', content, before='Main results')
        text = readme_section(text, 'Incomplete results', 'anabelian-reconstruction',
            'Realization of a prescribed arithmetic fundamental-group isomorphism by the\n'
            'reconstructed curve map, uniqueness in that correspondence, and reconstruction\n'
            'for general hyperbolic curves of positive genus remain unfinished.\n'
            'The selected arithmetic results are over number fields; the general finitely\n'
            'generated characteristic-zero base-field theorem is not claimed here.')
    if primary == ['EtaleFundamentalGroups', 'EtaleCohomology']:
        text = current_stacks_readme(text, files, selected_paths)
    return text


def readme_for_extract(text, files, selected_paths, primary, source_sha=None):
    """Preserve prose outside reviewed distribution, credit and mathematical blocks.

    The first migration replaces the known legacy distribution sentence and the
    license-section body. Later runs replace only those explicit generated blocks.
    No commit SHA is embedded: unchanged selected source gives unchanged prose.
    """
    require(source_sha is None or SHA.fullmatch(source_sha), 'Invalid canonical source SHA')
    _, pi1, anthropic, other = selected_records(files, selected_paths)
    text = text.replace('\r\n', '\n')
    dependencies = sorted({p.split('/')[1] for p in selected_paths
                           if p.startswith('Nyll/') and len(p.split('/')) > 2} - set(primary))
    distribution = ('Only the module-level import closure of ' +
        ', '.join(f'`Nyll.{f}.All`' for f in primary) +
        ' is bundled. Dependencies retain their canonical `Nyll` imports.')
    if dependencies:
        distribution += ('\n\nSupporting modules are included from ' +
            ', '.join(f'[{f}](Nyll/{f}/)' for f in dependencies) +
            '. These dependency libraries are included only to the extent required by the imports.')
    else:
        distribution += '\n\nThe NYLL sources in this extract use Mathlib without other bundled NYLL libraries.'
    def initial_distribution(text, block):
        old = 'Bundled dependencies use the same `Nyll` imports as the complete library.'
        if text.count(old) == 1:
            return text.replace(old, block)
        anchor = 'from [NYLL](https://github.com/n-yamaguchi-0729/NYLL).'
        require(text.count(old) == 0 and text.count(anchor) == 1,
                'Expected known extraction sentence for initial migration')
        return text.replace(anchor, anchor + '\n\n' + block)
    text = managed_block(text, 'distribution', distribution, initial_distribution)
    text = re.sub(r'The class-field-theory modules use Mathlib and the bundled\n.*?foundations\.\n',
                  '', text, flags=re.S)
    text = current_mathematics_readme(text, files, selected_paths, primary)
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
