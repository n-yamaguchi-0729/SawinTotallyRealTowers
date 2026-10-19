"""Consistent reader-facing introductions and result hierarchy for public extracts.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
"""
import re

NYLL = '[NYLL](https://github.com/n-yamaguchi-0729/NYLL)'
GUIDES = 'https://n-yamaguchi-0729.github.io/NYLL/libraries/'
INTRODUCTIONS = {
    ('ProCGroups',): ('pro-c-groups',
        'Developed as part of {nyll}, this Lean library studies profinite and pro-C groups,\n'
        'from finite quotients and completions to free groups, Golod–Shafarevich criteria\n'
        'and completed Crowell sequences. The {guide} explains the main constructions\n'
        'and selected theorems, with links to their proofs.'),
    ('ClassFieldTheory',): ('class-field-theory',
        'Developed as part of {nyll}, this Lean library treats class field theory for\n'
        'nonarchimedean local fields, number fields and function fields over finite fields.\n'
        'The {guide} presents reciprocity, existence and the other selected results\n'
        'with their mathematical hypotheses and links to the formal proofs.'),
    ('SawinTotallyRealTowers',): ('sawin-totally-real-towers',
        'This Lean component of {nyll} develops Sawin’s theorem on totally real fields\n'
        'of unbounded degree and bounded root discriminant, together with Martinet’s\n'
        'corollary and Shafarevich’s relation-rank bound. The {guide} describes these\n'
        'three results and their relationship to the formalized benchmark statements.'),
    ('EtaleFundamentalGroups', 'EtaleCohomology'): ('etale-fundamental-groups-and-cohomology',
        'These Lean libraries develop étale fundamental groups and étale cohomology\n'
        'within {nyll}, following the Stacks Project from finite étale covers and Galois\n'
        'categories to cohomological comparisons and trace constructions. The {guide}\n'
        'introduces selected results; the chapter inventory below distinguishes completed\n'
        'statements from partial results and the remaining goals.'),
    ('JacobianVarieties',): ('jacobian-varieties',
        'This Lean component of {nyll} develops Jacobians and generalized Jacobians\n'
        'of algebraic curves, including Abel–Jacobi maps, factorization properties,\n'
        'torsion and cohomological comparisons. The {guide} explains the principal\n'
        'constructions and results, including their base-field and characteristic hypotheses.'),
    ('Yamaguchi26AbfaithfulGalois', 'Yamaguchi26SolvableCoverings'): ('research-papers',
        'Developed within {nyll}, this Lean library formalizes Naganori Yamaguchi’s\n'
        'papers on ab-faithfulness of absolute Galois groups and extension of solvable\n'
        'coverings across horizontal divisors. The {guide} explains the selected arithmetic\n'
        'and geometric results, while the sections below relate them to the papers\n'
        'and identify the parts that remain unfinished.'),
    ('AnabelianGeometry',): ('anabelian-geometry',
        'This Lean component of {nyll} studies the recovery of algebraic curves from\n'
        'their étale fundamental groups, with results on genus-zero reconstruction\n'
        'over number fields, geometric slimness and explicit fundamental-group calculations.\n'
        'The {guide} explains the proved reconstruction statement and distinguishes it\n'
        'from the full Grothendieck correspondence, which remains a further goal.')}


def presentation(text, primary):
    """Rewrite the reviewed opening; keep source credits and mathematical hypotheses."""
    key = tuple(primary)
    if key not in INTRODUCTIONS:
        return text
    match = re.search(r'<!-- nyll-publication:distribution:begin -->.*?'
                      r'<!-- nyll-publication:distribution:end -->', text, re.S)
    if not match:
        raise ValueError('Missing distribution block')
    distribution = match[0]
    text = text[:match.start()] + text[match.end():]
    text = re.sub(r'^## Included sources\n.*?(?=^## |\Z)', '', text, flags=re.M | re.S)
    start = re.search(r'^## ', text, re.M)
    if not start:
        raise ValueError('Missing README sections')
    prefix, body = text[:start.start()], text[start.start():]
    title = prefix.splitlines()[0]
    badges = '\n'.join(line for line in prefix.splitlines() if line.startswith('[!['))
    slug, prose = INTRODUCTIONS[key]
    intro = prose.format(nyll=NYLL, guide=f'[mathematical guide]({GUIDES}{slug}/)')
    if key == ('JacobianVarieties',):
        intro += ('\n\nThe curve and Jacobian development builds substantially on\n'
                  '[Anthropic’s Fermat’s Last Theorem project](https://github.com/anthropics/fermats-last-theorem),\n'
                  'whose code is adapted and extended here. The original source credits\n'
                  'are retained in the files and in [NOTICE](NOTICE).')
    text = '\n\n'.join(part for part in (title, badges, intro) if part) + '\n\n' + body
    anchor = '## Public API\n' if '## Public API\n' in text else '## Use and build\n'
    if text.count(anchor) != 1:
        raise ValueError('Missing or ambiguous README API section')
    text = text.replace(anchor, '## Included sources\n\n' + distribution + '\n\n' + anchor)

    if key == ('ProCGroups',):
        old = re.search(r'^The current library also includes finite and profinite abelian\n'
                        r'.*?from a topological generator and finite quotients of every positive order\.\n',
                        text, re.M | re.S)
        if old:
            rows = ('| [Pontryagin biduality](Nyll/ProCGroups/Abelian/ProfiniteBidual.lean) | '
                    'Biduality for finite and profinite abelian groups. |\n'
                    '| [Recognition of the profinite integers](Nyll/ProCGroups/Completion/ProfiniteIntegerRecognition.lean) | '
                    'A topological generator and finite quotients of every positive order '
                    'characterize the profinite integers. |\n')
            text = text[:old.start()].rstrip() + '\n' + rows + text[old.end():]
            text = text.replace('## Main results\n',
                'The [full Tate module](Nyll/ProCGroups/Abelian/FullTateModule.lean) is also\n'
                'constructed as an inverse limit of actual torsion subgroups.\n\n## Main results\n', 1)
    if key == ('JacobianVarieties',):
        text = text.replace('## Main results\n\nFor a smooth',
                            '## Main results\n\n### Jacobians and curves\n\nFor a smooth')
        text = re.sub(r'^## Generalized Jacobians\n', '### Generalized Jacobians\n', text, flags=re.M)
    if key == ('AnabelianGeometry',):
        arithmetic = re.search(r'^## Genus-zero arithmetic reconstruction\n(.*?)'
                               r'(?=^## |\Z)', text, re.M | re.S)
        if arithmetic:
            text = text[:arithmetic.start()] + text[arithmetic.end():]
            heading = '### Grothendieck’s conjecture for genus-zero curves over number fields\n'
            text = text.replace('## Main results\n', '## Main results\n\n' + heading +
                                arithmetic[1] + '### Geometric fundamental groups\n', 1)
    return text
