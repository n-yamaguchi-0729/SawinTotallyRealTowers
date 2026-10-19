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
        'This Lean component of {nyll} develops generalized Jacobians of algebraic\n'
        'curves, with ordinary Jacobians as the zero-modulus case. It includes\n'
        'Abel–Jacobi maps, unique factorization through generalized Jacobians,\n'
        'torsion and cohomological comparisons. The {guide} explains the main results\n'
        'and their hypotheses.'),
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
        'The {guide} presents the reconstruction theorems and geometric applications\n'
        'with links to their formal proofs.')}


def presentation(text, primary):
    """Rewrite the reviewed opening; keep source credits and mathematical hypotheses."""
    key = tuple(primary)
    if key not in INTRODUCTIONS:
        return text
    text = re.sub(r'<!-- nyll-publication:distribution:begin -->.*?'
                  r'<!-- nyll-publication:distribution:end -->\s*', '', text, flags=re.S)
    text = re.sub(r'^## Included sources\n.*?(?=^## |\Z)', '', text, flags=re.M | re.S)
    start = re.search(r'^## ', text, re.M)
    if not start:
        raise ValueError('Missing README sections')
    prefix, body = text[:start.start()], text[start.start():]
    title = prefix.splitlines()[0]
    if key == ('JacobianVarieties',):
        title = re.sub(r'^# JacobianVarieties\b', '# Generalized Jacobians', title)
    badges = '\n'.join(line for line in prefix.splitlines() if line.startswith('[!['))
    slug, prose = INTRODUCTIONS[key]
    intro = prose.format(nyll=NYLL, guide=f'[mathematical guide]({GUIDES}{slug}/)')
    if key == ('JacobianVarieties',):
        intro += ('\n\nThe curve and Jacobian development builds substantially on\n'
                  '[Anthropic’s Fermat’s Last Theorem project](https://github.com/anthropics/fermats-last-theorem),\n'
                  'whose code is adapted and extended here. The original source credits\n'
                  'are retained in the files and in [NOTICE](NOTICE).')
    text = '\n\n'.join(part for part in (title, badges, intro) if part) + '\n\n' + body
    text = re.sub(r'Elaboration and linter options are shared in `lakefile.toml`:\n'
                  r'.*?Maintained sources do not override these options\.\n', '', text, flags=re.S)
    if key in {('ProCGroups',), ('ClassFieldTheory',)}:
        verification = (
            '[CI](.github/workflows/lean.yml) checks the import closure, builds with\n'
            'warnings as errors, audits declarations, and verifies proofs with NanoDa\n'
            'and the Lean kernel. The [public API contract](.github/verification/main-declarations.json)\n'
            'checks the named declarations and their source modules.\n\n')
        text = re.sub(r'(?<=## Verification\n)\n.*?(?=^## |\Z)',
                      '\n' + verification, text, flags=re.M | re.S)
    if key == ('SawinTotallyRealTowers',):
        verification = (
            'The accepted [Martinet and Shafarevich Lean Eval submissions]\n'
            '(https://github.com/leanprover/lean-eval-submissions/blob/main/results/n-yamaguchi-0729.json)\n'
            'and the [earlier Sawin proof]\n'
            '(https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/blob/'
            '3a455e1aa9140dbbe7b7d68f508392a69c86d0f4/Lean4/SawinTotallyRealTowers/SawinTotallyRealTower.lean#L31)\n'
            'concern earlier revisions.\n\n'
            '[CI](.github/workflows/lean.yml) builds the current import closure with warnings\n'
            'as errors and verifies proofs with NanoDa and the Lean kernel. It checks the\n'
            'Formal Conjectures and Martinet benchmark statements, and the public\n'
            'Shafarevich theorem. The latter has a different interface from the accepted\n'
            'submission. See the [verification notes](.github/verification/README.md)\n'
            'for the source audit and verification commands.\n\n')
        verification = verification.replace(']\n(', '](')
        text = re.sub(r'(?<=## Verification\n)\n.*?(?=^## |\Z)',
                      '\n' + verification, text, flags=re.M | re.S)

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
                            '## Main results\n\n### Zero modulus: ordinary Jacobians\n\nFor a smooth')
        text = text.replace('### Jacobians and curves\n', '### Zero modulus: ordinary Jacobians\n')
        text = re.sub(r'^#{2,3} Generalized Jacobians\n', '### General moduli and factorization\n', text, flags=re.M)
        text = text.replace('Import the Jacobian library and its required curve modules with:',
                            'Import the generalized Jacobian library with:')
        text = text.replace('For the Jacobian construction and its principal properties:',
                            'For the ordinary Jacobian construction and its principal properties:')
    if key == ('AnabelianGeometry',):
        arithmetic = re.search(r'^## Genus-zero arithmetic reconstruction\n(.*?)'
                               r'(?=^## |\Z)', text, re.M | re.S)
        if arithmetic:
            text = text[:arithmetic.start()] + text[arithmetic.end():]
            heading = '### Grothendieck’s conjecture for genus-zero curves over number fields\n'
            text = text.replace('## Main results\n', '## Main results\n\n' + heading +
                                arithmetic[1] + '### Geometric fundamental groups\n', 1)
        text = text.replace('The proofs realize open subgroups by finite étale covers\n'
                            'and use geometric cohomology and ramification calculations.\n', '')
        text = text.replace('the ambient group. \n', 'the ambient group.\n\n')
    text = text.replace('inverse limit of actual torsion subgroups', 'inverse limit of torsion subgroups')
    text = text.replace('`Jacobian C` over `k` without requiring a rational point.',
                        '`Jacobian C` over `k`.')
    text = text.replace('actual étale H¹', 'étale H¹')
    text = text.replace('the library studies the actual map of étale fundamental',
                        'the library studies the map of étale fundamental')
    text = text.replace(' Completeness is not required.', '')
    text = re.sub(r'\n{3,}', '\n\n', text)
    return text
