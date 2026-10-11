# Anthropic FLT sources in SchemeTheory

These files adapt the fixed upstream sources listed below. Local paths in this
document are relative to `Nyll/SchemeTheory`; historical module names in the
relocation table have the additional `Nyll.` prefix in this distribution.

## Fixed source and notices

- Repository: [Anthropic Fermat's Last Theorem](https://github.com/anthropics/fermats-last-theorem)
- Fixed revision: `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`
- [Upstream NOTICE](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE) and
  [upstream ATTRIBUTION.md](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md) are copied byte-for-byte as
  [ANTHROPIC_FLT_NOTICE](ANTHROPIC_FLT_NOTICE) and
  [ANTHROPIC_FLT_ATTRIBUTION.md](ANTHROPIC_FLT_ATTRIBUTION.md). “This repository” in
  those copies denotes the upstream repository. Retain the earlier FLT, flt-regular
  and Mathlib rights and author notices identified there; Anthropic is not asserted
  to be the sole author of every upstream contribution.
- The three proof files below have no per-file attribution row in that pinned
  ATTRIBUTION.md. Their absent headers are not a basis for inventing an author list.
- Licence: Apache 2.0, covered by the repository LICENSE.

## Exact source-to-owner map

### `FaithfullyFlatModuleDatum.lean`

- Declaration: `Module.FaithfullyFlat.isBaseChange_eqLocus_of_descentDatum`
- [Proof source](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum.lean)
- [Public statement](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum.lean)

### `FaithfullyFlatAlgebraEqualizer.lean`

- Declaration: `Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum`
- [Proof source](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum.lean)
- [Public statement](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum.lean)

### `FaithfullyFlatGradedAlgebraEqualizer.lean`

- Declaration: `Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle`
- [Proof source](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle.lean)
- [Public statement](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle.lean)

## Local changes

All three owners directly contain proofs; the generated `P2M.Util` elaborator and
separate proof/card wrappers are not imported. Bare `Mathlib` imports are replaced
with explicit leaf imports. `autoImplicit false` is retained, and no new axiom or
unproved assumption is introduced.

- Module datum: implementation helpers are private in a mathematical namespace.
  The unused `S17DescCanon` structure and canonical-datum example are omitted.
  Injectivity of `n ↦ n ⊗ 1` uses Mathlib's sharper
  `Algebra.TensorProduct.mk_one_injective_of_isScalarTower` and tensor commutation:
  the existing upstairs module structure supplies a retraction, without needing
  faithful flatness for that helper. Only genuinely unused private-helper class
  assumptions are omitted. A typed `LinearMap.range κ` boundary normalizes the
  equalizer witness before destructuring, preserving the chosen tensor dictionaries.
- Ordinary algebra: the upstream module-to-algebra comparison proof is retained.
  The two large heartbeat overrides are removed; an unused equation name is omitted.
  Linear tensor operations in the proof are explicitly root-qualified, avoiding
  accidental resolution to `Algebra.TensorProduct` inside the public theorem namespace.
  The cocycle comparison uses an explicitly typed pointwise equality. In the public
  statement and proof, `Commute.all _ _` now names the two mapped operands explicitly.
  This changes that proof-argument expression, not the quantified assumptions or
  mathematical conclusion. The
  final linear/algebra map comparison uses a typed local algebra homomorphism and
  fully applied tensor-lift and map-add equalities, avoiding dictionary-sensitive
  rewriting through the commutativity proof argument.
- Graded algebra: the ordinary theorem supplies bijectivity. Only the additional
  homogeneous-component invariance proof remains, eliminating its duplicated
  ordinary-descent proof. Its degree-preservation hypothesis is unchanged. The
  public `Commute.all` proof also names both actual mapped operands explicitly.
- Current-API edits: `TensorProduct.inductionOn` replaces the deprecated three-case
  induction theorem, obsolete coercion simplifier arguments are removed, and broad
  simplifier calls are narrowed. These are adaptations, not claims of byte-identical
  proof bodies.

## Versions

Upstream used Lean `v4.33.1` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. This distribution uses the
versions pinned in `lean-toolchain` and `lake-manifest.json`.

## Faithful flatness on the open image

`RingTheory/Descent/FaithfullyFlatOnOpenImage.lean` extracts two helpers from
[P2M/Sol/S_Algebra_FinitePresentation_of_faithfullyFlat_of_finitePresentation.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_FinitePresentation_of_faithfullyFlat_of_finitePresentation.lean#L17-L61), rather than importing the full finite-presentation proof:

- `LFPRingC.exists_ideal_range_comap` becomes
  `PrimeSpectrum.exists_ideal_range_comap_of_flat_of_finitePresentation`. For a flat
  finitely presented algebra, it constructs an ideal whose zero-locus complement
  is the image on spectra. Its hypotheses and conclusion are unchanged.
- `LFPRingC.faithfullyFlat_baseChange_of_map_eq_top` becomes
  `Module.Flat.faithfullyFlat_baseChange_of_map_eq_top`. A flat algebra becomes
  faithfully flat after a base change that makes the specified image ideal the
  unit ideal. The original one-way image-containment hypothesis is retained;
  finite presentation is not added to this second statement.

The first lemma is a small conversion of Mathlib's
`PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation` and the
closed-set/ideal correspondence, not a new proof of Chevalley's theorem. The second
reuses `Module.FaithfullyFlat.of_comap_surjective`,
`PrimeSpectrum.nontrivial_iff_mem_rangeComap`, residue-field functoriality and tensor
base-change cancellation. The inspected Mathlib owners expose those components,
not this ideal-controlled base-change interface. The standalone upstream
`nontrivial_tensor_of_field` helper is replaced by direct use of Mathlib's existing
`Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right`.

Only public helper names, explicit imports, and these implementation details change:
the residue-field map's definitional compatibility is given directly, the needed
fibre nontriviality is made an explicit local instance, and tensor cancellation is
root-qualified. No new algebraic hypothesis, global instance, axiom, heartbeat
extension or linter suppression is introduced. The pinned source file has no
individual row in the retained upstream ATTRIBUTION; all existing notices continue
to apply. Additional style changes replace three `haveI` bindings with `have` and one
`letI` with `let`, preserving the local types and values.

## Relocated flatness proofs

The following names under `SchemeTheory/RingTheory/Flat/` are the new proof
owners; the old AC paths become import-only compatibility facades. All existing
declaration names, including historical implementation namespaces, and all proof
bodies are preserved. Only their local imports are redirected. Namespace spelling
does not create a reverse library dependency.

- `RingTheory/Flat/LocalCriterion.lean` moves `AlgebraicCurves/Foundations/CommutativeAlgebra/Module_flat_of_comap_maximalIdeal_rTensor_injective.lean`; [fixed proof source](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean)
- `RingTheory/Flat/GenericFlatness.lean` moves `AlgebraicCurves/Foundations/CommutativeAlgebra/Module_Flat_exists_ne_zero_flat_localization_tensorProduct.lean`; [fixed proof source](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.lean)
- `RingTheory/Flat/OpenLocus.lean` moves `AlgebraicCurves/Foundations/CommutativeAlgebra/Module_Flat_isOpen_setOf_flat_localization_atPrime.lean`; [fixed proof source](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_isOpen_setOf_flat_localization_atPrime.lean)
- `RingTheory/Flat/FiniteSubalgebraLocalization.lean` moves `AlgebraicCurves/Foundations/CommutativeAlgebra/Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.lean`; [fixed proof source](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.lean)
- `RingTheory/Flat/FiniteSubalgebra.lean` moves `AlgebraicCurves/Foundations/Algebra/Module_Flat_exists_fg_subalgebra_flat_tensorProduct.lean`; [fixed proof source](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.lean)

The two actual direct consumers outside this closed set are updated to import the
new owner directly:

- `AlgebraicCurves/Foundations/Algebra/Module_Flat_of_finitePresentation_of_forall_flat_residueField_tensorProduct.lean`
- `AlgebraicCurves/Geometry/Schemes/Flat_exists_fg_subalgebra_of_flat_pullback_snd.lean`

The existing AC topic aggregates continue to reach the old import-only facades.
`SchemeTheory.RingTheory.Flat.All` reaches all five new owners, and
`SchemeTheory.RingTheory.All` imports that topic aggregate. The descent aggregate
reaches both new descent leaves. The new common-library proof closure contains no
AC/JV import. Importing both an old facade and its new owner loads one proof copy.

## Source-side finiteness descent

- `RingTheory/Descent/FiniteType.lean`: [proof](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_FiniteType_of_faithfullyFlat_of_finitePresentation.lean), [original statement](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FiniteType_of_faithfullyFlat_of_finitePresentation.lean)
- `RingTheory/Descent/FinitePresentation.lean`: [proof](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_FinitePresentation_of_faithfullyFlat_of_finitePresentation.lean), [original statement](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FinitePresentation_of_faithfullyFlat_of_finitePresentation.lean)

The two upstream proofs repeat polynomial quotient/model and coefficient-lifting
code. The model equivalence and relation-ideal transport have one implementation
in the finite-type owner and are reused by the finite-presentation owner. Existing
Mathlib APIs replace the duplicated coefficient support and lifting helpers
(`MvPolynomial.coeffs`, `MvPolynomial.mem_range_map_iff_coeffs_subset`), tensor
inclusion-surjectivity helper (`Algebra.TensorProduct.includeRight_surjective`),
and finite-generation lifting helper
(`Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective`). The finite-presentation owner
reuses the already qualified open-image lemmas instead of copying them.

Other adaptations are explicit leaf imports; current `TensorProduct.inductionOn` and local-instance syntax; explicit scalar-map operands; use of the canonical
residue-field algebra map rather than installing duplicate module structures; and
narrow proof rewrites instead of bare simplifier calls in the two new owners.
Generated `P2M.Util`, theorem-card wrappers, and upstream umbrella imports are not
included. The final public statements are checked against the original cards.
The tensor induction proofs have only the current `tmul` and `add` alternatives;
Mathlib derives the zero case internally. The helper `θ_injective` omits its
unused surjectivity hypothesis on `A' → A`: its proof uses the canonical
surjection `A' → A'/J`, supplied by `Ideal.Quotient.mk_surjective`. The single
caller is adjusted accordingly, and the final public theorem hypotheses are
unchanged. In `θ`, the quotient-lift proof supplies the actual element explicitly
to the ideal inclusion (`hJ (x := a) ha`), without hiding an unused variable.

The retained Apache 2.0 licence, NOTICE and ATTRIBUTION cover this batch. None of
the seven corresponding proof paths has an individual row in the pinned
ATTRIBUTION; this is not an attribution to Anthropic alone. Existing source notices
are retained verbatim in the relocated files and facades, and both new headers
link to their exact proof, statement and notices.

## AC foundation relocation on 2026-10-08

The following sources moved from AlgebraicCurves to SchemeTheory. Existing proof bodies,
public declaration names, namespaces, headers and upstream references are preserved.
This relocation does not resolve existing uncertainties about exact source-file
correspondence. In particular, LocalAlgebra, FreeModuleRegularScalar and
SmoothStalkNormality retain the unresolved attribution notes in their source headers.
The upstream NOTICE and ATTRIBUTION copies above are unchanged.

| Previous local module | Current local module |
|---|---|
| `AlgebraicCurves.Foundations.Algebra.Module_depth_quotSMulTop_succ_eq` | `SchemeTheory.RingTheory.ModuleDepthRegularQuotient` |
| `AlgebraicCurves.Foundations.Algebra.isSMulRegular_iff_of_free` | `SchemeTheory.RingTheory.FreeModuleRegularScalar` |
| `AlgebraicCurves.Foundations.CommutativeAlgebra.Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime` | `SchemeTheory.RingTheory.Descent.SmoothAtPrimeNormality` |
| `AlgebraicCurves.Foundations.CommutativeAlgebra.CohenMacaulay` | `SchemeTheory.RingTheory.CohenMacaulay` |
| `AlgebraicCurves.Foundations.CommutativeAlgebra.IsRegularLocalRing_depth_self_eq_ringKrullDim` | `SchemeTheory.RingTheory.RegularLocalDepth` |
| `AlgebraicCurves.Foundations.CommutativeAlgebra.IsRegularLocalRing_isDomain` | `SchemeTheory.RingTheory.RegularLocalDomain` |
| `AlgebraicCurves.Foundations.CommutativeAlgebra.LocalAlgebra` | `SchemeTheory.RingTheory.LocalAlgebra` |
| `AlgebraicCurves.Foundations.CommutativeAlgebra.Module_depth_le_ringKrullDim` | `SchemeTheory.RingTheory.ModuleDepthBound` |
| `AlgebraicCurves.Foundations.CommutativeAlgebra.Module_exists_mem_maximalIdeal_isSMulRegular_isSMulRegular` | `SchemeTheory.RingTheory.CommonRegularElement` |
| `AlgebraicCurves.Foundations.CommutativeAlgebra.Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing` | `SchemeTheory.RingTheory.RegularLocalDepthFreeness` |
| `AlgebraicCurves.Foundations.CommutativeAlgebra.RingTheory_Sequence_isWeaklyRegular_of_free` | `SchemeTheory.RingTheory.FreeModuleRegularSequence` |
| `AlgebraicCurves.Foundations.CommutativeAlgebra.RingTheory_Sequence_isWeaklyRegular_of_free_aux` | `SchemeTheory.RingTheory.FreeModuleRegularSequenceAux` |
| `AlgebraicCurves.Geometry.Curves.GeometricallyIntegral_of_isPullback_of_geometricallyIntegral` | `SchemeTheory.Morphisms.GeometricallyIntegralFieldDescent` |
| `AlgebraicCurves.Geometry.Curves.GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed` | `SchemeTheory.Morphisms.GeometricallyIrreducibleOverAlgebraicallyClosed` |
| `AlgebraicCurves.Geometry.Schemes.Smooth_isDomain_and_isIntegrallyClosed_stalk` | `SchemeTheory.LocalGeometry.SmoothStalkNormality` |

## Quasicoherent section localization

`Modules/AbelianSectionLocalization.lean` extracts and generalizes the finite-cover
kernel bound and compact-open gluing argument from
[the pinned section-localization proof](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial_of_qcqs.lean).
Its immediate local source is
`AlgebraicCurves/Geometry/Sheaves/Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial_of_qcqs.lean`.
The finite affine cover, maximum exponent, overlap annihilation, and two-open
sheaf gluing are retained. Powers of a supplied natural endomorphism replace
scalar multiplication inside the gluing core. This keeps the individual section
rings and module actions outside that proof.

`Modules/SectionLocalization.lean` supplies the actual multiplication
endomorphism and restriction maps. `Modules/QuasicoherentAffineLocalization.lean`
supplies affine localization from Mathlib's quasicoherence, `fromTildeΓ`, and
`IsLocalizedModule` owners. Thus the new endpoint applies to a quasicoherent
module on a quasi-compact, quasi-separated open. The original locally-trivial
public theorem and helper statements retain their exact types; three helper
proofs delegate to the shared owners with the existing affine supplier.

The full original notice is retained in the adapted core and compatibility
owner. The pinned ATTRIBUTION has no individual row for this upstream proof;
no earlier author list is inferred from that absence. The unchanged copied
NOTICE and ATTRIBUTION above remain applicable. The old compatibility owner's transparency override was removed. These results supply section localization;
they do not establish quasicoherent extension, global algebra approximation,
or proper base change.
