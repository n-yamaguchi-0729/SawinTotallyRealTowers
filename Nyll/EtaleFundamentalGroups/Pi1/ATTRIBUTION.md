# pi1 source attribution

The source repository is [chrisflav/pi1](https://github.com/chrisflav/pi1). The pinned
comparison revision is [`5c5c0171efc863ce9990171bdf46d7cb5fd582fb`](https://github.com/chrisflav/pi1/tree/5c5c0171efc863ce9990171bdf46d7cb5fd582fb).
It is licensed under Apache-2.0; [LICENSE](LICENSE) is an exact copy of the upstream
license. The reviewed upstream tree contains no `NOTICE` or `ATTRIBUTION` file.
The exact commit historically copied into NYLL is unknown. The current comparison
revision must not be presented as that original import commit.

Explicit upstream notices are reproduced below. Eight of the 25 upstream leaves
contain copyright and Authors notices; 17 do not. Missing notices do not establish
a holder. Git author records in [UPSTREAM.json](UPSTREAM.json) are historical
evidence only, not copyright determinations. Existing NYLL notices that additionally
cite original mathlib sources are retained and identified separately.

This inventory concerns pi1. Code from [Anthropic's Fermat's Last Theorem project](https://github.com/anthropics/fermats-last-theorem) has separate attribution and is
not included in this pi1 provenance inventory.

## Adaptations and NYLL additions

The ports preserve upstream credits while adapting imports and proofs to NYLL's
toolchain. Foundation source remains at depth 1 under `Nyll/SchemeTheory/Pi1`;
the EFG ports remain at depth 2. Relocation does not transfer mathematical ownership
or make a downstream import available to a foundation module.

NYLL-local contributions are recorded separately:

- `Nyll/SchemeTheory/Descent/EqualizerScalars.lean`: Nyll forward-map computation AlgHom.equalizerRestrictScalars_apply, split from the scalar-restriction comparison.
- `Nyll/SchemeTheory/FiniteEtale/Algebra/EtaleSplitting.lean`: Nyll etale-neighbourhood refinement Algebra.exists_etale_isFiniteSplit, stronger than the referenced upstream splitting construction.
- `Nyll/SchemeTheory/FiniteEtale/Forget/FiniteCoequalizers.lean`: Nyll simultaneous-map splitting adaptation and concrete coequalizer/descent construction; retained at the existing path with separate credits.
- `Nyll/EtaleFundamentalGroups/GeometricFiber/FundamentalGroup.lean`: Nyll completions of upstream Point.lean placeholders and dependent fiber-action/fundamental-group repairs; existing IsSepClosed and IsSepClosure assumptions preserved.

`SchemeTheory/Pi1/FiniteEtale/Geometry.lean` also retains the locally supplied
finite-spectrum and section-ring comparisons documented in its source and manifest.
These files contain adaptations; they are not claimed to match upstream bytes.

Upstream `Pi1/FundamentalGroup/Point.lean` contains 10 executable `sorry` tokens
(lines 118–121, 126, 131, 137, 181, 202 and 275) and one commented token (line 84).
The unfinished constructions concern `fiberObjEquivHom`, its naturality lemmas,
`fiberIsoCoyoneda`, continuity, `isField_of_isConnected` and `isGalois_of_isGalois`.
The completed NYLL implementations and their existing hypotheses are retained;
the upstream placeholders are not accepted as replacements.

Two upstream helper modules need no local copy: `RingTheory/StableProperties.lean`
is supplied by the current mathlib stable-equalizer and pushout-preservation APIs;
`Mathlib/RingTheory/TensorProduct/Basic.lean` is supplied by `commRight` and the
generalized tensor-product associator. Exact declarations and pinned source hashes
are listed in `UPSTREAM.json`.

Four previously mapped ports (`CategoryTheory/Over`, `Morphisms/ClosedImmersion`,
`Morphisms/FlatRank`, and `RingTheory/Finite`) also now use canonical mathlib APIs
directly. Their original provenance remains recorded below and in the manifest.
The maintained layout contains 21 adapted port files, four NYLL extension files,
and 13 aggregate modules. Six of the 25 upstream leaves are supplied by mathlib;
19 still have local adaptations. The retained `SmoothLocus`,
`GeometricIrreducibility`, `Smooth`, and finite-etale `Equalizer` ports also reuse
canonical localization, irreducibility, ideal, smoothness and idempotent APIs.
In total, 14 duplicate declarations (nine named declarations and five instances)
were removed, including seven in the four retired files. The exact replacements
are recorded in `UPSTREAM.json`. These counts do not measure proof completeness.

## File-by-file evidence

### [Pi1/FundamentalGroup/AffineAnd.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/AffineAnd.lean)

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Authors: Christian Merten
```

Original NYLL path: `Nyll/SchemeTheory/Affine/Property.lean`.

- `Nyll/SchemeTheory/Pi1/Affine/Property.lean` (adapted upstream port).

### [Pi1/FundamentalGroup/AffineColimits.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/AffineColimits.lean)

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Authors: Christian Merten
```

Original NYLL path: `Nyll/SchemeTheory/Affine/Over.lean`.

- `Nyll/SchemeTheory/Pi1/Affine/Over.lean` (adapted upstream port).

### [Pi1/FundamentalGroup/FiniteEtale.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/FiniteEtale.lean)

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Authors: Christian Merten
```

Original NYLL path: `Nyll/SchemeTheory/FiniteEtale/Basic.lean`.

- `Nyll/SchemeTheory/Pi1/FiniteEtale/Basic.lean` (adapted upstream port).

### [Pi1/FundamentalGroup/Galois.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/Galois.lean)

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Authors: Christian Merten
```

Original NYLL path: `Nyll/EtaleFundamentalGroups/FiniteEtale/GaloisCategory.lean`.

- `Nyll/EtaleFundamentalGroups/Pi1/FiniteEtale/GaloisCategory.lean` (adapted upstream port).

Original NYLL path: `Nyll/SchemeTheory/FiniteEtale/Geometry.lean`.

- `Nyll/SchemeTheory/Pi1/FiniteEtale/Geometry.lean` (adapted upstream port).

### [Pi1/FundamentalGroup/Point.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/Point.lean)

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Authors: Christian Merten
```

Original NYLL path: `Nyll/EtaleFundamentalGroups/GeometricFiber/FundamentalGroup.lean`.

- `Nyll/EtaleFundamentalGroups/Pi1/GeometricFiber/FieldPoints.lean` (adapted upstream port).
- `Nyll/EtaleFundamentalGroups/GeometricFiber/FundamentalGroup.lean` (nyll extension).

### [Pi1/FundamentalGroup/Rank.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/Rank.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/Morphisms/FlatRank.lean`.

- The duplicate local port `Nyll/SchemeTheory/Pi1/Morphisms/FlatRank.lean` was retired. Its consumers now use [`Mathlib.AlgebraicGeometry.Morphisms.FlatRank`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean) directly.

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Authors: Christian Merten
```

### [Pi1/Mathlib/AlgebraicGeometry/Limits.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/AlgebraicGeometry/Limits.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/Morphisms/ClosedImmersion.lean`.

- The duplicate local port `Nyll/SchemeTheory/Pi1/Morphisms/ClosedImmersion.lean` was retired. Its consumers now use [`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean) directly.

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Authors: Christian Merten
```

### [Pi1/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean)

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Authors: Christian Merten
```

Original NYLL path: `Nyll/SchemeTheory/Morphisms/Finite.lean`.

- `Nyll/SchemeTheory/Pi1/Morphisms/Finite.lean` (adapted upstream port).

### [Pi1/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/Morphisms/Flat.lean`.

- `Nyll/SchemeTheory/Pi1/Morphisms/Flat.lean` (adapted upstream port).

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Copyright (c) 2024 Christian Merten. All rights reserved.
Authors: Christian Merten, Andrew Yang
```

Additional source cited by the retained header: [original mathlib file](https://github.com/leanprover-community/mathlib4/blob/53f8a93a7739dd4eb33926f645811ebb6cee21bf/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean).

### [Pi1/Mathlib/CategoryTheory/Galois/IsFundamentalGroup.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/CategoryTheory/Galois/IsFundamentalGroup.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/EtaleFundamentalGroups/GaloisCategories/FundamentalGroup.lean`.

- `Nyll/EtaleFundamentalGroups/Pi1/GaloisCategories/FundamentalGroup.lean` (adapted upstream port).

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Authors: Christian Merten
```

### [Pi1/Mathlib/CategoryTheory/Limits/MorphismProperty.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/CategoryTheory/Limits/MorphismProperty.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/CategoryTheory/Over.lean`.

- The duplicate local port `Nyll/SchemeTheory/Pi1/CategoryTheory/Over.lean` was retired. Its consumers now use [`Mathlib.CategoryTheory.Limits.MorphismProperty`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Limits/MorphismProperty.lean) directly.

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Copyright (c) 2024 Christian Merten. All rights reserved.
Authors: Christian Merten
```

Additional source cited by the retained header: [original mathlib file](https://github.com/leanprover-community/mathlib4/blob/53f8a93a7739dd4eb33926f645811ebb6cee21bf/Mathlib/CategoryTheory/Limits/MorphismProperty.lean).

### [Pi1/Mathlib/RingTheory/Flat/Equalizer.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/Flat/Equalizer.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/Descent/FlatEqualizer.lean`.

- `Nyll/SchemeTheory/Pi1/Descent/FlatEqualizer.lean` (adapted upstream port).
- `Nyll/SchemeTheory/Pi1/Descent/EqualizerScalars.lean` (adapted upstream port).
- `Nyll/SchemeTheory/Descent/EqualizerScalars.lean` (nyll extension).

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Copyright (c) 2024 Christian Merten. All rights reserved.
Authors: Christian Merten
```

Additional source cited by the retained header: [original mathlib file](https://github.com/leanprover-community/mathlib4/blob/53f8a93a7739dd4eb33926f645811ebb6cee21bf/Mathlib/RingTheory/Flat/Equalizer.lean).

### [Pi1/Mathlib/RingTheory/Geometric.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/Geometric.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/Affine/GeometricIrreducibility.lean`.

- `Nyll/SchemeTheory/Pi1/Affine/GeometricIrreducibility.lean` (adapted upstream port).

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Authors: Christian Merten
```

### [Pi1/Mathlib/RingTheory/Ideal/Quotient/Operations.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/Ideal/Quotient/Operations.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/RingTheory/QuotientProducts.lean`.

- `Nyll/SchemeTheory/Pi1/RingTheory/QuotientProducts.lean` (adapted upstream port).

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Authors: Christian Merten
```

### [Pi1/Mathlib/RingTheory/RingHom/Etale.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/RingHom/Etale.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/Etale/RingHom.lean`.

- `Nyll/SchemeTheory/Pi1/Etale/RingHom.lean` (adapted upstream port).

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Authors: Christian Merten
```

Additional source cited by the retained header: [original mathlib file](https://github.com/leanprover-community/mathlib4/blob/53f8a93a7739dd4eb33926f645811ebb6cee21bf/Mathlib/RingTheory/RingHom/Etale.lean).

### [Pi1/Mathlib/RingTheory/RingHom/Finite.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/RingHom/Finite.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/RingTheory/Finite.lean`.

- The duplicate local port `Nyll/SchemeTheory/Pi1/RingTheory/Finite.lean` was retired. Its consumers now use [`Mathlib.RingTheory.Finiteness.Defs`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/Finiteness/Defs.lean) directly.

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Authors: Christian Merten
```

### [Pi1/Mathlib/RingTheory/RingHom/Smooth.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/RingHom/Smooth.lean)

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Authors: Christian Merten
```

Original NYLL path: `Nyll/SchemeTheory/Morphisms/Smooth.lean`.

- `Nyll/SchemeTheory/Pi1/Morphisms/Smooth.lean` (adapted upstream port).

### [Pi1/Mathlib/RingTheory/TensorProduct/Basic.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/TensorProduct/Basic.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Replaced by the current mathlib API described above and in `UPSTREAM.json`.

### [Pi1/RingTheory/FiniteEtale/Basic.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Basic.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/FiniteEtale/Algebra/Basic.lean`.

- `Nyll/SchemeTheory/Pi1/FiniteEtale/Algebra/Basic.lean` (adapted upstream port).

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Authors: Christian Merten
```

### [Pi1/RingTheory/FiniteEtale/Descent.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Descent.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/FiniteEtale/Algebra/Descent.lean`.

- `Nyll/SchemeTheory/Pi1/FiniteEtale/Algebra/Descent.lean` (adapted upstream port).

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Authors: Christian Merten
```

### [Pi1/RingTheory/FiniteEtale/Equalizer.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Equalizer.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/FiniteEtale/Algebra/Equalizer.lean`.

- `Nyll/SchemeTheory/Pi1/FiniteEtale/Algebra/Equalizer.lean` (adapted upstream port).

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Authors: Christian Merten
```

### [Pi1/RingTheory/KerTensor.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/KerTensor.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/FiniteEtale/Algebra/Splitting.lean`.

- `Nyll/SchemeTheory/Pi1/FiniteEtale/Algebra/Splitting.lean` (adapted upstream port).
- `Nyll/SchemeTheory/FiniteEtale/Algebra/EtaleSplitting.lean` (nyll extension).

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Authors: Christian Merten
```

Original NYLL path: `Nyll/SchemeTheory/FiniteEtale/Forget/FiniteCoequalizers.lean`.

- `Nyll/SchemeTheory/FiniteEtale/Forget/FiniteCoequalizers.lean` (nyll extension).

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Authors: Christian Merten
```

### [Pi1/RingTheory/Smooth/StandardSmoothSmooth.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/Smooth/StandardSmoothSmooth.lean)

```text
Copyright (c) 2024 Christian Merten. All rights reserved.
Authors: Christian Merten
```

Original NYLL path: `Nyll/SchemeTheory/Morphisms/SmoothLocus.lean`.

- `Nyll/SchemeTheory/Pi1/Morphisms/SmoothLocus.lean` (adapted upstream port).

### [Pi1/RingTheory/StableProperties.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/StableProperties.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Replaced by the current mathlib API described above and in `UPSTREAM.json`.

### [Pi1/RingTheory/Transcendence.lean](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/Transcendence.lean)

The reviewed upstream file has no explicit copyright or Authors notice.

Original NYLL path: `Nyll/SchemeTheory/FunctionFields/Transcendence.lean`.

- `Nyll/SchemeTheory/Pi1/FunctionFields/Transcendence.lean` (adapted upstream port).

Historical NYLL notices from the pre-refresh source (not headers found in this pi1 revision):

```text
Authors: Christian Merten
```

## Document authorship

The newly written provenance prose and manifest organization are Copyright (c)
2026 Naganori Yamaguchi, licensed under Apache-2.0. Authors: Naganori Yamaguchi
(assisted by OpenAI Codex), <https://github.com/n-yamaguchi-0729>. This credit applies
only to the local documentation, not to the upstream source or license.
