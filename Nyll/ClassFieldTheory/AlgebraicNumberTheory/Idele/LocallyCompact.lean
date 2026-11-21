/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Topology
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalField

/-!
# Local compactness of the idele group

The topology on the finite ideles is the restricted-product topology from
`AlgebraicNumberTheory.Idele.Topology`.  We prove local compactness by showing
that every finite completion is proper, that its integral unit group is
compact, and then applying the restricted-product theorem.
-/

@[expose] public section

open scoped NumberField RestrictedProduct Valued
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

/-- The correctly topologized finite idele group is locally compact. -/
instance finiteIdeleGroupLocallyCompactSpace :
    LocallyCompactSpace (FiniteIdeleGroup K) := by
  apply RestrictedProduct.locallyCompactSpace_of_group
    (fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
  exact Filter.Eventually.of_forall (isCompact_finiteLocalUnits K)

/-- The archimedean factor of the idele group is locally compact. -/
instance infiniteIdeleGroupLocallyCompactSpace :
    LocallyCompactSpace (InfiniteIdeleGroup K) :=
  inferInstance

/-- The adele-unit topology on the idele group is locally compact. -/
instance ideleGroupLocallyCompactSpace :
    LocallyCompactSpace (IdeleGroup K) :=
  let e := (IdeleGroup.componentsContinuousMulEquiv (K := K)).toHomeomorph
  e.isOpenEmbedding.locallyCompactSpace
