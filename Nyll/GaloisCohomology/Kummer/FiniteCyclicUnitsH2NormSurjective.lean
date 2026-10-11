/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.FiniteCyclicBaseUnitsH2
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Cyclic unit H² vanishes when the actual field norm is surjective

This uses the existing periodic H² calculation and base-unit representatives.
The norm hypothesis is the actual algebra norm, rather than a separate cohomology model.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

/-- Surjectivity of the field norm kills actual degree-two unit cohomology
for a finite cyclic Galois extension. -/
theorem finiteCyclicUnitsH2_eq_zero_of_norm_surjective
    (K M : Type) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] [IsCyclic Gal(M/K)]
    (hN : Function.Surjective (Algebra.norm K : M →* K))
    (c : groupCohomology (Rep.ofAlgebraAutOnUnits K M) 2) : c = 0 := by
  classical
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(M/K))
  have hmap := finiteCyclicH2_coefficientMap_eq_zero_of_norm
    (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) (Rep.ofAlgebraAutOnUnits K M)
    g hg (finiteGaloisBaseUnitsRepHom K M) (by
      intro a
      let u : Kˣ := (show Additive Kˣ from a.1).toMul
      obtain ⟨v, hv⟩ := hN (u : K)
      have hv0 : v ≠ 0 := by
        intro hz
        have hu : (u : K) = 0 := by
          rw [hz, Algebra.norm_zero] at hv
          exact hv.symm
        exact u.ne_zero hu
      refine ⟨Additive.ofMul (Units.mk0 v hv0), ?_⟩
      apply Units.ext
      change ((Additive.toMul
        ((Rep.ofAlgebraAutOnUnits K M).norm.hom
          (Additive.ofMul (Units.mk0 v hv0))) : Mˣ) : M) =
        algebraMap K M (u : K)
      exact (groupCohomology.norm_ofAlgebraAutOnUnits_eq
        (K := K) (L := M) (Units.mk0 v hv0)).trans
          (congrArg (algebraMap K M) hv))
  obtain ⟨b, hb⟩ := finiteCyclicBaseUnitsH2Map_surjective K M c
  rw [← hb]
  change groupCohomology.map (MonoidHom.id Gal(M/K))
    (finiteGaloisBaseUnitsRepHom K M) 2 b = 0
  rw [hmap]
  rfl

end ClassFieldTower.Cohomology
