/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianInertiaRestriction
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteInertiaStructure
import Nyll.ValuedFieldTheory.Valuation.ComapResidueCharP

/-!
# Surjectivity of finite wild inertia restriction

Over a Henselian base the actual inertia restriction is surjective. If upper
inertia is finite, ramification at both levels is the unique Sylow subgroup
for the residue characteristic. A surjective homomorphism carries a Sylow
subgroup onto a Sylow subgroup, so actual ramification restriction is also
surjective.
-/


namespace RamificationTheory.HilbertRamification.ValuationSubring

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Actual ramification restriction is surjective over a Henselian base when
upper inertia is finite. This applies to every finite Galois extension tower;
only normality of the intermediate extension is needed. -/
theorem galoisPullback_ramificationGroupMap_surjective_of_henselianRing
    [IsGalois K L]
    (V : _root_.ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (A : _root_.ValuationSubring L) [V.valuation.HasExtension A.valuation]
    [Finite (inertiaGroup K A)]
    (E : IntermediateField K L) [Normal K E]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    Function.Surjective
      (_root_.HilbertRamification.ValuationSubring.galoisPullback_ramificationGroupMap
        (RingHom.id K) E.val.toRingHom
        (by
          apply RingHom.ext
          intro a
          exact E.val.commutes a) A) := by
  let B : _root_.ValuationSubring E := A.comap E.val.toRingHom
  have : CharP (IsLocalRing.ResidueField B) p :=
    _root_.ValuationSubring.charP_residueField_comap A E.val.toRingHom p
  have hsquare : E.val.toRingHom.comp (algebraMap K E) =
      (algebraMap K L).comp (RingHom.id K) := by
    apply RingHom.ext
    intro a
    exact E.val.commutes a
  let ρ : inertiaGroup K A →* inertiaGroup K B :=
    _root_.HilbertRamification.ValuationSubring.galoisPullback_inertiaGroupMap
      (RingHom.id K) E.val.toRingHom hsquare A
  have hρ : Function.Surjective ρ :=
    galoisPullback_inertiaGroupMap_surjective_of_henselianRing V A E
  have : Finite (inertiaGroup K B) := Finite.of_surjective ρ hρ
  let P : Sylow p (inertiaGroup K A) := Sylow.nonempty.some
  have hP : (P : Subgroup (inertiaGroup K A)) = ramificationGroup K A :=
    sylow_eq_ramificationGroup_of_residueChar K A p P
  have hmap : (ramificationGroup K A).map ρ = ramificationGroup K B := by
    have hQ := sylow_eq_ramificationGroup_of_residueChar K B p (P.mapSurjective hρ)
    change (P : Subgroup (inertiaGroup K A)).map ρ = ramificationGroup K B at hQ
    rwa [hP] at hQ
  intro τ
  have hτ : (τ : inertiaGroup K B) ∈ (ramificationGroup K A).map ρ := by
    rw [hmap]
    exact τ.property
  obtain ⟨σ, hσ, hστ⟩ := Subgroup.mem_map.mp hτ
  refine ⟨⟨σ, hσ⟩, ?_⟩
  apply Subtype.ext
  exact hστ

end RamificationTheory.HilbertRamification.ValuationSubring
