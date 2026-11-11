/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Rep.Res
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.Tactic.Abel

/-!
# Descent of actual field-unit primitives

Hilbert 90 corrects a primitive by a principal one-coboundary. The corrected
primitive is constant on restriction fibres and takes values in the actual lower
field. This argument uses only additive units and their given automorphism action;
no choice of a cohomology coefficient ring or cohomology comparison is involved.
-/

@[expose] public section

universe u v

namespace ClassFieldTower.Cohomology

noncomputable section

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
variable (E : IntermediateField K L) [Normal K E]

/-- Inclusion of intermediate-field units in upper-field units, written additively. -/
def unitsInclusion :
    Rep.ofAlgebraAutOnUnits K E →+ Rep.ofAlgebraAutOnUnits K L :=
  (Units.map E.val.toMonoidHom).toAdditive

omit [Normal K E] in
private theorem unitsInclusion_injective : Function.Injective (unitsInclusion K L E) :=
  Units.map_injective E.val.injective

/-- Inclusion of units commutes with restriction of Galois automorphisms. -/
theorem unitsInclusion_equivariant (σ : Gal(L/K)) (a : Rep.ofAlgebraAutOnUnits K E) :
    unitsInclusion K L E ((Rep.ofAlgebraAutOnUnits K E).ρ
      (AlgEquiv.restrictNormalHom E σ) a) =
      (Rep.ofAlgebraAutOnUnits K L).ρ σ (unitsInclusion K L E a) := by
  apply Units.ext
  exact (σ.restrictNormal_commutes E ((show Additive Eˣ from a).toMul : E))

private theorem restrictNormal_restrictScalars (τ : Gal(L/E)) :
    AlgEquiv.restrictNormalHom E (τ.restrictScalars K) = 1 := by
  ext a
  change (((τ.restrictScalars K).restrictNormal E a) : L) = (a : L)
  exact ((τ.restrictScalars K).restrictNormal_commutes E a).trans (τ.commutes a)

omit [Normal K E] in
private theorem unitsInclusion_relative_fixed (τ : Gal(L/E)) (a : Rep.ofAlgebraAutOnUnits K E) :
    (Rep.ofAlgebraAutOnUnits K L).ρ (τ.restrictScalars K) (unitsInclusion K L E a) =
      unitsInclusion K L E a := by
  apply Units.ext
  exact τ.commutes ((show Additive Eˣ from a).toMul : E)

private theorem exists_relativeAut_of_restrictNormal_eq_one
    (σ : Gal(L/K)) (hσ : AlgEquiv.restrictNormalHom E σ = 1) :
    ∃ τ : Gal(L/E), τ.restrictScalars K = σ := by
  have hmem : σ ∈ E.fixingSubgroup := by
    rw [← E.restrictNormalHom_ker]
    exact hσ
  exact ⟨E.fixingSubgroupEquiv ⟨σ, hmem⟩, rfl⟩

variable [FiniteDimensional K L] [IsGalois K L]

omit [Normal K E] in
private theorem exists_unitsInclusion_eq_of_fixed (a : Rep.ofAlgebraAutOnUnits K L)
    (ha : ∀ τ : Gal(L/E), (Rep.ofAlgebraAutOnUnits K L).ρ (τ.restrictScalars K) a = a) :
    ∃ b : Rep.ofAlgebraAutOnUnits K E, unitsInclusion K L E b = a := by
  have hfix : ∀ τ : Gal(L/E),
      τ ((show Additive Lˣ from a).toMul : L) = ((show Additive Lˣ from a).toMul : L) := by
    intro τ
    exact congrArg Units.val (ha τ)
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := E) (E := L)
    ((show Additive Lˣ from a).toMul : L)).mpr hfix
  have hb0 : b ≠ 0 := by
    intro h
    apply Units.ne_zero (show Additive Lˣ from a).toMul
    rw [← hb, h, map_zero]
  refine ⟨Additive.ofMul (Units.mk0 b hb0), ?_⟩
  apply Units.ext
  exact hb

omit [IsGalois K L] in
private theorem exists_primitive_constant_on_relativeAut
    (c : Gal(E/K) × Gal(E/K) → Rep.ofAlgebraAutOnUnits K E)
    (b : Gal(L/K) → Rep.ofAlgebraAutOnUnits K L)
    (hb : ∀ σ τ : Gal(L/K),
      (Rep.ofAlgebraAutOnUnits K L).ρ σ (b τ) - b (σ * τ) + b σ =
        unitsInclusion K L E
          (c (AlgEquiv.restrictNormalHom E σ, AlgEquiv.restrictNormalHom E τ))) :
    ∃ b' : Gal(L/K) → Rep.ofAlgebraAutOnUnits K L,
      (∀ σ τ : Gal(L/K),
        (Rep.ofAlgebraAutOnUnits K L).ρ σ (b' τ) - b' (σ * τ) + b' σ =
          unitsInclusion K L E
            (c (AlgEquiv.restrictNormalHom E σ, AlgEquiv.restrictNormalHom E τ))) ∧
      ∀ τ : Gal(L/E), b' (τ.restrictScalars K) = b' 1 := by
  have h0 : b 1 = unitsInclusion K L E (c (1, 1)) := by
    simpa only [map_one, Module.End.one_apply, one_mul, sub_self, zero_add] using hb 1 1
  have hfixed (τ : Gal(L/E)) :
      (Rep.ofAlgebraAutOnUnits K L).ρ (τ.restrictScalars K) (b 1) = b 1 := by
    rw [h0, unitsInclusion_relative_fixed]
  let f : Gal(L/E) → Lˣ := fun τ ↦ (show Additive Lˣ from b (τ.restrictScalars K) - b 1).toMul
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro σ τ
    change b ((σ * τ).restrictScalars K) - b 1 =
      (Rep.ofAlgebraAutOnUnits K L).ρ (σ.restrictScalars K) (b (τ.restrictScalars K) - b 1) +
        (b (σ.restrictScalars K) - b 1)
    have h := hb (σ.restrictScalars K) (τ.restrictScalars K)
    rw [restrictNormal_restrictScalars, restrictNormal_restrictScalars, ← h0] at h
    change (Rep.ofAlgebraAutOnUnits K L).ρ (σ.restrictScalars K) (b (τ.restrictScalars K)) -
      b ((σ * τ).restrictScalars K) + b (σ.restrictScalars K) = b 1 at h
    have heq : b ((σ * τ).restrictScalars K) =
        (Rep.ofAlgebraAutOnUnits K L).ρ (σ.restrictScalars K) (b (τ.restrictScalars K)) +
          b (σ.restrictScalars K) - b 1 := by
      rw [← h]
      abel
    rw [heq, map_sub, hfixed]
    abel
  obtain ⟨β, hβ⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  let βa : Rep.ofAlgebraAutOnUnits K L := Additive.ofMul β
  let b' : Gal(L/K) → Rep.ofAlgebraAutOnUnits K L :=
    fun σ => b σ - ((Rep.ofAlgebraAutOnUnits K L).ρ σ βa - βa)
  have hd (σ τ : Gal(L/K)) :
      (Rep.ofAlgebraAutOnUnits K L).ρ σ (b' τ) - b' (σ * τ) + b' σ =
        (Rep.ofAlgebraAutOnUnits K L).ρ σ (b τ) - b (σ * τ) + b σ := by
    change (Rep.ofAlgebraAutOnUnits K L).ρ σ
        (b τ - ((Rep.ofAlgebraAutOnUnits K L).ρ τ βa - βa)) -
      (b (σ * τ) - ((Rep.ofAlgebraAutOnUnits K L).ρ (σ * τ) βa - βa)) +
      (b σ - ((Rep.ofAlgebraAutOnUnits K L).ρ σ βa - βa)) = _
    rw [map_sub, map_sub, map_mul, Module.End.mul_apply]
    abel
  refine ⟨b', ?_, ?_⟩
  · intro σ τ
    exact (hd σ τ).trans (hb σ τ)
  · intro τ
    have hβ' : (Rep.ofAlgebraAutOnUnits K L).ρ (τ.restrictScalars K) βa - βa =
        b (τ.restrictScalars K) - b 1 := hβ τ
    change b (τ.restrictScalars K) -
        ((Rep.ofAlgebraAutOnUnits K L).ρ (τ.restrictScalars K) βa - βa) =
      b 1 - ((Rep.ofAlgebraAutOnUnits K L).ρ 1 βa - βa)
    rw [hβ', map_one, Module.End.one_apply]
    abel

private theorem exists_lower_primitive
    (c : Gal(E/K) × Gal(E/K) → Rep.ofAlgebraAutOnUnits K E)
    (hc_snd : ∀ σ : Gal(E/K),
      c (σ, 1) = (Rep.ofAlgebraAutOnUnits K E).ρ σ (c (1, 1)))
    (hc_fst : ∀ σ : Gal(E/K), c (1, σ) = c (1, 1))
    (b : Gal(L/K) → Rep.ofAlgebraAutOnUnits K L)
    (hb : ∀ σ τ : Gal(L/K),
      (Rep.ofAlgebraAutOnUnits K L).ρ σ (b τ) - b (σ * τ) + b σ =
        unitsInclusion K L E
          (c (AlgEquiv.restrictNormalHom E σ, AlgEquiv.restrictNormalHom E τ)))
    (hn : ∀ τ : Gal(L/E), b (τ.restrictScalars K) = b 1) :
    ∃ a : Gal(E/K) → Rep.ofAlgebraAutOnUnits K E,
      ∀ σ τ : Gal(E/K),
        (Rep.ofAlgebraAutOnUnits K E).ρ σ (a τ) - a (σ * τ) + a σ = c (σ, τ) := by
  have h0 : b 1 = unitsInclusion K L E (c (1, 1)) := by
    simpa only [map_one, Module.End.one_apply, one_mul, sub_self, zero_add] using hb 1 1
  have hright (σ : Gal(L/K)) (τ : Gal(L/E)) : b (σ * τ.restrictScalars K) = b σ := by
    have h := hb σ (τ.restrictScalars K)
    rw [restrictNormal_restrictScalars, hc_snd,
      unitsInclusion_equivariant, ← h0, hn] at h
    have h' : b σ = b (σ * τ.restrictScalars K) := by
      apply add_left_cancel (a := (Rep.ofAlgebraAutOnUnits K L).ρ σ (b 1))
      apply (sub_eq_iff_eq_add).mp
      simpa only [sub_add_eq_add_sub] using h
    exact h'.symm
  have hfiber (σ τ : Gal(L/K))
      (hστ : AlgEquiv.restrictNormalHom E σ = AlgEquiv.restrictNormalHom E τ) :
      b σ = b τ := by
    have hk : AlgEquiv.restrictNormalHom E (τ⁻¹ * σ) = 1 := by
      rw [map_mul, map_inv, hστ, inv_mul_cancel]
    obtain ⟨η, hη⟩ := exists_relativeAut_of_restrictNormal_eq_one K L E (τ⁻¹ * σ) hk
    calc
      b σ = b (τ * η.restrictScalars K) := by rw [hη, mul_inv_cancel_left]
      _ = b τ := hright τ η
  have hfixed (σ : Gal(L/K)) (τ : Gal(L/E)) :
      (Rep.ofAlgebraAutOnUnits K L).ρ (τ.restrictScalars K) (b σ) = b σ := by
    have h := hb (τ.restrictScalars K) σ
    rw [restrictNormal_restrictScalars, hc_fst,
      ← h0, hn] at h
    have heq : b (τ.restrictScalars K * σ) = b σ := by
      apply hfiber
      rw [map_mul, restrictNormal_restrictScalars, one_mul]
    rw [heq] at h
    exact sub_eq_zero.mp (add_right_cancel (h.trans (zero_add (b 1)).symm))
  have ha : ∀ σ : Gal(L/K), ∃ a : Rep.ofAlgebraAutOnUnits K E,
      unitsInclusion K L E a = b σ := fun σ ↦
    exists_unitsInclusion_eq_of_fixed K L E (b σ) (hfixed σ)
  choose a ha using ha
  let surj : Function.Surjective (AlgEquiv.restrictNormalHom E : Gal(L/K) → Gal(E/K)) :=
    AlgEquiv.restrictNormalHom_surjective L (F := K) (K₁ := E)
  let s : Gal(E/K) → Gal(L/K) := Function.surjInv surj
  let aE : Gal(E/K) → Rep.ofAlgebraAutOnUnits K E := fun σ ↦ a (s σ)
  have hdesc (σ : Gal(L/K)) :
      unitsInclusion K L E (aE (AlgEquiv.restrictNormalHom E σ)) = b σ := by
    change unitsInclusion K L E (a (s (AlgEquiv.restrictNormalHom E σ))) = b σ
    rw [ha]
    exact hfiber _ σ (Function.surjInv_eq surj _)
  refine ⟨aE, ?_⟩
  intro σE τE
  obtain ⟨σ, hσ⟩ := surj σE
  obtain ⟨τ, hτ⟩ := surj τE
  apply unitsInclusion_injective K L E
  rw [← hσ, ← hτ, map_add, map_sub, unitsInclusion_equivariant,
    hdesc, ← map_mul, hdesc, hdesc]
  simpa only [hσ, hτ] using hb σ τ

/-- A primitive of an inflated unit-valued cochain descends to the original
lower field after the Hilbert 90 correction. The two displayed identities are
precisely the degree-two cocycle identities involving the identity element. -/
theorem unitsPrimitiveDescends
    (c : Gal(E/K) × Gal(E/K) → Rep.ofAlgebraAutOnUnits K E)
    (hc_snd : ∀ σ : Gal(E/K),
      c (σ, 1) = (Rep.ofAlgebraAutOnUnits K E).ρ σ (c (1, 1)))
    (hc_fst : ∀ σ : Gal(E/K), c (1, σ) = c (1, 1))
    (b : Gal(L/K) → Rep.ofAlgebraAutOnUnits K L)
    (hb : ∀ σ τ : Gal(L/K),
      (Rep.ofAlgebraAutOnUnits K L).ρ σ (b τ) - b (σ * τ) + b σ =
        unitsInclusion K L E
          (c (AlgEquiv.restrictNormalHom E σ, AlgEquiv.restrictNormalHom E τ))) :
    ∃ a : Gal(E/K) → Rep.ofAlgebraAutOnUnits K E,
      ∀ σ τ : Gal(E/K),
        (Rep.ofAlgebraAutOnUnits K E).ρ σ (a τ) - a (σ * τ) + a σ = c (σ, τ) := by
  obtain ⟨b', hb', hn⟩ := exists_primitive_constant_on_relativeAut K L E c b hb
  exact exists_lower_primitive K L E c hc_snd hc_fst b' hb' hn

end
end ClassFieldTower.Cohomology
