/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.EtaleFieldPointGlobalBound
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.SetTheory.Cardinal.Finite


/-!
# Uniform bounds for affine étale geometric fibers

For an étale map between spectra, one natural number bounds the actual
carrier of every pullback to the spectrum of a separably closed field.
The field and its map to the base are chosen after the bound.

The proof uses the existing uniform bound on field-valued algebra maps.
Every point of the étale pullback has a rational section through it, and
its first projection corresponds to an algebra map by `Spec.homEquivAlgHom`.
The evaluation map is therefore surjective onto the actual pullback.
No tensor-product presentation or assumed point comparison is used.

This is the affine geometric-fiber supplier for the finite-refinement
argument of Stacks Project, Tag `09Z0`; the refinement itself remains open.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- All geometric fibers of an étale morphism between affine spectra have
one finite bound, independent of the separably closed field and its actual
map to the base. Finiteness is asserted as well as the `Nat.card` inequality. -/
theorem exists_uniform_geometricFiber_bound_spec
    {R S : CommRingCat.{u}} (f : Spec S ⟶ Spec R) [Etale f] :
    ∃ N : ℕ, ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ Spec R),
      Finite (pullback f s : Scheme.{u}) ∧
        Nat.card (pullback f s : Scheme.{u}) ≤ N := by
  obtain ⟨α, rfl⟩ := Spec.map_surjective f
  let : Algebra R S := α.hom.toAlgebra
  have : Algebra.Etale R S :=
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp
      (inferInstance : Etale (Spec.map α))).toAlgebra
  obtain ⟨N, hN⟩ := Algebra.Etale.exists_uniform_fieldHom_bound.{u, u, u}
    (R := R) (S := S)
  refine ⟨N, ?_⟩
  intro Ω _ _ s
  obtain ⟨β, rfl⟩ := Spec.map_surjective s
  let : Algebra R Ω := β.hom.toAlgebra
  let I := {g : Spec (CommRingCat.of Ω) ⟶ Spec S // g ≫ Spec.map α = Spec.map β}
  let e : I ≃ (S →ₐ[R] Ω) := Spec.homEquivAlgHom (R := R) (A := S) (B := Ω)
  have : Finite (S →ₐ[R] Ω) := (hN Ω).1
  have : Finite I := Finite.of_injective e e.injective
  let l (g : I) : Spec (CommRingCat.of Ω) ⟶ pullback (Spec.map α) (Spec.map β) :=
    pullback.lift g.val (𝟙 _) (g.property.trans (Category.id_comp _).symm)
  let ev : I → (pullback (Spec.map α) (Spec.map β) : Scheme.{u}) :=
    fun g => l g default
  have hev : Function.Surjective ev := by
    intro y
    obtain ⟨a, ha, hay⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
      (pullback.snd (Spec.map α) (Spec.map β)) (𝟙 (Spec (CommRingCat.of Ω)))
      y (Subsingleton.elim _ _)
    have hg : (a ≫ pullback.fst (Spec.map α) (Spec.map β)) ≫ Spec.map α =
        Spec.map β := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ha, Category.id_comp]
    let g : I := ⟨a ≫ pullback.fst (Spec.map α) (Spec.map β), hg⟩
    have hl : l g = a := by
      apply pullback.hom_ext
      · exact pullback.lift_fst _ _ _
      · exact (pullback.lift_snd _ _ _).trans ha.symm
    refine ⟨g, ?_⟩
    exact (congrArg (fun k : Spec (CommRingCat.of Ω) ⟶
      pullback (Spec.map α) (Spec.map β) => k default) hl).trans hay
  refine ⟨Finite.of_surjective ev hev, ?_⟩
  calc
    Nat.card (pullback (Spec.map α) (Spec.map β) : Scheme.{u}) ≤ Nat.card I :=
      Nat.card_le_card_of_surjective ev hev
    _ = Nat.card (S →ₐ[R] Ω) := Nat.card_congr e
    _ ≤ N := (hN Ω).2

end AlgebraicGeometry.Etale
