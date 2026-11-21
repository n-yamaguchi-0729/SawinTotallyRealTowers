/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Induced

/-! # Evaluation of the actual induction-restriction adjunction -/

@[expose] public section

noncomputable section

universe r u v w

open CategoryTheory

namespace Rep

variable {R : Type r} {H : Type u} {G : Type v} [CommRing R] [Group H] [Group G]

/-- The morphism supplied by induction sends the actual class of `g ⊗ a`
to the original target action of `g⁻¹` on the original coefficient map. -/
theorem indResHomEquiv_symm_apply_mk (φ : H →* G)
    (A : Rep.{max r v w} R H) (B : Rep.{max r v w} R G)
    (f : A ⟶ res φ B) (g : G) (a : A) :
    ((indResHomEquiv.{max r v w} φ A B).symm f).hom
        (Representation.IndV.mk φ A.ρ g a) = B.ρ g⁻¹ (f.hom a) := by
  let t := (indResHomEquiv.{max r v w} φ A B).symm f
  have h1 : t.hom (Representation.IndV.mk φ A.ρ 1 a) = f.hom a :=
    congrArg (fun s : A ⟶ res φ B => s.hom a)
      ((indResHomEquiv.{max r v w} φ A B).apply_symm_apply f)
  have h := hom_comm_apply t g⁻¹ (Representation.IndV.mk φ A.ρ 1 a)
  rw [Representation.ind_mk, inv_inv, one_mul, h1] at h
  exact h

end Rep
