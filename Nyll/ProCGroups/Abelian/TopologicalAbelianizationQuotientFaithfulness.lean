/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality

/-!
# Faithfulness pulled back from quotient abelianizations

Trivial conjugation descends along a continuous homomorphism. Consequently,
faithfulness on the image pulls back for normal subgroups containing its kernel.
-/

namespace ProCGroups.Abelian

variable {G H : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
  (f : G →ₜ* H) (N : Subgroup G) [N.Normal] [(N.map f.toMonoidHom).Normal]

/-- Trivial conjugation on a normal subgroup's topological abelianization
remains trivial on its image under a continuous homomorphism. -/
theorem quotientConjugationTopologicalAbelianizationMap_mk_eq_one_map
    (g : G)
    (hg : quotientConjugationTopologicalAbelianizationMap N (QuotientGroup.mk' N g) = 1) :
    quotientConjugationTopologicalAbelianizationMap (N.map f.toMonoidHom)
      (QuotientGroup.mk' (N.map f.toMonoidHom) (f g)) = 1 := by
  let M := N.map f.toMonoidHom
  let r : N →ₜ* M :=
    { toMonoidHom :=
        { toFun x := ⟨f x, ⟨x, x.property, rfl⟩⟩
          map_one' := Subtype.ext (map_one f)
          map_mul' x y := Subtype.ext (map_mul f (x : G) (y : G)) }
      continuous_toFun := Continuous.subtype_mk
        (f.continuous.comp continuous_subtype_val) (fun x => ⟨x, x.property, rfl⟩) }
  apply MulEquiv.ext
  intro a
  obtain ⟨y, rfl⟩ := TopologicalAbelianization.surjective_mk M a
  obtain ⟨x, hx, hxy⟩ := y.property
  let z : N := ⟨x, hx⟩
  have hrz : r z = y := Subtype.ext hxy
  have hpoint : TopologicalAbelianization.mk N (MulAut.conjNormal g z) =
      TopologicalAbelianization.mk N z := by
    have h := congrArg (fun e : MulAut (TopologicalAbelianization N) =>
      e (TopologicalAbelianization.mk N z)) hg
    exact h
  have hconj : r (MulAut.conjNormal g z) = MulAut.conjNormal (f g) (r z) := by
    apply Subtype.ext
    change f (g * (z : G) * g⁻¹) = f g * f (z : G) * (f g)⁻¹
    rw [map_mul, map_mul, map_inv]
  have h := congrArg (TopologicalAbelianization.map r) hpoint
  rw [TopologicalAbelianization.map_apply_mk,
    TopologicalAbelianization.map_apply_mk, hconj, hrz] at h
  exact h

/-- Faithfulness on the image of a normal subgroup pulls back when the subgroup
contains the kernel of the ambient continuous homomorphism. -/
theorem quotientConjugationTopologicalAbelianizationMap_injective_of_map
    (hker : f.toMonoidHom.ker ≤ N)
    (hinj : Function.Injective
      (quotientConjugationTopologicalAbelianizationMap (N.map f.toMonoidHom))) :
    Function.Injective (quotientConjugationTopologicalAbelianizationMap N) := by
  apply (injective_iff_map_eq_one (quotientConjugationTopologicalAbelianizationMap N)).mpr
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  have hmap := quotientConjugationTopologicalAbelianizationMap_mk_eq_one_map f N g hq
  have heq : QuotientGroup.mk' (N.map f.toMonoidHom) (f g) = 1 := by
    apply hinj
    exact hmap.trans (map_one (quotientConjugationTopologicalAbelianizationMap
      (N.map f.toMonoidHom))).symm
  have hmem : f g ∈ N.map f.toMonoidHom :=
    (QuotientGroup.eq_one_iff (N := N.map f.toMonoidHom) (f g)).mp heq
  obtain ⟨x, hx, hfx⟩ := hmem
  change f x = f g at hfx
  have hcorrection : g * x⁻¹ ∈ f.toMonoidHom.ker := by
    change f (g * x⁻¹) = 1
    rw [map_mul, map_inv, hfx, mul_inv_cancel]
  have hg : g ∈ N := by
    have h := N.mul_mem (hker hcorrection) hx
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  exact (QuotientGroup.eq_one_iff (N := N) g).mpr hg

end ProCGroups.Abelian
