/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.AlgebraCoactionTransport
public import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleEqualizer
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Recovering an algebra from the canonical faithfully flat equalizer

The algebra equalizer is constructed from the actual Amitsur module equalizer.
A map into a scalar extension descends when its values are fixed by the
canonical coaction. If its scalar extension is bijective, faithful flatness
reflects bijectivity of the descended map.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Algebra.Descent

variable (S E A : Type u) [CommRing S] [CommRing E] [CommRing A]
variable [Algebra S E] [Algebra S A]

/-- The actual subalgebra fixed by the canonical scalar-extension coaction. -/
def canonicalInvariants : Subalgebra S (E ⊗[S] A) :=
  AlgHom.equalizer ((canonicalCoaction S E A).restrictScalars S)
    Algebra.TensorProduct.includeRight

/-- The coefficient inclusion lands in the canonical equalizer. -/
def canonicalInvariantsInclusion : A →ₐ[S] canonicalInvariants S E A :=
  (Algebra.TensorProduct.includeRight : A →ₐ[S] E ⊗[S] A).codRestrict
    (canonicalInvariants S E A) (fun a ↦ by
      change canonicalCoaction S E A ((1 : E) ⊗ₜ[S] a) =
        (1 : E) ⊗ₜ[S] ((1 : E) ⊗ₜ[S] a)
      rfl)

/-- Faithfully flat descent recovers the original algebra as the canonical
coaction's literal equalizer subalgebra. -/
def canonicalInvariantsEquiv [Module.FaithfullyFlat S E] :
    A ≃ₐ[S] canonicalInvariants S E A :=
  AlgEquiv.ofBijective (canonicalInvariantsInclusion S E A) (by
    constructor
    · intro a b hab
      apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := S) (B := E) A
      exact congrArg Subtype.val hab
    · intro z
      have hleft (w : E ⊗[S] A) :
          _root_.TensorProduct.assoc S E E A
              (EtaleFundamentalGroups.tensorProductDescentLeft
                (R := S) (S := E) (M := A) w) =
            canonicalCoaction S E A w := by
        induction w using TensorProduct.inductionOn with
        | tmul e a => rfl
        | add x y hx hy => simp only [map_add, hx, hy]
      have hright (w : E ⊗[S] A) :
          _root_.TensorProduct.assoc S E E A
              (EtaleFundamentalGroups.tensorProductDescentRight
                (R := S) (S := E) (M := A) w) =
            (1 : E) ⊗ₜ[S] w := by
        induction w using TensorProduct.inductionOn with
        | tmul e a => rfl
        | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
      have hz : canonicalCoaction S E A (z : E ⊗[S] A) =
          (1 : E) ⊗ₜ[S] (z : E ⊗[S] A) := z.property
      have heq :
          EtaleFundamentalGroups.tensorProductDescentLeft
              (R := S) (S := E) (M := A) (z : E ⊗[S] A) =
            EtaleFundamentalGroups.tensorProductDescentRight
              (R := S) (S := E) (M := A) (z : E ⊗[S] A) := by
        apply (_root_.TensorProduct.assoc S E E A).injective
        rw [hleft, hright]
        exact hz
      let w : LinearMap.eqLocus
          (EtaleFundamentalGroups.tensorProductDescentLeft
            (R := S) (S := E) (M := A))
          (EtaleFundamentalGroups.tensorProductDescentRight
            (R := S) (S := E) (M := A)) := ⟨z, heq⟩
      obtain ⟨a, ha⟩ :=
        (EtaleFundamentalGroups.tensorProductEqualizerEquiv
          (R := S) (S := E) (M := A)).surjective w
      have hval := congrArg
        (fun t : LinearMap.eqLocus
            (EtaleFundamentalGroups.tensorProductDescentLeft
              (R := S) (S := E) (M := A))
            (EtaleFundamentalGroups.tensorProductDescentRight
              (R := S) (S := E) (M := A)) ↦ (t : E ⊗[S] A)) ha
      refine ⟨a, Subtype.ext ?_⟩
      change (1 : E) ⊗ₜ[S] a = (z : E ⊗[S] A)
      exact (EtaleFundamentalGroups.tensorProductEqualizerEquiv_apply
        (R := S) (S := E) a).symm.trans hval)

variable (D : Type u) [CommRing D] [Algebra S D]

/-- Descend a concrete algebra map whose values satisfy the canonical
coaction relation, using the faithfully flat equalizer. -/
def descendCanonicalAlgHom [Module.FaithfullyFlat S E]
    (φ : D →ₐ[S] E ⊗[S] A)
    (hφ : ∀ d : D, canonicalCoaction S E A (φ d) = (1 : E) ⊗ₜ[S] φ d) :
    D →ₐ[S] A :=
  (canonicalInvariantsEquiv S E A).symm.toAlgHom.comp
    (φ.codRestrict (canonicalInvariants S E A) hφ)

/-- The descended map has exactly the prescribed coefficient inclusion. -/
theorem descendCanonicalAlgHom_spec [Module.FaithfullyFlat S E]
    (φ : D →ₐ[S] E ⊗[S] A)
    (hφ : ∀ d : D, canonicalCoaction S E A (φ d) = (1 : E) ⊗ₜ[S] φ d)
    (d : D) :
    (1 : E) ⊗ₜ[S] descendCanonicalAlgHom S E A D φ hφ d = φ d := by
  exact congrArg Subtype.val
    ((canonicalInvariantsEquiv S E A).apply_symm_apply
      (φ.codRestrict (canonicalInvariants S E A) hφ d))

/-- Bijectivity after faithfully flat scalar extension proves that the actual
equalizer-descended algebra map is an equivalence. -/
def descendCanonicalEquiv [Module.FaithfullyFlat S E]
    (φ : D →ₐ[S] E ⊗[S] A)
    (hφ : ∀ d : D, canonicalCoaction S E A (φ d) = (1 : E) ⊗ₜ[S] φ d)
    (hbij : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId E (E ⊗[S] A)) φ
        (fun _ _ ↦ Commute.all _ _))) :
    D ≃ₐ[S] A := by
  let f : D →ₐ[S] A := descendCanonicalAlgHom S E A D φ hφ
  apply AlgEquiv.ofBijective f
  apply (Module.FaithfullyFlat.lTensor_bijective_iff_bijective S E f.toLinearMap).mp
  have hmap : (f.toLinearMap.lTensor E : E ⊗[S] D → E ⊗[S] A) =
      Algebra.TensorProduct.lift (Algebra.ofId E (E ⊗[S] A)) φ
        (fun _ _ ↦ Commute.all _ _) := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul e d =>
      rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.lift_tmul,
        ← descendCanonicalAlgHom_spec S E A D φ hφ d]
      change e ⊗ₜ[S] f d =
        (e ⊗ₜ[S] (1 : A)) * ((1 : E) ⊗ₜ[S] f d)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hmap]
  exact hbij

end Algebra.Descent
