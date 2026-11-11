/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Coinduced
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence

/-!
# Coinduction and the same coefficient-ring transport

Coinduction consists of the original equivariant functions. Restricting scalars through a ring
equivalence leaves their equivariance equation and right-translation action unchanged. The
comparison below records the actual pointwise maps used by integral Shapiro.
-/

@[expose] public section

noncomputable section

namespace Rep

open CategoryTheory

universe uR uS uG uH uA

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  {G : Type uG} {H : Type uH} [Monoid G] [Monoid H]
  (e : R ≃+* S) (φ : G →* H)

/-- Coefficient transport commutes with actual coinduction by keeping each equivariant function. -/
def coefficientRingCoindIso (A : Rep.{uA} S G) :
    (coefficientRingEquivalence e H).functor.obj (coind φ A) ≅
      coind φ ((coefficientRingEquivalence e G).functor.obj A) := by
  let X := (coefficientRingEquivalence e H).functor.obj (coind φ A)
  let Y := coind φ ((coefficientRingEquivalence e G).functor.obj A)
  let l : X ≃ₗ[R] Y := {
    toFun := fun f => ⟨f.1, f.2⟩
    invFun := fun f => ⟨f.1, f.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact Rep.mkIso (Representation.Equiv.mk l (by
    intro h
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    rfl))

/-- The coinduction comparison evaluates to the original equivariant function. -/
theorem coefficientRingCoindIso_hom_apply (A : Rep.{uA} S G)
    (f : (coefficientRingEquivalence e H).functor.obj (coind φ A)) (h : H) :
    ((coefficientRingCoindIso e φ A).hom f).1 h = f.1 h := rfl

/-- The inverse coinduction comparison also keeps the same function. -/
theorem coefficientRingCoindIso_inv_apply (A : Rep.{uA} S G)
    (f : coind φ ((coefficientRingEquivalence e G).functor.obj A)) (h : H) :
    ((coefficientRingCoindIso e φ A).inv f).1 h = f.1 h := rfl

/-- The pointwise coinduction comparison commutes with each original coefficient morphism. -/
def coefficientRingCoindNatIso :
    (coindFunctor S φ : Rep.{uA} S G ⥤ Rep.{max uH uA} S H) ⋙
        (coefficientRingEquivalence e H).functor ≅
      (coefficientRingEquivalence e G).functor ⋙ coindFunctor R φ :=
  NatIso.ofComponents (coefficientRingCoindIso e φ) (by
    intro A B f
    ext x
    rfl)

end Rep
