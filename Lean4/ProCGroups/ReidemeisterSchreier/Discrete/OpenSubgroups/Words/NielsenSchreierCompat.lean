import ProCGroups.ReidemeisterSchreier.Groupoid

set_option autoImplicit false

universe u

/-!
# Reidemeister Schreier / Discrete / Open Subgroups / Words / Nielsen Schreier Compat

This module connects the local word conventions with Mathlib's
Nielsen--Schreier action-groupoid basis and establishes the edge and back-edge
identities needed to transport that basis.
-/

namespace ReidemeisterSchreier.Discrete.OpenSubgroups

section NielsenSchreierCompat

open scoped Pointwise
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver _root_.FreeGroup

/--
An explicit free-group basis makes the corresponding action groupoid free with controlled
generator labels.
-/
@[reducible] noncomputable def FreeGroupBasis.actionGroupoidIsFree
    {ι G A : Type u} [Group G] [MulAction G A] (b : FreeGroupBasis ι G) :
    IsFreeGroupoid (ActionCategory G A) where
  quiverGenerators :=
    ⟨fun a b' => { i : ι // b i • a.back = b'.back }⟩
  of := fun (e : Subtype _) => ⟨b e, e.property⟩
  unique_lift := by
    intro X _ f
    let f' : ι → (A → X) ⋊[mulAutArrow] G := fun i =>
      ⟨fun a =>
          @f ⟨(), (b i)⁻¹ • a⟩ ⟨(), a⟩
            ⟨i, smul_inv_smul (b i) a⟩,
        b i⟩
    let F' : G →* (A → X) ⋊[mulAutArrow] G := b.lift f'
    have hF' : ∀ i, F' (b i) = f' i := congrFun (b.lift.left_inv f')
    refine ⟨uncurry F' ?_, ?_, ?_⟩
    · intro g
      suffices SemidirectProduct.rightHom.comp F' = MonoidHom.id G by
        exact DFunLike.ext_iff.mp this g
      apply b.ext_hom
      intro i
      rw [MonoidHom.comp_apply, hF' i]
      rfl
    · rintro ⟨⟨⟩, a : A⟩ ⟨⟨⟩, b'⟩ ⟨i, h : b i • a = b'⟩
      change (F' (b i)).left _ = _
      rw [hF' i]
      cases inv_smul_eq_iff.mpr h.symm
      rfl
    · intro E hE
      have hcurried : curry E = F' := by
        apply b.ext_hom
        intro i
        rw [hF' i]
        apply SemidirectProduct.ext
        · funext a
          exact hE ⟨(), (b i)⁻¹ • a⟩ ⟨(), a⟩ ⟨i, smul_inv_smul (b i) a⟩
        · rfl
      apply Functor.hext
      · intro
        apply Unit.ext
      · refine ActionCategory.cases ?_
        intro t g
        have hEval :
            (E.map (homOfPair (G := G) t g) : X) = (F' g).left t :=
          (curry_apply_left E g t).symm.trans
            (congrArg (fun φ : G →* (A → X) ⋊[mulAutArrow] G => (φ g).left t) hcurried)
        exact heq_of_eq hEval

/-- Two action-category objects are equal when their underlying points are equal. -/
lemma actionCategory_eq_of_back_eq {M X : Type u} [Monoid M] [MulAction M X]
    {u v : ActionCategory M X} (h : u.back = v.back) : u = v := by
  cases u
  cases v
  cases h
  rfl

end NielsenSchreierCompat

end ReidemeisterSchreier.Discrete.OpenSubgroups
