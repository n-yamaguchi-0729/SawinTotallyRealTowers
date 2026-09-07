import Mathlib.Combinatorics.Quiver.Arborescence
import Mathlib.Combinatorics.Quiver.ConnectedComponent

set_option autoImplicit false

/-!
# Reidemeister Schreier / Quiver

This module formalizes the quiver and arborescence tools used by the groupoid construction.
-/

universe u

namespace ReidemeisterSchreier

/-- Forgetting the orientation of a tree edge in a symmetrized quiver identifies the total arrows
of the tree with the original arrows covered by its symmetrification. -/
noncomputable def Quiver.coveredArrowEquivTotal
    {V : Type u} [Quiver V] (T : WideSubquiver (Quiver.Symmetrify V)) [Quiver.Arborescence T] :
    ↥(Quiver.wideSubquiverEquivSetTotal (Quiver.wideSubquiverSymmetrify T)) ≃ Quiver.Total T := by
  classical
  refine
    { toFun := fun e =>
        if hpos : T e.1.left e.1.right (Sum.inl e.1.hom) then
            { left := e.1.left
              right := e.1.right
              hom := ⟨Sum.inl e.1.hom, hpos⟩ }
        else
            { left := e.1.right
              right := e.1.left
              hom := ⟨Sum.inr e.1.hom, by
                rcases e.2 with h | h
                · exact False.elim (hpos h)
                · exact h⟩ }
      invFun := fun e =>
        match he : e.hom.1 with
        | Sum.inl f =>
            ⟨⟨e.left, e.right, f⟩, by
              change T e.left e.right (Sum.inl f) ∨ T e.right e.left (Sum.inr f)
              exact Or.inl (he ▸ e.hom.property)⟩
        | Sum.inr f =>
            ⟨⟨e.right, e.left, f⟩, by
              change T e.right e.left (Sum.inl f) ∨ T e.left e.right (Sum.inr f)
              exact Or.inr (he ▸ e.hom.property)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    apply Subtype.ext
    rcases e with ⟨⟨a, b, f⟩, hf⟩
    dsimp
    by_cases hpos : T a b (Sum.inl f)
    · rw [dif_pos hpos]
    · rcases hf with h | h
      · exact False.elim (hpos h)
      · rw [dif_neg hpos]
  · let edgeStep {a b : T} (e : a ⟶ b) :
        (default : Quiver.Path (Quiver.root T) a).length + 1 =
          (default : Quiver.Path (Quiver.root T) b).length := by
        have hpath :
            ((default : Quiver.Path (Quiver.root T) a).cons e :
              Quiver.Path (Quiver.root T) b) = default :=
          Subsingleton.elim _ _
        simpa only [Quiver.Path.length_cons] using congrArg Quiver.Path.length hpath
    intro e
    rcases e with ⟨a, b, e⟩
    cases e with
    | mk e he =>
        cases e with
        | inl f =>
            dsimp
            by_cases hpos : T a b (Sum.inl f)
            · simp only [hpos, ↓reduceDIte]
            · exact False.elim (hpos he)
        | inr f =>
            dsimp
            have hnot : ¬ T b a (Sum.inl f) := by
              intro hpos
              let e₁ : a ⟶ b := ⟨Sum.inr f, he⟩
              let e₂ : b ⟶ a := ⟨Sum.inl f, hpos⟩
              have h₁ := edgeStep e₁
              have h₂ := edgeStep e₂
              have hab :
                  (default : Quiver.Path (Quiver.root T) a).length <
                    (default : Quiver.Path (Quiver.root T) b).length := by
                rw [← h₁]
                exact Nat.lt_succ_self _
              have hba :
                  (default : Quiver.Path (Quiver.root T) b).length <
                    (default : Quiver.Path (Quiver.root T) a).length := by
                rw [← h₂]
                exact Nat.lt_succ_self _
              exact (Nat.lt_asymm hab hba).elim
            rw [dif_neg hnot]

namespace Quiver

/-- In an arborescence, the last edge of the unique path to a non-root vertex determines that
vertex, and every edge arises this way. -/
noncomputable def Arborescence.totalEquivNonRoot
    (V : Type u) [Quiver V] [Quiver.Arborescence V] :
    Quiver.Total V ≃ {v : V // v ≠ Quiver.root V} := by
  let f : Quiver.Total V → {v : V // v ≠ Quiver.root V} := fun e =>
    ⟨e.right, by
      intro hroot
      have hpath :
          ((default : Quiver.Path (Quiver.root V) e.left).cons
              (Quiver.homOfEq e.hom rfl hroot) :
            Quiver.Path (Quiver.root V) (Quiver.root V)) = default :=
        Subsingleton.elim _ _
      have hnil : (default : Quiver.Path (Quiver.root V) (Quiver.root V)) = Quiver.Path.nil :=
        Subsingleton.elim _ _
      exact Quiver.Path.cons_ne_nil
        (default : Quiver.Path (Quiver.root V) e.left)
        (Quiver.homOfEq e.hom rfl hroot) (hpath.trans hnil)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro e e' h
    cases e with
    | mk left right hom =>
        cases e' with
        | mk left' right' hom' =>
            cases h
            have hpath :
                ((default : Quiver.Path (Quiver.root V) left).cons hom :
                  Quiver.Path (Quiver.root V) right) =
                ((default : Quiver.Path (Quiver.root V) left').cons hom' :
                  Quiver.Path (Quiver.root V) right) :=
              Subsingleton.elim _ _
            have hleft : left = left' := Quiver.Path.obj_eq_of_cons_eq_cons hpath
            subst hleft
            have hhom : hom ≍ hom' := Quiver.Path.hom_heq_of_cons_eq_cons hpath
            cases hhom
            rfl
  · intro v
    let p : Quiver.Path (Quiver.root V) v.1 := default
    have hpne : p.length ≠ 0 := by
      intro hp0
      exact v.2 (Quiver.Path.eq_of_length_zero p hp0).symm
    rcases (Quiver.Path.length_ne_zero_iff_eq_cons p).mp hpne with ⟨c, p', e, hp⟩
    refine ⟨⟨c, v.1, e⟩, ?_⟩
    exact Subtype.ext rfl

end Quiver

end ReidemeisterSchreier
