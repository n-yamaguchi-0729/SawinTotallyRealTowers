import Mathlib.GroupTheory.Schreier
import ProCGroups.ReidemeisterSchreier.Discrete.OpenSubgroups.Generators
import ProCGroups.ReidemeisterSchreier.Discrete.OpenSubgroups.Words.NielsenSchreierCompat
import ProCGroups.ReidemeisterSchreier.FreeGroup.Automorphisms

set_option autoImplicit false

universe u

/-!
# Reidemeister Schreier / Discrete / Open Subgroups / Prefix Tree

This module constructs the Schreier prefix tree from a right transversal,
proves its positive and negative edge criteria, and relates its complement
edges to the nontrivial Schreier generators.
-/

namespace ReidemeisterSchreier.Discrete.OpenSubgroups

section SchreierPrefixTrees

open scoped Pointwise
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver _root_.ReidemeisterSchreier.FreeGroup

/--
The parent vertex of a nontrivial prefix-parent edge of a Schreier transversal again lies in the
transversal.
-/
theorem prefixParentEdge_mem_transversal {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    (t : T) (ht1 : (t : FreeGroup X) ≠ 1) :
    (FreeGroup.prefixParentEdgeOfNeOne (X := X) (t := (t : FreeGroup X)) ht1).parent ∈ T := by
  rw [FreeGroup.prefixParentEdgeOfNeOne_parent]
  exact prefixParent_mem_of_mem (X := X) hT t.property

/-- Every nonidentity transversal representative is reached from its prefix parent by an inverse-basis edge. -/
theorem exists_inverseBasis_edge_of_ne_one {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    (t : T) (ht1 : (t : FreeGroup X) ≠ 1) :
    ∃ x : X,
      letI := schreierTransversalRightCosetAction (X := X) hT
      (FreeGroup.inverseBasis X x •
          (⟨FreeGroup.prefixParent (t : FreeGroup X),
            prefixParent_mem_of_mem (X := X) hT t.property⟩ : T) = t) ∨
      (FreeGroup.inverseBasis X x • t =
          (⟨FreeGroup.prefixParent (t : FreeGroup X),
            prefixParent_mem_of_mem (X := X) hT t.property⟩ : T)) := by
  let edge := FreeGroup.prefixParentEdgeOfNeOne (X := X) (t := (t : FreeGroup X)) ht1
  have hlastEdge :
      FreeGroup.lastLetter? (t : FreeGroup X) = some edge.letter :=
    FreeGroup.prefixParentEdgeOfNeOne_lastLetter? (X := X) (t := (t : FreeGroup X)) ht1
  rcases hletter : edge.letter with ⟨x, b⟩
  cases b with
  | false =>
    have hlast? :
        FreeGroup.lastLetter? (t : FreeGroup X) = some ((x, false) : Internal.SignedLetter X) := by
      simpa [edge, hletter] using hlastEdge
    rcases (Internal.FreeGroupWord.FreeGroup.lastLetter?_eq_some_iff
      (g := (t : FreeGroup X)) (y := ((x, false) : Internal.SignedLetter X))).1 hlast? with
      ⟨hw, hlast⟩
    refine ⟨x, ?_⟩
    refine Or.inr ?_
    let p : T := ⟨FreeGroup.prefixParent (t : FreeGroup X),
      prefixParent_mem_of_mem (X := X) hT t.property⟩
    rw [FreeGroup.inverseBasis_apply,
      schreierTransversalRightCosetAction_smul (X := X) hT (FreeGroup.of x)⁻¹ t]
    simpa [p] using
      schreierRepresentative_eq_prefixParent_of_cancels (X := X) hT t.property hw hlast
  | true =>
    have hlast? :
        FreeGroup.lastLetter? (t : FreeGroup X) = some ((x, true) : Internal.SignedLetter X) := by
      simpa [edge, hletter] using hlastEdge
    rcases (Internal.FreeGroupWord.FreeGroup.lastLetter?_eq_some_iff
      (g := (t : FreeGroup X)) (y := ((x, true) : Internal.SignedLetter X))).1 hlast? with
      ⟨hw, hlast⟩
    refine ⟨x, ?_⟩
    refine Or.inl ?_
    let p : T := ⟨FreeGroup.prefixParent (t : FreeGroup X),
      prefixParent_mem_of_mem (X := X) hT t.property⟩
    rw [FreeGroup.inverseBasis_apply,
      schreierTransversalRightCosetAction_smul (X := X) hT (FreeGroup.of x)⁻¹ p]
    simpa [p] using
      schreierRepresentative_eq_of_prefixParent_last_pos (X := X) hT t.property hw hlast

/--
The canonical prefix tree on the Schreier transversal. Its unique incoming edge for a non-root
vertex is determined by the last letter of the reduced word of that vertex.
-/
noncomputable def schreierPrefixTree {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    WideSubquiver
      (Quiver.Symmetrify <| IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T)) := by
  exact fun a b =>
    { e |
        ∃ hw : FreeGroup.toWord (Subtype.val (show T from Sigma.snd b)) ≠ [],
          let tb : T := Sigma.snd b
          let pb : T := ⟨FreeGroup.prefixParent (tb : FreeGroup X),
            prefixParent_mem_of_mem (X := X) hT tb.property⟩
          (Sigma.snd a : T) = pb ∧
            match e with
            | Sum.inl g => (FreeGroup.toWord (tb : FreeGroup X)).getLast hw = (g.1, true)
            | Sum.inr g => (FreeGroup.toWord (tb : FreeGroup X)).getLast hw = (g.1, false) }

/--
Membership in the left branch of the Schreier prefix tree is equivalent to the displayed prefix
condition.
-/
theorem mem_schreierPrefixTree_inl_iff {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    {hT : IsRightSchreierTransversal (X := X) L T} :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    ∀ {a b : IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T)}
      {g : a ⟶ b},
      (Sum.inl g :
          @Quiver.Hom
            (Quiver.Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T)))
            inferInstance a b) ∈
          schreierPrefixTree (X := X) hT a b ↔
        ∃ hw : FreeGroup.toWord ((((show ActionCategory (FreeGroup X) T from b).back : T)) :
            FreeGroup X) ≠ [],
          let tb : T := (show ActionCategory (FreeGroup X) T from b).back
          let pb : T := ⟨FreeGroup.prefixParent (tb : FreeGroup X),
            prefixParent_mem_of_mem (X := X) hT tb.property⟩
          (show ActionCategory (FreeGroup X) T from a).back = pb ∧
            (FreeGroup.toWord (tb : FreeGroup X)).getLast hw = (g.1, true) := by
  intro a b g
  rfl

/--
Membership in the right branch of the Schreier prefix tree is equivalent to the displayed prefix
condition.
-/
theorem mem_schreierPrefixTree_inr_iff {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    {hT : IsRightSchreierTransversal (X := X) L T} :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    ∀ {a b : IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T)}
      {g : b ⟶ a},
      (Sum.inr g :
          @Quiver.Hom
            (Quiver.Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T)))
            inferInstance a b) ∈
          schreierPrefixTree (X := X) hT a b ↔
        ∃ hw : FreeGroup.toWord ((((show ActionCategory (FreeGroup X) T from b).back : T)) :
            FreeGroup X) ≠ [],
          let tb : T := (show ActionCategory (FreeGroup X) T from b).back
          let pb : T := ⟨FreeGroup.prefixParent (tb : FreeGroup X),
            prefixParent_mem_of_mem (X := X) hT tb.property⟩
          (show ActionCategory (FreeGroup X) T from a).back = pb ∧
            (FreeGroup.toWord (tb : FreeGroup X)).getLast hw = (g.1, false) := by
  intro a b g
  rfl

/-- A positive final letter determines the forward edge from the prefix parent in the Schreier tree. -/
theorem schreierPrefixTree_edge_of_last_pos {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    (t : T) {x : X} (hw : FreeGroup.toWord (t : FreeGroup X) ≠ [])
    (hlast : (FreeGroup.toWord (t : FreeGroup X)).getLast hw = (x, true)) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    let p : T := ⟨FreeGroup.prefixParent (t : FreeGroup X),
      prefixParent_mem_of_mem (X := X) hT t.property⟩
    let pA : IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) :=
      show IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) from
        ((p : T) : ActionCategory (FreeGroup X) T)
    let tA : IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) :=
      show IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) from
        ((t : T) : ActionCategory (FreeGroup X) T)
    ∃ e : @Quiver.Hom
        (Quiver.Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T)))
        inferInstance pA tA,
      e ∈ schreierPrefixTree (X := X) hT pA tA := by
  let p : T := ⟨FreeGroup.prefixParent (t : FreeGroup X),
    prefixParent_mem_of_mem (X := X) hT t.property⟩
  refine ⟨Sum.inl ⟨x, ?_⟩, ?_⟩
  · exact (schreierTransversalRightCosetAction_smul (X := X) hT
      (FreeGroup.inverseBasis X x) p).trans (by
        simpa only [FreeGroup.inverseBasis_apply, inv_inv, p, coe_back] using
          schreierRepresentative_eq_of_prefixParent_last_pos (X := X) hT t.property hw hlast)
  · exact (mem_schreierPrefixTree_inl_iff (X := X) (hT := hT)).2
      ⟨hw, rfl, hlast⟩

/-- A negative final letter determines the oppositely oriented edge from the prefix parent. -/
theorem schreierPrefixTree_edge_of_last_neg {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    (t : T) {x : X} (hw : FreeGroup.toWord (t : FreeGroup X) ≠ [])
    (hlast : (FreeGroup.toWord (t : FreeGroup X)).getLast hw = (x, false)) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    let p : T := ⟨FreeGroup.prefixParent (t : FreeGroup X),
      prefixParent_mem_of_mem (X := X) hT t.property⟩
    let pA : IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) :=
      show IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) from
        ((p : T) : ActionCategory (FreeGroup X) T)
    let tA : IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) :=
      show IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) from
        ((t : T) : ActionCategory (FreeGroup X) T)
    ∃ e : @Quiver.Hom
        (Quiver.Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T)))
        inferInstance pA tA,
      e ∈ schreierPrefixTree (X := X) hT pA tA := by
  let p : T := ⟨FreeGroup.prefixParent (t : FreeGroup X),
    prefixParent_mem_of_mem (X := X) hT t.property⟩
  refine ⟨Sum.inr ⟨x, ?_⟩, ?_⟩
  · exact (schreierTransversalRightCosetAction_smul (X := X) hT
      (FreeGroup.inverseBasis X x) t).trans (by
        simpa only [FreeGroup.inverseBasis_apply, inv_inv, p, coe_back] using
          schreierRepresentative_eq_prefixParent_of_cancels (X := X) hT t.property hw hlast)
  · exact (mem_schreierPrefixTree_inr_iff (X := X) (hT := hT)).2
      ⟨hw, rfl, hlast⟩

/-- Every nonroot vertex has a Schreier-tree edge from its canonical prefix parent. -/
theorem schreierPrefixTree_parent_edge_of_ne_one {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    (t : T) (ht1 : (t : FreeGroup X) ≠ 1) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    let p : T := ⟨FreeGroup.prefixParent (t : FreeGroup X),
      prefixParent_mem_of_mem (X := X) hT t.property⟩
    let pA : IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) :=
      show IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) from
        ((p : T) : ActionCategory (FreeGroup X) T)
    let tA : IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) :=
      show IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) from
        ((t : T) : ActionCategory (FreeGroup X) T)
    ∃ e : @Quiver.Hom
        (Quiver.Symmetrify (IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T)))
        inferInstance pA tA,
      e ∈ schreierPrefixTree (X := X) hT pA tA := by
  let edge := FreeGroup.prefixParentEdgeOfNeOne (X := X) (t := (t : FreeGroup X)) ht1
  have hlastEdge :
      FreeGroup.lastLetter? (t : FreeGroup X) = some edge.letter :=
    FreeGroup.prefixParentEdgeOfNeOne_lastLetter? (X := X) (t := (t : FreeGroup X)) ht1
  rcases hletter : edge.letter with ⟨x, b⟩
  cases b with
  | false =>
      have hlast? :
          FreeGroup.lastLetter? (t : FreeGroup X) = some ((x, false) : Internal.SignedLetter X)
              := by
        simpa [edge, hletter] using hlastEdge
      rcases (Internal.FreeGroupWord.FreeGroup.lastLetter?_eq_some_iff
        (g := (t : FreeGroup X)) (y := ((x, false) : Internal.SignedLetter X))).1 hlast? with
        ⟨hw, hlast⟩
      exact schreierPrefixTree_edge_of_last_neg (X := X) hT t hw hlast
  | true =>
      have hlast? :
          FreeGroup.lastLetter? (t : FreeGroup X) = some ((x, true) : Internal.SignedLetter X) := by
        simpa [edge, hletter] using hlastEdge
      rcases (Internal.FreeGroupWord.FreeGroup.lastLetter?_eq_some_iff
        (g := (t : FreeGroup X)) (y := ((x, true) : Internal.SignedLetter X))).1 hlast? with
        ⟨hw, hlast⟩
      exact schreierPrefixTree_edge_of_last_pos (X := X) hT t hw hlast

/-- Every Schreier-tree vertex is either the identity root or the target of an incoming edge. -/
lemma schreierPrefixTree_root_or_arrow {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    ∀ b : schreierPrefixTree (X := X) hT,
      b = ((((⟨(1 : FreeGroup X), hT.2.1⟩ : T) : ActionCategory (FreeGroup X) T) :
        schreierPrefixTree (X := X) hT)) ∨
      ∃ a, Nonempty (a ⟶ b) := by
  intro b
  let tb : T := Sigma.snd b
  by_cases hb1 : (tb : FreeGroup X) = 1
  · left
    cases b with
    | mk fst snd =>
        cases fst
        cases snd with
        | mk val hval =>
            have hb1' : val = 1 := by
              simpa [tb] using hb1
            cases hb1'
            rfl
  · right
    let pb : T := ⟨FreeGroup.prefixParent (tb : FreeGroup X),
      prefixParent_mem_of_mem (X := X) hT tb.property⟩
    refine ⟨⟨(), pb⟩, ?_⟩
    rcases schreierPrefixTree_parent_edge_of_ne_one (X := X) hT tb hb1 with ⟨e, he⟩
    exact ⟨⟨e, he⟩⟩

/-- Two Schreier-tree arrows with the same target have equal sources and agree as quiver edges. -/
lemma schreierPrefixTree_unique_arrow {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    ∀ ⦃a b c : schreierPrefixTree (X := X) hT⦄ (e : a ⟶ c) (f : b ⟶ c), a = b ∧ e ≍ f := by
  intro a b c e f
  rcases e with ⟨e0, hme⟩
  rcases f with ⟨f0, hmf⟩
  have hme0 := hme
  have hmf0 := hmf
  rcases hme with ⟨hwe, hsrca, hlast_e⟩
  rcases hmf with ⟨hwf, hsrcb, hlast_f⟩
  let tc : T := Sigma.snd c
  let pc : T := ⟨FreeGroup.prefixParent (tc : FreeGroup X),
    prefixParent_mem_of_mem (X := X) hT tc.property⟩
  have ha_back : (Sigma.snd a : T) = pc := by
    simpa [tc, pc] using hsrca
  have hb_back : (Sigma.snd b : T) = pc := by
    simpa [tc, pc] using hsrcb
  have hab : a = b :=
    Sigma.ext (Unit.ext (Sigma.fst a) (Sigma.fst b))
      (heq_of_eq (ha_back.trans hb_back.symm))
  refine ⟨hab, ?_⟩
  subst hab
  have hUnder : e0 = f0 := by
    cases e0 with
    | inl ge =>
        cases f0 with
        | inl gf =>
            have hxeq : ge.1 = gf.1 := by
              have hlast : (ge.1, true) = (gf.1, true) := by
                calc
                  (ge.1, true) = (FreeGroup.toWord (tc : FreeGroup X)).getLast hwe := by
                    simpa [tc] using hlast_e.symm
                  _ = (gf.1, true) := by simpa [tc] using hlast_f
              exact congrArg Prod.fst hlast
            have hgegf : ge = gf := Subtype.ext hxeq
            subst hgegf
            rfl
        | inr gf =>
            exfalso
            have hlast : (ge.1, true) = (gf.1, false) := by
              calc
                (ge.1, true) = (FreeGroup.toWord (tc : FreeGroup X)).getLast hwe := by
                  simpa [tc] using hlast_e.symm
                _ = (gf.1, false) := by simpa [tc] using hlast_f
            have : (true : Bool) = false := congrArg Prod.snd hlast
            cases this
    | inr ge =>
        cases f0 with
        | inl gf =>
            exfalso
            have hlast : (ge.1, false) = (gf.1, true) := by
              calc
                (ge.1, false) = (FreeGroup.toWord (tc : FreeGroup X)).getLast hwe := by
                  simpa [tc] using hlast_e.symm
                _ = (gf.1, true) := by simpa [tc] using hlast_f
            have : (false : Bool) = true := congrArg Prod.snd hlast
            cases this
        | inr gf =>
            have hxeq : ge.1 = gf.1 := by
              have hlast : (ge.1, false) = (gf.1, false) := by
                calc
                  (ge.1, false) = (FreeGroup.toWord (tc : FreeGroup X)).getLast hwe := by
                    simpa [tc] using hlast_e.symm
                  _ = (gf.1, false) := by simpa [tc] using hlast_f
              exact congrArg Prod.fst hlast
            have hgegf : ge = gf := Subtype.ext hxeq
            subst hgegf
            rfl
  have hEq : (⟨e0, hme0⟩ : a ⟶ c) = ⟨f0, hmf0⟩ := by
    apply Subtype.ext
    exact hUnder
  cases hEq
  rfl

/-- The reduced-word length strictly increases along every oriented Schreier-tree edge. -/
lemma schreierPrefixTree_height_lt {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    ∀ ⦃a b : schreierPrefixTree (X := X) hT⦄ (_ : a ⟶ b),
      (FreeGroup.toWord (((show ActionCategory (FreeGroup X) T from a).back : T) :
        FreeGroup X)).length <
      (FreeGroup.toWord (((show ActionCategory (FreeGroup X) T from b).back : T) :
        FreeGroup X)).length := by
  intro a b e
  rcases e with ⟨_, hmem⟩
  rcases hmem with ⟨hw, hsrc, _⟩
  let tb : T := Sigma.snd b
  have htb1 : (tb : FreeGroup X) ≠ 1 := by
    exact mt (FreeGroup.toWord_eq_nil_iff.mpr) hw
  have hlt :=
    Internal.FreeGroupWord.FreeGroup.toWord_length_prefixParent_lt (t := (tb : FreeGroup X)) htb1
  have hsrc' : (Sigma.snd a : T) =
      ⟨FreeGroup.prefixParent (tb : FreeGroup X),
        prefixParent_mem_of_mem (X := X) hT tb.property⟩ := by
    simpa [tb] using hsrc
  exact (congrArg (fun t : T => (FreeGroup.toWord (t : FreeGroup X)).length) hsrc').trans_lt hlt

/-- The prefix-closed Schreier quiver is an arborescence rooted at the identity representative. -/
noncomputable instance schreierPrefixTree_arborescence {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    Quiver.Arborescence (schreierPrefixTree (X := X) hT) := by
  refine Quiver.arborescenceMk (V := schreierPrefixTree (X := X) hT)
    ⟨(), ⟨(1 : FreeGroup X), hT.2.1⟩⟩
    (fun a =>
      (FreeGroup.toWord (Subtype.val (show T from Sigma.snd a))).length)
    ?_ ?_ ?_
  · intro a b e
    exact schreierPrefixTree_height_lt (X := X) hT e
  · intro a b c e f
    exact schreierPrefixTree_unique_arrow (X := X) hT e f
  · intro b
    exact schreierPrefixTree_root_or_arrow (X := X) hT b

/--
The classical Schreier generators attached to a right Schreier transversal algebraically
generate the subgroup.
-/
theorem closure_schreierGeneratorSet_eq_top {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    Subgroup.closure (schreierGeneratorSet (X := X) hT : Set L) = ⊤ := by
  let U : Set L :=
    (T * Set.range (FreeGroup.of : X → FreeGroup X)).image fun g =>
      ⟨g * (hT.1.toRightFun g : FreeGroup X)⁻¹, hT.1.mul_inv_toRightFun_mem g⟩
  have hUtop : Subgroup.closure U = ⊤ := by
    simpa [U] using
      (Subgroup.closure_mul_image_eq_top
        (H := L) (R := T) (S := Set.range (FreeGroup.of : X → FreeGroup X))
        hT.1 hT.2.1 (FreeGroup.closure_range_of X))
  have hSchreier_le :
      (schreierGeneratorSet (X := X) hT : Set L) ⊆ U := by
    intro z hz
    rcases hz with ⟨t, ht, x, rfl, _hz1⟩
    refine ⟨t * FreeGroup.of x, ⟨t, ht, FreeGroup.of x, ⟨x, rfl⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hU_le :
      U ⊆ insert 1 (schreierGeneratorSet (X := X) hT : Set L) := by
    intro z hz
    rcases hz with ⟨g, hg, rfl⟩
    rcases hg with ⟨t, ht, y, hy, rfl⟩
    rcases hy with ⟨x, rfl⟩
    by_cases hgen : schreierGenerator (X := X) hT t x = 1
    · left
      simpa [schreierGenerator, schreierRepresentative] using congrArg Subtype.val hgen
    · right
      exact ⟨t, ht, x, rfl, hgen⟩
  have hclosureU_le :
      Subgroup.closure U ≤
        Subgroup.closure (schreierGeneratorSet (X := X) hT : Set L) := by
    refine (Subgroup.closure_mono hU_le).trans ?_
    exact le_of_eq (Subgroup.closure_insert_one
      (schreierGeneratorSet (X := X) hT : Set L))
  apply top_unique
  calc
    ⊤ = Subgroup.closure U := hUtop.symm
    _ ≤ Subgroup.closure (schreierGeneratorSet (X := X) hT : Set L) := hclosureU_le

/--
The root vertex group in the Schreier action groupoid is canonically the subgroup L, via the
action label of an endomorphism.
-/
noncomputable def schreierRootEndMulEquiv {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    CategoryTheory.End
      (show ActionCategory (FreeGroup X) T from ((⟨(1 : FreeGroup X), hT.2.1⟩ : T) :
        ActionCategory (FreeGroup X) T)) ≃* L := by
  let rootT : T := ⟨(1 : FreeGroup X), hT.2.1⟩
  refine
    { toFun := fun g => ⟨g.1, ?_⟩
      invFun := fun l => ⟨l.1, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · let gF : FreeGroup X := g.1
    have hrep : schreierRepresentative (X := X) hT (gF⁻¹) = rootT := by
      simpa only [rootT, one_mul] using
        (schreierTransversalRightCosetAction_smul (X := X) hT gF rootT).symm.trans g.2
    have hmemInv : gF⁻¹ ∈ L := by
      have hm : gF⁻¹ *
          (((schreierRepresentative (X := X) hT (gF⁻¹) : T) : FreeGroup X))⁻¹ ∈ L :=
        hT.1.mul_inv_toRightFun_mem (gF⁻¹)
      simpa only [hrep, rootT, inv_one, mul_one] using hm
    simpa only [inv_inv] using L.inv_mem hmemInv
  · exact (schreierTransversalRightCosetAction_smul (X := X) hT l.1 rootT).trans
      (by simpa only [rootT, one_mul] using
        schreierRepresentative_eq_one_of_mem (X := X) hT (L.inv_mem l.2))
  · intro g
    rfl
  · intro l
    rfl
  · intro g h
    rfl

/--
The cocycle functor on the Schreier action groupoid. It sends a morphism \(a\to b\) labelled by
\(g\) to the subgroup element \(b g a^{-1}\), the inverse of the corresponding classical
Schreier generator.
-/
noncomputable def schreierLabelFunctor {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    ActionCategory (FreeGroup X) T ⥤ CategoryTheory.SingleObj L := by
  refine
    { obj := fun _ => ()
      map := fun {a b} p => ?_
      map_id := ?_
      map_comp := ?_ }
  · let g : FreeGroup X := p.1
    refine ⟨Subtype.val (show T from Sigma.snd b) * g *
      (Subtype.val (show T from Sigma.snd a))⁻¹, ?_⟩
    have hp : schreierRepresentative (X := X) hT
        ((Subtype.val (show T from Sigma.snd a)) * g⁻¹) = (Sigma.snd b : T) := by
      simpa only [CategoryTheory.ActionCategory.back] using
        (schreierTransversalRightCosetAction_smul (X := X) hT g
          (Sigma.snd a : T)).symm.trans p.2
    have hmem : (Subtype.val (show T from Sigma.snd a)) * g⁻¹ *
        (Subtype.val (show T from Sigma.snd b))⁻¹ ∈ L := by
      have hmem0 : (Subtype.val (show T from Sigma.snd a)) * g⁻¹ *
          (((schreierRepresentative (X := X) hT
            ((Subtype.val (show T from Sigma.snd a)) * g⁻¹) : T) : FreeGroup X))⁻¹ ∈ L := by
        simpa [schreierRepresentative] using
          hT.1.mul_inv_toRightFun_mem ((Subtype.val (show T from Sigma.snd a)) * g⁻¹)
      rw [hp] at hmem0
      exact hmem0
    simpa [mul_assoc] using L.inv_mem hmem
  · intro a
    apply Subtype.ext
    change ((Subtype.val (show T from Sigma.snd a)) * (1 : FreeGroup X) *
        (Subtype.val (show T from Sigma.snd a))⁻¹) = 1
    simp only [mul_one, mul_inv_cancel]
  · intro a b c p q
    let gp : FreeGroup X := p.1
    let gq : FreeGroup X := q.1
    apply Subtype.ext
    change ((Subtype.val (show T from Sigma.snd c)) * (gq * gp) *
        (Subtype.val (show T from Sigma.snd a))⁻¹) =
        (((Subtype.val (show T from Sigma.snd c)) * gq * (Subtype.val (show T from Sigma.snd b))⁻¹) *
          ((Subtype.val (show T from Sigma.snd b)) * gp * (Subtype.val (show T from Sigma.snd a))⁻¹))
    simp only [mul_assoc, inv_mul_cancel_left]

/-- The Schreier label functor respects the corresponding map of generators. -/
@[simp 900] theorem schreierLabelFunctor_map_of {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    ∀ {a b : ActionCategory (FreeGroup X) T}
      (e : ((show IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) from a) ⟶ b)),
      ((schreierLabelFunctor (X := X) hT).map (IsFreeGroupoid.of e) : L) =
        (schreierGenerator (X := X) hT (((a.back : T) : FreeGroup X)) e.1)⁻¹ := by
  intro a b e
  have hb : schreierRepresentative (X := X) hT
      ((Subtype.val (show T from Sigma.snd a)) * FreeGroup.of e.1) = (Sigma.snd b : T) := by
    simpa only [FreeGroup.inverseBasis_apply, inv_inv, CategoryTheory.ActionCategory.back] using
      (schreierTransversalRightCosetAction_smul (X := X) hT
        (FreeGroup.inverseBasis X e.1) (Sigma.snd a : T)).symm.trans e.property
  apply Subtype.ext
  change ((Subtype.val (show T from Sigma.snd b)) * (FreeGroup.of e.1)⁻¹ *
      (Subtype.val (show T from Sigma.snd a))⁻¹) =
      ((((schreierGenerator (X := X) hT (Subtype.val (show T from Sigma.snd a)) e.1 : L) :
        FreeGroup X))⁻¹)
  simp only [mul_assoc, schreierGenerator, hb, mul_inv_rev, inv_inv]

/-- The corresponding Schreier representative satisfies the stated membership criterion. -/
lemma schreierLabelFunctor_map_of_eq_one_of_mem_tree {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    ∀ {a b : ActionCategory (FreeGroup X) T}
      (e : ((show IsFreeGroupoid.Generators (ActionCategory (FreeGroup X) T) from a) ⟶ b)),
      e ∈ Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT) a b →
        (schreierLabelFunctor (X := X) hT).map (IsFreeGroupoid.of e) = (1 : L) := by
  intro a b e he
  refine (schreierLabelFunctor_map_of (X := X) hT e).trans ?_
  rcases he with htree | htree
  · rcases htree with ⟨hw, hsrc, hlast⟩
    let tb : T := Sigma.snd b
    have hsrc' : (Sigma.snd a : T) = ⟨FreeGroup.prefixParent (tb : FreeGroup X),
        prefixParent_mem_of_mem (X := X) hT tb.property⟩ := by
      simpa [tb] using hsrc
    have hgen :
        schreierGenerator (X := X) hT
          (FreeGroup.prefixParent (tb : FreeGroup X)) e.1 = (1 : L) := by
      exact schreierGenerator_eq_one_of_prefixParent_last_pos (X := X) hT
        (t := (tb : FreeGroup X)) tb.property hw hlast
    have hgen' :
        schreierGenerator (X := X) hT (Subtype.val (show T from Sigma.snd a)) e.1 = (1 : L) := by
      simpa [hsrc'] using hgen
    exact inv_eq_one.mpr hgen'
  · rcases htree with ⟨hw, hsrc, hlast⟩
    let ta : T := Sigma.snd a
    have hgen : schreierGenerator (X := X) hT (ta : FreeGroup X) e.1 = (1 : L) := by
      exact schreierGenerator_eq_one_of_cancels (X := X) hT
        (t := (ta : FreeGroup X)) ta.property hw hlast
    exact inv_eq_one.mpr (by simpa [ta] using hgen)

/-- The Schreier generator is trivial exactly in the corresponding subgroup-membership case. -/
lemma schreierGenerator_eq_one_implies_mem_prefixTree {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    ∀ {a b : CategoryTheory.ActionCategory (FreeGroup X) T}
      (e :
        (show IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T) from
          a) ⟶ b),
      schreierGenerator (X := X) hT (a.back : FreeGroup X) e.1 = 1 →
        e ∈ Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT) a b := by
  intro a b e hgen
  let ta : T := Sigma.snd a
  have hrep : schreierRepresentative (X := X) hT
      ((((ta : T) : FreeGroup X)) * FreeGroup.of e.1) = (Sigma.snd b : T) := by
    simpa only [FreeGroup.inverseBasis_apply, inv_inv, ta,
      CategoryTheory.ActionCategory.back] using
      (schreierTransversalRightCosetAction_smul (X := X) hT
        (FreeGroup.inverseBasis X e.1) (Sigma.snd a : T)).symm.trans e.property
  have hraw :
      (((schreierRepresentative (X := X) hT
          ((((ta : T) : FreeGroup X)) * FreeGroup.of e.1) : T) : FreeGroup X)) =
        ((ta : T) : FreeGroup X) * FreeGroup.of e.1 := by
    exact (schreierGenerator_eq_one_iff (X := X) (hT := hT)
      (t := ((ta : T) : FreeGroup X)) (x := e.1)).mp hgen
  by_cases hcancel : ∃ hw : FreeGroup.toWord ((ta : T) : FreeGroup X) ≠ [],
      (FreeGroup.toWord ((ta : T) : FreeGroup X)).getLast hw = (e.1, false)
  · rcases hcancel with ⟨hw, hlast⟩
    have hb : Subtype.val (show T from Sigma.snd b) =
        FreeGroup.prefixParent ((ta : T) : FreeGroup X) := by
      calc
        (Subtype.val (show T from Sigma.snd b))
            = (((schreierRepresentative (X := X) hT
                ((((ta : T) : FreeGroup X)) * FreeGroup.of e.1) : T) : FreeGroup X)) := by
                  exact congrArg Subtype.val hrep.symm
        _ = ((ta : T) : FreeGroup X) * FreeGroup.of e.1 := hraw
        _ = FreeGroup.prefixParent ((ta : T) : FreeGroup X) :=
              Internal.FreeGroupWord.FreeGroup.mul_of_eq_prefixParent_of_cancels
                ((ta : T) : FreeGroup X) e.1 hw hlast
    refine Or.inr ?_
    refine ⟨hw, ?_⟩
    constructor
    · apply Subtype.ext
      simpa [ta] using hb
    · simpa [ta] using hlast
  · have hword : FreeGroup.toWord (((ta : T) : FreeGroup X) * FreeGroup.of e.1) =
        FreeGroup.toWord ((ta : T) : FreeGroup X) ++ [(e.1, true)] :=
      Internal.FreeGroupWord.FreeGroup.toWord_mul_of_of_not_cancels
        ((ta : T) : FreeGroup X) e.1 hcancel
    have hb : (Subtype.val (show T from Sigma.snd b)) = ((ta : T) : FreeGroup X) * FreeGroup.of e.1 := by
      calc
        (Subtype.val (show T from Sigma.snd b))
            = (((schreierRepresentative (X := X) hT
                ((((ta : T) : FreeGroup X)) * FreeGroup.of e.1) : T) : FreeGroup X)) := by
                  exact congrArg Subtype.val hrep.symm
        _ = ((ta : T) : FreeGroup X) * FreeGroup.of e.1 := hraw
    have hbw : FreeGroup.toWord (Subtype.val (show T from Sigma.snd b)) =
        FreeGroup.toWord ((ta : T) : FreeGroup X) ++ [(e.1, true)] := by
      simpa [hb] using hword
    have hbw_ne : FreeGroup.toWord (Subtype.val (show T from Sigma.snd b)) ≠ [] := by
      rw [hbw]
      simp only [ne_eq, List.append_eq_nil_iff, FreeGroup.toWord_eq_nil_iff,
  List.cons_ne_self, and_false, not_false_eq_true]
    have hprefix : FreeGroup.prefixParent (Subtype.val (show T from Sigma.snd b)) =
        ((ta : T) : FreeGroup X) := by
      apply FreeGroup.toWord_injective
      rw [Internal.FreeGroupWord.FreeGroup.toWord_prefixParent, hbw]
      simp only [ne_eq, List.cons_ne_self, not_false_eq_true,
          List.dropLast_append_of_ne_nil,
  List.dropLast_singleton, List.append_nil]
    refine Or.inl ?_
    refine ⟨hbw_ne, ?_⟩
    constructor
    · apply Subtype.ext
      exact hprefix.symm
    · simp only [hbw, ne_eq, List.cons_ne_self, not_false_eq_true,
  List.getLast_append_of_ne_nil, List.getLast_singleton]

/--
A generator edge lies in the symmetrized prefix tree exactly when the associated Schreier
generator is trivial.
-/
theorem schreierGenerator_eq_one_iff_mem_prefixTree {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    {hT : IsRightSchreierTransversal (X := X) L T} :
    letI := schreierTransversalRightCosetAction (X := X) hT
    letI : IsFreeGroupoid (CategoryTheory.ActionCategory (FreeGroup X) T) :=
      FreeGroupBasis.actionGroupoidIsFree (FreeGroup.inverseBasis X)
    ∀ {a b : CategoryTheory.ActionCategory (FreeGroup X) T}
      {e :
        (show IsFreeGroupoid.Generators (CategoryTheory.ActionCategory (FreeGroup X) T) from
          a) ⟶ b},
      schreierGenerator (X := X) hT (a.back : FreeGroup X) e.1 = 1 ↔
        e ∈ Quiver.wideSubquiverSymmetrify (schreierPrefixTree (X := X) hT) a b := by
  intro a b e
  constructor
  · exact schreierGenerator_eq_one_implies_mem_prefixTree (X := X) hT e
  · intro he
    have hmap :=
      schreierLabelFunctor_map_of_eq_one_of_mem_tree (X := X) hT e he
    exact inv_eq_one.mp
      ((schreierLabelFunctor_map_of (X := X) hT e).symm.trans hmap)


end SchreierPrefixTrees

end ReidemeisterSchreier.Discrete.OpenSubgroups
