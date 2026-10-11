/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial_of_qcqs.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Tactic.Choose


/-!
# Section localization under an endomorphism

This extracts the finite-cover kernel bound and compact-open gluing argument
from the attributed source above. The same induction now uses powers of a
natural endomorphism of an abelian sheaf. Scalar multiplication is supplied
outside this core, so distinct rings of sections and their module actions
are not simultaneously materialized in the gluing proof.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.AbelianSectionLocalization

variable {X : Scheme.{u}} (F : X.Opensᵒᵖ ⥤ Ab.{u})
  (hF : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology (X : Type u)) F)
  (α : End F)

private def sheaf : TopCat.Sheaf Ab.{u} (TopCat.of (X : Type u)) := ⟨F, hF⟩

/-- The actual restriction map of the abelian presheaf. -/
abbrev res {V W : X.Opens} (h : V ≤ W) : F.obj (op W) → F.obj (op V) :=
  fun x => F.map (homOfLE h).op x

/-- Iteration of the fixed natural endomorphism on one open. -/
abbrev act (n : ℕ) (V : X.Opens) : F.obj (op V) → F.obj (op V) :=
  fun x => (α ^ n).app (op V) x

lemma res_res {V W Z : X.Opens} (hVW : V ≤ W) (hZV : Z ≤ V)
    (x : F.obj (op W)) : res F hZV (res F hVW x) = res F (hZV.trans hVW) x := by
  change (F.map (homOfLE hVW).op ≫ F.map (homOfLE hZV).op) x = _
  rw [← Functor.map_comp]
  rfl

lemma res_act {V W : X.Opens} (h : V ≤ W) (n : ℕ) (x : F.obj (op W)) :
    res F h (act F α n W x) = act F α n V (res F h x) := by
  have e := congrArg (fun k : F.obj (op W) ⟶ F.obj (op V) => k x)
    ((α ^ n).naturality (homOfLE h).op)
  exact e.symm

lemma act_add (m n : ℕ) (V : X.Opens) (x : F.obj (op V)) :
    act F α (m + n) V x = act F α m V (act F α n V x) := by
  rw [act, pow_add, End.mul_def, NatTrans.comp_app]
  rfl

lemma act_zero (n : ℕ) (V : X.Opens) : act F α n V 0 = 0 := map_zero _

lemma act_sub (n : ℕ) (V : X.Opens) (x y : F.obj (op V)) :
    act F α n V (x - y) = act F α n V x - act F α n V y := map_sub _ _ _

lemma res_zero {V W : X.Opens} (h : V ≤ W) : res F h 0 = 0 := map_zero _

lemma res_sub {V W : X.Opens} (h : V ≤ W) (x y : F.obj (op W)) :
    res F h (x - y) = res F h x - res F h y := map_sub _ _ _

/-- The two elementwise localization conditions for the actual restriction
map to the intersection with `D`. -/
def Clauses (D U : X.Opens) : Prop :=
  (∀ x : F.obj (op (U ⊓ D)), ∃ n : ℕ, ∃ y : F.obj (op U),
    res F inf_le_left y = act F α n (U ⊓ D) x) ∧
  (∀ y : F.obj (op U), res F (inf_le_left : U ⊓ D ≤ U) y = 0 →
    ∃ n : ℕ, act F α n U y = 0)

include hF in
lemma glue_two {S V : X.Opens} (a : F.obj (op S)) (b : F.obj (op V))
    (h : res F (inf_le_left : S ⊓ V ≤ S) a = res F inf_le_right b) :
    ∃ y : F.obj (op (S ⊔ V)), res F le_sup_left y = a ∧ res F le_sup_right y = b := by
  let W : Bool → X.Opens := fun c => cond c V S
  have hsup : S ⊔ V ≤ iSup W := sup_le (le_iSup W false) (le_iSup W true)
  let sf : ∀ c : Bool, F.obj (op (W c)) := fun c => match c with
    | false => a
    | true => b
  have hle : ∀ c : Bool, W c ≤ S ⊔ V := by
    intro c
    cases c
    · exact le_sup_left
    · exact le_sup_right
  have hcomp : TopCat.Presheaf.IsCompatible F W sf := by
    intro i j
    change F.map _ (sf i) = F.map _ (sf j)
    rw [Subsingleton.elim ((W i).infLELeft (W j)) (homOfLE inf_le_left),
      Subsingleton.elim ((W i).infLERight (W j)) (homOfLE inf_le_right)]
    cases i <;> cases j
    · rfl
    · exact h
    · change res F (inf_le_left : V ⊓ S ≤ V) b = res F inf_le_right a
      have hVS : V ⊓ S ≤ S ⊓ V := le_of_eq (inf_comm V S)
      rw [← res_res F inf_le_right hVS, ← res_res F inf_le_left hVS, h]
    · rfl
  obtain ⟨y, hy, _⟩ := (sheaf F hF).existsUnique_gluing' W (S ⊔ V)
    (fun c => homOfLE (hle c)) hsup sf hcomp
  exact ⟨y, hy false, hy true⟩

variable (D : X.Opens) (hlocal : ∀ V : X.affineOpens, Clauses F α D V.1)

include hF hlocal in
lemma ker_of_isCompact {U : X.Opens} (hU : IsCompact (U : Set X))
    (y : F.obj (op U)) (hy : res F (inf_le_left : U ⊓ D ≤ U) y = 0) :
    ∃ n : ℕ, act F α n U y = 0 := by
  classical
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  have he : U = ⨆ i : s, (i : X.Opens) := by
    simpa only [iSup_subtype] using e
  have hle (i : s) : (i : X.Opens) ≤ U := by
    rw [he]
    exact le_iSup (fun i : s => (i : X.Opens)) i
  have hstep (i : s) : ∃ n : ℕ, act F α n (i : X.Opens) (res F (hle i) y) = 0 := by
    apply (hlocal i.1).2
    have hd : (i : X.Opens) ⊓ D ≤ U ⊓ D := inf_le_inf (hle i) le_rfl
    rw [res_res, ← res_res F inf_le_left hd, hy, res_zero]
  choose n hn using hstep
  have := hs.to_subtype
  cases nonempty_fintype s
  refine ⟨Finset.univ.sup n, ?_⟩
  apply (sheaf F hF).eq_of_locally_eq' (fun i : s => (i : X.Opens)) U
    (fun i => homOfLE (hle i)) (le_of_eq he)
  intro i
  change res F (hle i) _ = res F (hle i) 0
  rw [res_zero, res_act]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n) (Finset.mem_univ i))
  rw [hk, Nat.add_comm, act_add, hn, act_zero]

include hF hlocal in
lemma surj_of_qcqs {U : X.Opens} (hU : IsCompact (U : Set X))
    (hqs : IsQuasiSeparated (U : Set X)) (x : F.obj (op (U ⊓ D))) :
    ∃ n : ℕ, ∃ y : F.obj (op U), res F inf_le_left y = act F α n (U ⊓ D) x := by
  revert hqs x
  refine compact_open_induction_on U hU ?_ ?_
  · intro _ x
    refine ⟨0, 0, ?_⟩
    apply (sheaf F hF).eq_of_locally_eq' (fun _ : Empty => (⊥ : X.Opens)) (⊥ ⊓ D)
      (fun i => i.elim) (inf_le_left.trans bot_le)
    intro i
    exact i.elim
  · intro S hS V IH hqs x
    have hqsS : IsQuasiSeparated (S : Set X) := hqs.of_subset Set.subset_union_left
    have hSg : S ⊓ D ≤ (S ⊔ V.1) ⊓ D := inf_le_inf le_sup_left le_rfl
    have hVg : V.1 ⊓ D ≤ (S ⊔ V.1) ⊓ D := inf_le_inf le_sup_right le_rfl
    obtain ⟨n₁, y₁, hy₁⟩ := IH hqsS (res F hSg x)
    obtain ⟨n₂, y₂, hy₂⟩ := (hlocal V).1 (res F hVg x)
    have hT : IsCompact ((S ⊓ V.1 : X.Opens) : Set X) :=
      hqs _ _ Set.subset_union_left S.2 hS Set.subset_union_right V.1.2 V.2.isCompact
    have hTS : S ⊓ V.1 ≤ S := inf_le_left
    have hTV : S ⊓ V.1 ≤ V.1 := inf_le_right
    have hDT : (S ⊓ V.1) ⊓ D ≤ S ⊓ V.1 := inf_le_left
    have hDS : (S ⊓ V.1) ⊓ D ≤ S ⊓ D := inf_le_inf inf_le_left le_rfl
    have hDV : (S ⊓ V.1) ⊓ D ≤ V.1 ⊓ D := inf_le_inf inf_le_right le_rfl
    let z : F.obj (op (S ⊓ V.1)) :=
      res F hTS (act F α n₂ S y₁) - res F hTV (act F α n₁ V.1 y₂)
    have hz : res F hDT z = 0 := by
      change res F hDT (res F hTS (act F α n₂ S y₁) -
        res F hTV (act F α n₁ V.1 y₂)) = 0
      rw [res_sub, res_res, res_res,
        ← res_res F inf_le_left hDS, ← res_res F inf_le_left hDV]
      simp only [res_act]
      rw [hy₁, hy₂]
      simp only [res_act, res_res, ← act_add]
      rw [Nat.add_comm n₂ n₁, sub_self]
    obtain ⟨m, hm⟩ := ker_of_isCompact F hF α D hlocal hT z hz
    have hagree : res F hTS (act F α (m + n₂) S y₁) =
        res F hTV (act F α (m + n₁) V.1 y₂) := by
      apply sub_eq_zero.mp
      simpa only [z, act_add, res_act, act_sub] using hm
    obtain ⟨y, hyS, hyV⟩ := glue_two F hF _ _ hagree
    refine ⟨m + n₁ + n₂, y, ?_⟩
    have hcov : (S ⊔ V.1) ⊓ D ≤ (S ⊓ D) ⊔ (V.1 ⊓ D) := by
      intro p hp
      rcases Opens.mem_sup.mp hp.1 with hpS | hpV
      · exact Opens.mem_sup.mpr (Or.inl ⟨hpS, hp.2⟩)
      · exact Opens.mem_sup.mpr (Or.inr ⟨hpV, hp.2⟩)
    apply (sheaf F hF).eq_of_locally_eq₂ (homOfLE hSg) (homOfLE hVg) hcov
    · change res F hSg (res F inf_le_left y) = res F hSg (act F α (m + n₁ + n₂) _ x)
      rw [res_res, ← res_res F le_sup_left inf_le_left, hyS, res_act, hy₁,
        res_act, ← act_add]
      rw [show m + n₂ + n₁ = m + n₁ + n₂ from Nat.add_right_comm m n₂ n₁]
    · change res F hVg (res F inf_le_left y) = res F hVg (act F α (m + n₁ + n₂) _ x)
      rw [res_res, ← res_res F le_sup_right inf_le_left, hyV, res_act, hy₂,
        res_act, ← act_add]

include hF hlocal in
/-- The existing compact-open gluing argument, with all local hypotheses
supplied on the actual affine charts. -/
theorem clauses_of_qcqs {U : X.Opens} (hU : IsCompact (U : Set X))
    (hqs : IsQuasiSeparated (U : Set X)) : Clauses F α D U :=
  ⟨surj_of_qcqs F hF α D hlocal hU hqs, ker_of_isCompact F hF α D hlocal hU⟩

end AlgebraicGeometry.Scheme.AbelianSectionLocalization
