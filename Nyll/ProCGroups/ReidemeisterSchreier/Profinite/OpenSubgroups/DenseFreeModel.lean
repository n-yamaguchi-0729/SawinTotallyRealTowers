/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.WreathProducts
import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.OpenSubgroups.FreeBasis
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.FinitePermutationTargets

/-!
# Dense abstract free models of open subgroups

This module transports right-coset sections across a dense free-group lift,
proves that the preimage of an open subgroup remains dense, and applies the
discrete Nielsen--Schreier basis theorem to compute the abstract preimage
rank.  The result feeds the later pro-\(C\) completion argument.
-/

open Set
open scoped Topology Pointwise

namespace ReidemeisterSchreier
namespace Profinite

open ProCGroups
open ProCGroups.WreathProducts
open ReidemeisterSchreier.Discrete.OpenSubgroups

universe u v w


section RightQuotientTransport

open _root_.ReidemeisterSchreier.FreeGroup

variable {F : Type u} [Group F]
variable {P : Type v} [Group P]
variable {Y : Type w}

/-- The right relator map is compatible with comap of the open subgroup. -/
theorem rightRel_map_of_comap
    (π : F →* P) (βF : FreeGroup Y →* F) (β : FreeGroup Y →* P)
    (K : Subgroup P) (hβ : π.comp βF = β)
    {a b : FreeGroup Y}
    (hab : QuotientGroup.rightRel (Subgroup.comap β K) a b) :
    QuotientGroup.rightRel (Subgroup.comap π K) (βF a) (βF b) := by
  have ha : π (βF a) = β a := by
    simpa [MonoidHom.comp_apply] using congrArg (fun f : FreeGroup Y →* P => f a) hβ
  have hb : π (βF b) = β b := by
    simpa [MonoidHom.comp_apply] using congrArg (fun f : FreeGroup Y →* P => f b) hβ
  rw [QuotientGroup.rightRel_apply] at hab ⊢
  simpa only [Subgroup.mem_comap, map_mul, map_inv, ha, hb] using hab

/-- Transport right-coset classes along a homomorphism compatible with two subgroup preimages. -/
noncomputable def mapRightQuotientOfComap :
    (π : F →* P) → (βF : FreeGroup Y →* F) → (β : FreeGroup Y →* P) →
      (K : Subgroup P) → (hβ : π.comp βF = β) →
    Quotient (QuotientGroup.rightRel (Subgroup.comap β K)) →
      Quotient (QuotientGroup.rightRel (Subgroup.comap π K))
  | π, βF, β, K, hβ =>
      Quotient.map' βF (fun _a _b hab => rightRel_map_of_comap π βF β K hβ hab)

/-- Surjectivity of the free-group map makes the induced map on right-quotient classes
surjective. -/
theorem surjective_mapRightQuotientOfComap
    (π : F →* P) (βF : FreeGroup Y →* F) (β : FreeGroup Y →* P)
    (K : Subgroup P) (hβ : π.comp βF = β)
    (hβsurj : Function.Surjective β) :
    Function.Surjective
      (mapRightQuotientOfComap π βF β K hβ) := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro p
  rcases hβsurj (π p) with ⟨w, hw⟩
  refine ⟨Quotient.mk'' w, ?_⟩
  change Quotient.mk'' (βF w) = Quotient.mk'' p
  apply Quotient.sound'
  have hw' : π (βF w) = π p := by
    calc
      π (βF w) = β w := by
        simpa [MonoidHom.comp_apply] using congrArg (fun f : FreeGroup Y →* P => f w) hβ
      _ = π p := hw
  rw [QuotientGroup.rightRel_apply]
  apply (Subgroup.mem_comap (K := K) (f := π)).2
  rw [map_mul, map_inv, hw', mul_inv_cancel]
  exact K.one_mem

/-- The induced map on right-quotient classes is injective under the comap compatibility
equation. -/
theorem injective_mapRightQuotientOfComap
    (π : F →* P) (βF : FreeGroup Y →* F) (β : FreeGroup Y →* P)
    (K : Subgroup P) (hβ : π.comp βF = β) :
    Function.Injective (mapRightQuotientOfComap π βF β K hβ) := by
  intro a b hab
  revert hab
  refine Quotient.inductionOn₂' a b ?_
  intro x y hxy
  apply Quotient.sound'
  have hrel :
      QuotientGroup.rightRel (Subgroup.comap π K) (βF x) (βF y) := Quotient.exact' hxy
  have hx : π (βF x) = β x := by
    simpa [MonoidHom.comp_apply] using congrArg (fun f : FreeGroup Y →* P => f x) hβ
  have hy : π (βF y) = β y := by
    simpa [MonoidHom.comp_apply] using congrArg (fun f : FreeGroup Y →* P => f y) hβ
  rw [QuotientGroup.rightRel_apply] at hrel ⊢
  change π (βF y * (βF x)⁻¹) ∈ K at hrel
  change β (y * x⁻¹) ∈ K
  simpa [MonoidHom.map_mul, MonoidHom.map_inv, hx, hy] using hrel

/--
If \(\beta : \mathrm{FreeGroup}(Y) \to P\) is surjective and \(\beta = \pi \circ \beta_F\), then
the right cosets of \(\beta^{-1}(K)\) are canonically identified with the right cosets of
\(\pi^{-1}(K)\).
-/
noncomputable def rightQuotientEquivOfComap
    (π : F →* P) (βF : FreeGroup Y →* F) (β : FreeGroup Y →* P)
    (K : Subgroup P) (hβ : π.comp βF = β)
    (hβsurj : Function.Surjective β) :
    Quotient (QuotientGroup.rightRel (Subgroup.comap β K)) ≃
      Quotient (QuotientGroup.rightRel (Subgroup.comap π K)) :=
  Equiv.ofBijective
    (mapRightQuotientOfComap π βF β K hβ)
    ⟨injective_mapRightQuotientOfComap π βF β K hβ,
      surjective_mapRightQuotientOfComap π βF β K hβ hβsurj⟩

/-- The right-quotient comparison induced by comap is an equivalence. -/
@[simp] theorem rightQuotientEquivOfComap_mk
    (π : F →* P) (βF : FreeGroup Y →* F) (β : FreeGroup Y →* P)
    (K : Subgroup P) (hβ : π.comp βF = β)
    (hβsurj : Function.Surjective β) (w : FreeGroup Y) :
    rightQuotientEquivOfComap π βF β K hβ hβsurj
        (Quotient.mk'' w) =
      Quotient.mk'' (βF w) := by
  simp only [rightQuotientEquivOfComap, mapRightQuotientOfComap, Equiv.ofBijective_apply,
      Quotient.map'_mk'']

section SchreierSections

variable [DecidableEq Y]
variable {T : Set (FreeGroup Y)}

/--
Transport a discrete Schreier transversal for \(\beta^{-1}(K)\) to a right-coset section for
\(\pi^{-1}(K)\) in the ambient group \(F\).
-/
noncomputable def rightSchreierSectionOfComap
    (π : F →* P) (βF : FreeGroup Y →* F) (β : FreeGroup Y →* P)
    (K : Subgroup P) (hβ : π.comp βF = β)
    (hβsurj : Function.Surjective β)
    (hT : IsRightSchreierTransversal (X := Y) (Subgroup.comap β K) T) :
    Quotient (QuotientGroup.rightRel (Subgroup.comap π K)) → F :=
  fun q =>
    βF <|
      rightTransversalSection (H := Subgroup.comap β K) hT.1
        ((rightQuotientEquivOfComap π βF β K hβ hβsurj).symm q)

/-- The transported right Schreier section satisfies its defining specification. -/
@[simp 900] theorem rightSchreierSectionOfComap_spec
    (π : F →* P) (βF : FreeGroup Y →* F) (β : FreeGroup Y →* P)
    (K : Subgroup P) (hβ : π.comp βF = β)
    (hβsurj : Function.Surjective β)
    (hT : IsRightSchreierTransversal (X := Y) (Subgroup.comap β K) T)
    (q : Quotient (QuotientGroup.rightRel (Subgroup.comap π K))) :
    Quotient.mk'' (rightSchreierSectionOfComap π βF β K hβ hβsurj hT q) = q := by
  let e := rightQuotientEquivOfComap π βF β K hβ hβsurj
  let τT := rightTransversalSection (H := Subgroup.comap β K) hT.1
  calc
    Quotient.mk'' (rightSchreierSectionOfComap π βF β K hβ hβsurj hT q)
        = e (Quotient.mk'' (τT (e.symm q))) := by
            simpa [rightSchreierSectionOfComap, e, τT] using
              (rightQuotientEquivOfComap_mk π βF β K hβ hβsurj (τT (e.symm q))).symm
    _ = e (e.symm q) := by
          rw [rightTransversalSection_spec (H := Subgroup.comap β K) hT.1]
    _ = q := e.apply_symm_apply q

/--
On a coset represented by an element of the chosen Schreier transversal, the transported section
returns the image of that representative.
-/
@[simp 900] theorem rightSchreierSectionOfComap_eq_of_mem
    (π : F →* P) (βF : FreeGroup Y →* F) (β : FreeGroup Y →* P)
    (K : Subgroup P) (hβ : π.comp βF = β)
    (hβsurj : Function.Surjective β)
    (hT : IsRightSchreierTransversal (X := Y) (Subgroup.comap β K) T)
    {t : FreeGroup Y} (ht : t ∈ T) :
    rightSchreierSectionOfComap π βF β K hβ hβsurj hT
        (Quotient.mk'' (βF t)) =
      βF t := by
  let e := rightQuotientEquivOfComap π βF β K hβ hβsurj
  have heq :
      e.symm (Quotient.mk'' (βF t)) = Quotient.mk'' t := by
    apply e.injective
    simp only [Equiv.apply_symm_apply, rightQuotientEquivOfComap_mk, e]
  have hsec :
      rightTransversalSection (H := Subgroup.comap β K) hT.1
          (Quotient.mk'' t) = t := by
    have hsub :
        hT.1.rightQuotientEquiv (Quotient.mk'' t) = ⟨t, ht⟩ := by
      have hq :
          Quotient.mk'' t = hT.1.rightQuotientEquiv.symm ⟨t, ht⟩ := by
        simpa using
          hT.1.mk''_rightQuotientEquiv (hT.1.rightQuotientEquiv.symm ⟨t, ht⟩)
      apply hT.1.rightQuotientEquiv.symm.injective
      simpa using hq
    simpa [rightTransversalSection] using congrArg Subtype.val hsub
  rw [rightSchreierSectionOfComap, heq, hsec]

/-- The transported Schreier section is normalized at the trivial right coset. -/
@[simp 900] theorem rightSchreierSectionOfComap_one
    (π : F →* P) (βF : FreeGroup Y →* F) (β : FreeGroup Y →* P)
    (K : Subgroup P) (hβ : π.comp βF = β)
    (hβsurj : Function.Surjective β)
    (hT : IsRightSchreierTransversal (X := Y) (Subgroup.comap β K) T) :
    rightSchreierSectionOfComap π βF β K hβ hβsurj hT
        (Quotient.mk'' (1 : F)) =
      1 := by
  have hβFone : βF (1 : FreeGroup Y) = 1 := by simp only [map_one]
  rw [← hβFone]
  exact rightSchreierSectionOfComap_eq_of_mem π βF β K hβ hβsurj hT hT.2.1

end SchreierSections

end RightQuotientTransport

section DenseAbstractFreeModel

open _root_.ReidemeisterSchreier.FreeGroup

variable {X : Type u}
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {ι : X → F}

/-- The abstract free-group lift of a topologically generating family has dense range. -/
theorem denseRange_freeGroupLift_of_topologicallyGenerates
    (hgen : ProCGroups.Generation.TopologicallyGenerates (G := F) (Set.range ι)) :
    DenseRange (FreeGroup.lift ι : FreeGroup X →* F) := by
  let φ : FreeGroup X →* F := FreeGroup.lift ι
  have hsub : Set.range ι ⊆ (φ.range : Set F) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨FreeGroup.of x, by simp only [FreeGroup.lift_apply_of, φ]⟩
  have hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := F) (φ.range : Set F) :=
    ProCGroups.Generation.topologicallyGenerates_mono (G := F) hgen hsub
  have hdense : Dense ((φ.range : Subgroup F) : Set F) := by
    rw [← Subgroup.closure_eq φ.range]
    exact (ProCGroups.Generation.topologicallyGenerates_iff_dense
      (G := F) (X := (φ.range : Set F))).1 hφgen
  simpa [DenseRange, MonoidHom.coe_range] using hdense

/--
A dense abstract free-group lift topologically generates through the images of the free
generators.
-/
theorem topologicallyGenerates_range_of_denseAbstractFreeLift
    {Y : Type u}
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {φ : FreeGroup Y →* H}
    (hφ : DenseRange φ) :
    ProCGroups.Generation.TopologicallyGenerates
      (G := H) (Set.range fun y : Y => φ (FreeGroup.of y)) := by
  let j : Y → H := fun y => φ (FreeGroup.of y)
  have himage :
      φ '' Set.range (FreeGroup.of : Y → FreeGroup Y) = Set.range j := by
    ext h
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨FreeGroup.of y, ⟨y, rfl⟩, rfl⟩
  have hclosure :
      Subgroup.closure (Set.range j) = φ.range := by
    calc
      Subgroup.closure (Set.range j)
          = Subgroup.map φ (Subgroup.closure (Set.range (FreeGroup.of : Y → FreeGroup Y))) := by
              simpa [himage] using
                (φ.map_closure (Set.range (FreeGroup.of : Y → FreeGroup Y))).symm
      _ = φ.range := by
          rw [FreeGroup.closure_range_of Y, MonoidHom.range_eq_map]
  rw [ProCGroups.Generation.TopologicallyGenerates, hclosure]
  rw [SetLike.ext'_iff, Subgroup.topologicalClosure_coe, Subgroup.coe_top]
  simpa [DenseRange, MonoidHom.coe_range, dense_iff_closure_eq] using hφ

/--
Restricting a dense homomorphism to the preimage of an open subgroup still has dense range in
that subgroup.
-/
theorem denseRange_comapMap_of_openSubgroup
    {G : Type u} [Group G]
    {H : Type u} [Group H] [TopologicalSpace H]
    {φ : G →* H} (hφ : DenseRange φ)
    {U : Subgroup H} (hU : IsOpen (U : Set H)) :
    DenseRange
      ({ toFun := fun g : Subgroup.comap φ U => ⟨φ g.1, g.2⟩
         map_one' := by simp only [OneMemClass.coe_one, map_one, Subgroup.mk_eq_one]
         map_mul' := by
           intro a b
           ext
           simp only [Subgroup.coe_mul, map_mul]} : Subgroup.comap φ U →* U) := by
  let ψ : Subgroup.comap φ U →* U :=
    { toFun := fun g => ⟨φ g.1, g.2⟩
      map_one' := by simp only [OneMemClass.coe_one, map_one, Subgroup.mk_eq_one]
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul, map_mul]}
  have hdense : Dense (Set.range φ) := by
    simpa [DenseRange] using hφ
  have himage :
      ((↑) : U → H) '' Set.range ψ = (U : Set H) ∩ Set.range φ := by
    ext h
    constructor
    · rintro ⟨_, hu, rfl⟩
      rcases hu with ⟨g, rfl⟩
      exact ⟨g.2, ⟨g.1, rfl⟩⟩
    · rintro ⟨hu, g, rfl⟩
      exact ⟨⟨φ g, hu⟩, ⟨⟨g, hu⟩, rfl⟩, rfl⟩
  have hsubset :
      (U : Set H) ⊆ closure (((↑) : U → H) '' Set.range ψ) := by
    rw [himage]
    simpa [Set.inter_comm] using hdense.open_subset_closure_inter hU
  have hDenseU : Dense (Set.range ψ : Set U) := by
    exact (Subtype.dense_iff).2 hsubset
  change Dense (Set.range ψ)
  exact hDenseU

section FiniteTargets

variable {P : Type u} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]

omit [TopologicalSpace F] [IsTopologicalGroup F] [Finite P] in
/-- A homomorphism into a finite discrete group is surjective as soon as it has dense range. -/
theorem surjective_of_denseRange
    {φ : F →* P} (hφ : DenseRange φ) :
    Function.Surjective φ := by
  have hclosed : IsClosed (Set.range φ) := isClosed_discrete _
  have hclosure : closure (Set.range φ) = Set.univ := hφ.closure_range
  have hrange : Set.range φ = Set.univ := by
    rw [← hclosure]
    exact (closure_eq_iff_isClosed.mpr hclosed).symm
  intro p
  have hp : p ∈ Set.range φ := by
    simp only [hrange, mem_univ]
  exact hp

end FiniteTargets

/--
The abstract subgroup of \(\mathrm{FreeGroup}(X)\) lying over an open subgroup of a compact
group via the dense free-group lift has the corresponding Schreier-transformed rank.
-/
theorem exists_freeBasis_comap_freeGroupLift_of_openSubgroup_of_rankTransform
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F] [CompactSpace F]
    {ι : X → F}
    (hgen : ProCGroups.Generation.TopologicallyGenerates (G := F) (Set.range ι))
    (H : OpenSubgroup F) :
    ∃ Y : Type u,
      Nonempty (FreeGroupBasis Y (Subgroup.comap (FreeGroup.lift ι) (H : Subgroup F))) ∧
      Nat.card Y = _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F
          ⧸ (H : Subgroup F))) := by
  classical
  let βF : FreeGroup X →* F := FreeGroup.lift ι
  let L : Subgroup (FreeGroup X) := Subgroup.comap βF (H : Subgroup F)
  let nQ : ℕ := Nat.card (F ⧸ (H : Subgroup F))
  let P := openSubgroupIndexActionRange (G := F) H
    (show Nat.card (F ⧸ (H : Subgroup F)) = nQ by rfl)
  let ρ : F →ₜ* P :=
    openSubgroupIndexActionRangeContinuousHom (G := F) H
      (show Nat.card (F ⧸ (H : Subgroup F)) = nQ by rfl)
  let q0 : F ⧸ (H : Subgroup F) := QuotientGroup.mk (s := (H : Subgroup F)) (1 : F)
  let K : Subgroup P := MulAction.stabilizer P q0
  let β : FreeGroup X →* P := ρ.toMonoidHom.comp βF
  let : TopologicalSpace (FreeGroup X) := ⊥
  let : DiscreteTopology (FreeGroup X) := ⟨rfl⟩
  have hcomap : Subgroup.comap ρ.toMonoidHom K = (H : Subgroup F) := by
    ext g
    constructor
    · intro hg
      change ρ g • q0 = q0 at hg
      rw [openSubgroupIndexActionRangeContinuousHom_smul_basepoint (G := F) H
        (show Nat.card (F ⧸ (H : Subgroup F)) = nQ by rfl) g] at hg
      change (QuotientGroup.mk (s := (H : Subgroup F)) g : F ⧸ (H : Subgroup F)) =
          QuotientGroup.mk (s := (H : Subgroup F)) (1 : F) at hg
      simpa [QuotientGroup.eq] using hg
    · intro hg
      change ρ g • q0 = q0
      exact openSubgroupIndexActionRangeContinuousHom_smul_basepoint_of_mem
        (G := F) H (show Nat.card (F ⧸ (H : Subgroup F)) = nQ by rfl) hg
  have hβFdense : DenseRange βF :=
    denseRange_freeGroupLift_of_topologicallyGenerates (F := F) (X := X) hgen
  have hρsurj : Function.Surjective ρ := by
    intro p
    rcases p.down.2 with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    apply ULift.ext
    apply Subtype.ext
    exact hg
  have hβdense : DenseRange β := by
    simpa [β, MonoidHom.comp_apply] using
      (Function.Surjective.denseRange hρsurj).comp hβFdense ρ.continuous_toFun
  have hβsurj : Function.Surjective β :=
    surjective_of_denseRange (F := FreeGroup X) (P := P) hβdense
  let H0 : Subgroup F := Subgroup.comap ρ.toMonoidHom K
  have hH0 : H0 = (H : Subgroup F) := by
    simpa [H0] using hcomap
  let eQ :
      Quotient (QuotientGroup.rightRel (Subgroup.comap β K)) ≃
        Quotient (QuotientGroup.rightRel H0) :=
    rightQuotientEquivOfComap ρ.toMonoidHom βF β K rfl hβsurj
  have hcomapL : Subgroup.comap β K = L := by
    ext w
    change β w ∈ K ↔ βF w ∈ (H : Subgroup F)
    change βF w ∈ Subgroup.comap ρ.toMonoidHom K ↔ βF w ∈ (H : Subgroup F)
    rw [hcomap]
  let eQ0 :
      Quotient (QuotientGroup.rightRel L) ≃
        Quotient (QuotientGroup.rightRel H0) := by
    simpa [hcomapL] using eQ
  let : Finite (Quotient (QuotientGroup.rightRel (H : Subgroup F))) := by
    exact
      Finite.of_equiv (F ⧸ (H : Subgroup F))
        (QuotientGroup.quotientRightRelEquivQuotientLeftRel (H : Subgroup F)).symm
  have hRightEq :
      Quotient (QuotientGroup.rightRel (H : Subgroup F)) =
        Quotient (QuotientGroup.rightRel H0) := by
    simpa using
      congrArg (fun S : Subgroup F => Quotient (QuotientGroup.rightRel S)) hH0.symm
  let : Finite (Quotient (QuotientGroup.rightRel H0)) := by
    exact Eq.ndrec
      (motive := fun T => Finite T)
      (inferInstance : Finite (Quotient (QuotientGroup.rightRel (H : Subgroup F))))
      hRightEq
  let : Finite (Quotient (QuotientGroup.rightRel L)) :=
    Finite.of_equiv
      (Quotient (QuotientGroup.rightRel H0)) eQ0.symm
  let : Finite (FreeGroup X ⧸ L) :=
    Finite.of_equiv
      (Quotient (QuotientGroup.rightRel L))
      (QuotientGroup.quotientRightRelEquivQuotientLeftRel L)
  have hquotCard :
      Nat.card (FreeGroup X ⧸ L) = Nat.card (F ⧸ (H : Subgroup F)) := by
    calc
      Nat.card (FreeGroup X ⧸ L)
          = Nat.card (Quotient (QuotientGroup.rightRel L)) :=
            Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel L).symm
      _ = Nat.card (Quotient (QuotientGroup.rightRel H0)) :=
            Nat.card_congr eQ0
      _ = Nat.card (Quotient (QuotientGroup.rightRel (H : Subgroup F))) := by
            simpa using congrArg Nat.card hRightEq.symm
      _ = Nat.card (F ⧸ (H : Subgroup F)) :=
            Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (H : Subgroup F))
  obtain ⟨Y, hYfree, hYcard⟩ :=
    exists_freeBasis_subgroupOfFreeGroup_of_rankTransform (X := X) (L := L)
  refine ⟨Y, hYfree, ?_⟩
  simpa [hquotCard] using hYcard

end DenseAbstractFreeModel

end Profinite
end ReidemeisterSchreier
