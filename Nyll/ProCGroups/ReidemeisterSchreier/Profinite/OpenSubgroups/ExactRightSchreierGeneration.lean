/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.DenseFreeModel
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.SchreierTransversals

/-!
# Exact right-Schreier generation

Using a transported right-coset section and the wreath-product embedding, this
module identifies the concrete right-Schreier cocycles that topologically
generate an open subgroup.  It also proves the finite-quotient lifting
statements used to recognize the resulting dense abstract free group as the
required pro-\(C\) completion.
-/

open Set
open scoped Topology Pointwise

namespace ReidemeisterSchreier
namespace Profinite

open ProCGroups
open ProCGroups.FreeProC
open ProCGroups.ProC
open ProCGroups.WreathProducts
open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.OpenSubgroups

universe u v

section ExactRightSchreierGeneration

open _root_.ReidemeisterSchreier.FreeGroup

variable {X : Type u} [TopologicalSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable {P : Type u} [Group P]
variable {ι : X → F}
variable {φ : FreeGroup X →* F}
variable {π : F →* P}
variable {K : Subgroup P}

omit [TopologicalSpace X] [Group F] [TopologicalSpace F] [IsTopologicalGroup F] ι φ π in
/--
The distinguished profinite minimal-power Schreier generator agrees with the generator supplied
by the discrete minimal-power Schreier-transversal theorem for the finite quotient/comap
subgroup.
-/
theorem profinite_minimalPower_schreierGenerator_lifts_discrete
    [DecidableEq X]
    (β : FreeGroup X →* P) (K : Subgroup P) (x : X) {N : ℕ}
    (hN : 0 < N)
    (hpow : β ((FreeGroup.of x) ^ N) ∈ K)
    (hmin : ∀ m : ℕ, 0 < m → m < N → β ((FreeGroup.of x) ^ m) ∉ K) :
    ∃ T : Set (FreeGroup X), ∃ hT :
        IsRightSchreierTransversal (X := X) (Subgroup.comap β K) T,
      (FreeGroup.of x) ^ (N - 1) ∈ T ∧
        schreierGenerator (X := X) hT ((FreeGroup.of x) ^ (N - 1)) x =
          ⟨(FreeGroup.of x) ^ N, hpow⟩ := by
  exact
    exists_rightSchreierTransversal_of_minimalGeneratorPower
      (X := X) (L := Subgroup.comap β K) x hN hpow hmin

omit [TopologicalSpace X] [TopologicalSpace F] [IsTopologicalGroup F] in
/--
On elements of the abstract Schreier transversal, the transported cocycle in the ambient group
matches the image of the discrete Schreier generator.
-/
theorem map_schreierGenerator_eq_cocycle
    [DecidableEq X]
    {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) (Subgroup.comap (π.comp φ) K) T)
    (hβsurj : Function.Surjective (π.comp φ))
    {t : FreeGroup X} (ht : t ∈ T) (x : X) :
    let τ := rightSchreierSectionOfComap π φ (π.comp φ) K rfl hβsurj hT
    let hτ := rightSchreierSectionOfComap_spec π φ (π.comp φ) K rfl hβsurj hT
    let Hc : Subgroup F := Subgroup.comap π K
    rightQuotientSectionCocycle (H := Hc) τ hτ (φ (FreeGroup.of x))
        (Quotient.mk'' (φ t)) =
      ⟨φ (schreierGenerator (X := X) hT t x), by
        change (π.comp φ) ↑(schreierGenerator (X := X) hT t x) ∈ K
        exact (schreierGenerator (X := X) hT t x).2⟩ := by
  classical
  let τ := rightSchreierSectionOfComap π φ (π.comp φ) K rfl hβsurj hT
  let hτ := rightSchreierSectionOfComap_spec π φ (π.comp φ) K rfl hβsurj hT
  let Hc : Subgroup F := Subgroup.comap π K
  let rep := schreierRepresentative (X := X) hT (t * FreeGroup.of x)
  have hτt :
      τ (Quotient.mk'' (φ t)) = φ t := by
    simpa [τ] using
      (rightSchreierSectionOfComap_eq_of_mem π φ (π.comp φ) K rfl hβsurj hT ht)
  have hrep_rel :
      QuotientGroup.rightRel Hc (φ ((rep : T) : FreeGroup X)) (φ (t * FreeGroup.of x)) := by
    rw [QuotientGroup.rightRel_apply]
    dsimp [Hc]
    change π (φ (t * FreeGroup.of x) * (φ ((rep : T) : FreeGroup X))⁻¹) ∈ K
    have hrel :
        t * FreeGroup.of x * (((rep : T) : FreeGroup X))⁻¹ ∈
          Subgroup.comap (π.comp φ) K := by
      exact hT.1.mul_inv_toRightFun_mem (t * FreeGroup.of x)
    simpa [MonoidHom.comp_apply, MonoidHom.map_mul, MonoidHom.map_inv] using hrel
  have hqnext :
      (φ (FreeGroup.of x))⁻¹ • (Quotient.mk'' (φ t) : Quotient (QuotientGroup.rightRel Hc)) =
        Quotient.mk'' (φ ((rep : T) : FreeGroup X)) := by
    calc
      (φ (FreeGroup.of x))⁻¹ • (Quotient.mk'' (φ t) : Quotient (QuotientGroup.rightRel Hc))
          = Quotient.mk'' (φ t * φ (FreeGroup.of x)) := by
              rw [rightCosetMulAction_inv_mk_smul (H := Hc) (φ (FreeGroup.of x)) (φ t)]
      _ = Quotient.mk'' (φ (t * FreeGroup.of x)) := by
            simp only [MonoidHom.map_mul]
      _ = Quotient.mk'' (φ ((rep : T) : FreeGroup X)) := (Quotient.sound' hrep_rel).symm
  have hτnext :
      τ (Quotient.mk'' (φ t * φ (FreeGroup.of x))) =
        φ ((rep : T) : FreeGroup X) := by
    have hqnext' :
        (Quotient.mk'' (φ t * φ (FreeGroup.of x)) :
            Quotient (QuotientGroup.rightRel Hc)) =
          Quotient.mk'' (φ ((rep : T) : FreeGroup X)) := by
      calc
        (Quotient.mk'' (φ t * φ (FreeGroup.of x)) :
            Quotient (QuotientGroup.rightRel Hc))
            = Quotient.mk'' (φ (t * FreeGroup.of x)) := by
                simp only [MonoidHom.map_mul]
        _ = Quotient.mk'' (φ ((rep : T) : FreeGroup X)) := (Quotient.sound' hrep_rel).symm
    rw [hqnext']
    exact
      rightSchreierSectionOfComap_eq_of_mem π φ (π.comp φ) K rfl hβsurj hT rep.2
  have hτrep :
      τ ((φ (FreeGroup.of x))⁻¹ •
          (Quotient.mk'' (φ t) : Quotient (QuotientGroup.rightRel Hc))) =
        φ ((rep : T) : FreeGroup X) := by
    have hrep_sec :
        τ (Quotient.mk'' (φ ((rep : T) : FreeGroup X))) =
          φ ((rep : T) : FreeGroup X) :=
      rightSchreierSectionOfComap_eq_of_mem π φ (π.comp φ) K rfl hβsurj hT rep.2
    exact hqnext ▸ hrep_sec
  apply Subtype.ext
  change
      τ (Quotient.mk'' (φ t)) * φ (FreeGroup.of x) *
          (τ ((φ (FreeGroup.of x))⁻¹ •
            (Quotient.mk'' (φ t) : Quotient (QuotientGroup.rightRel Hc))))⁻¹ =
        φ ↑(schreierGenerator hT t x)
  dsimp [rightQuotientSectionCocycle]
  have hqnext'' :
      (Quotient.mk'' (φ t * φ (FreeGroup.of x)) :
          Quotient (QuotientGroup.rightRel Hc)) =
        (φ (FreeGroup.of x))⁻¹ •
          (Quotient.mk'' (φ t) : Quotient (QuotientGroup.rightRel Hc)) := by
    simp only [rightCosetMulAction_mk_smul, inv_inv] at hqnext ⊢
  have hqnext''' :
      (Quotient.mk'' (φ t * (φ (FreeGroup.of x))⁻¹⁻¹) :
          Quotient (QuotientGroup.rightRel Hc)) =
        (φ (FreeGroup.of x))⁻¹ •
          (Quotient.mk'' (φ t) : Quotient (QuotientGroup.rightRel Hc)) := by
    simpa only [inv_inv] using hqnext''
  rw [hτt, hqnext''', hτrep]
  simp only [mul_assoc, schreierGenerator, MonoidHom.map_mul, MonoidHom.map_inv, rep]

omit [TopologicalSpace X] [TopologicalSpace F] [IsTopologicalGroup F] in
/--
On elements of the abstract Schreier transversal, the transported right Schreier cocycle in the
ambient group is the image of the discrete Schreier generator.
-/
theorem rightQuotientSectionCocycle_eq_map_schreierGenerator_of_comap
    [DecidableEq X]
    {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) (Subgroup.comap (π.comp φ) K) T)
    (hβsurj : Function.Surjective (π.comp φ))
    {t : FreeGroup X} (ht : t ∈ T) (x : X) :
    let τ := rightSchreierSectionOfComap π φ (π.comp φ) K rfl hβsurj hT
    let hτ := rightSchreierSectionOfComap_spec π φ (π.comp φ) K rfl hβsurj hT
    let Hc : Subgroup F := Subgroup.comap π K
    rightQuotientSectionCocycle (H := Hc) τ hτ (φ (FreeGroup.of x))
        (Quotient.mk'' (φ t)) =
      ⟨φ (schreierGenerator (X := X) hT t x), by
        change (π.comp φ) ↑(schreierGenerator (X := X) hT t x) ∈ K
        exact (schreierGenerator (X := X) hT t x).2⟩ := by
  simpa using map_schreierGenerator_eq_cocycle
    (X := X) (φ := φ) (π := π) (K := K) hT hβsurj ht x

omit [TopologicalSpace X] [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F] in
/--
The transported right Schreier cocycle topologically generates the ambient subgroup as soon as
the dense abstract free subgroup remains dense after restricting to that subgroup.
-/
theorem topologicallyGenerates_range_transportedCocycle
    [DecidableEq X]
    {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) (Subgroup.comap (π.comp φ) K) T)
    (hβsurj : Function.Surjective (π.comp φ))
    (hφdense :
      DenseRange
        ({ toFun := fun g : Subgroup.comap (π.comp φ) K => ⟨φ g.1, g.2⟩
           map_one' := by simp only [OneMemClass.coe_one, map_one, Subgroup.mk_eq_one]
           map_mul' := by
             intro a b
             ext
             simp only [Subgroup.coe_mul, map_mul]} :
          Subgroup.comap (π.comp φ) K →* ↥(Subgroup.comap π K))) :
    let τ := rightSchreierSectionOfComap π φ (π.comp φ) K rfl hβsurj hT
    let hτ := rightSchreierSectionOfComap_spec π φ (π.comp φ) K rfl hβsurj hT
    let κ :
        Quotient (QuotientGroup.rightRel (Subgroup.comap π K)) × X →
          ↥(Subgroup.comap π K) :=
      fun p =>
        rightQuotientSectionCocycle (H := Subgroup.comap π K) τ hτ (φ (FreeGroup.of p.2)) p.1
    ProCGroups.Generation.TopologicallyGenerates (G := ↥(Subgroup.comap π K)) (Set.range κ) := by
  classical
  let φL : Subgroup.comap (π.comp φ) K →* ↥(Subgroup.comap π K) :=
    { toFun := fun g => ⟨φ g.1, g.2⟩
      map_one' := by simp only [OneMemClass.coe_one, map_one, Subgroup.mk_eq_one]
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul, map_mul]}
  let τ := rightSchreierSectionOfComap π φ (π.comp φ) K rfl hβsurj hT
  let hτ := rightSchreierSectionOfComap_spec π φ (π.comp φ) K rfl hβsurj hT
  let κ :
      Quotient (QuotientGroup.rightRel (Subgroup.comap π K)) × X →
        ↥(Subgroup.comap π K) :=
    fun p =>
      rightQuotientSectionCocycle (H := Subgroup.comap π K) τ hτ (φ (FreeGroup.of p.2)) p.1
  have hsubset :
      φL '' (schreierGeneratorSet (X := X) hT : Set (Subgroup.comap (π.comp φ) K)) ⊆
        Set.range κ := by
    intro z hz
    rcases hz with ⟨s, hs, rfl⟩
    rcases hs with ⟨t, ht, x, rfl, _⟩
    refine ⟨(Quotient.mk'' (φ t), x), ?_⟩
    simpa [κ, φL] using
      (map_schreierGenerator_eq_cocycle (X := X) (φ := φ) (π := π) (K := K)
        hT hβsurj ht x)
  have hmap :
      Subgroup.closure
          (φL '' (schreierGeneratorSet (X := X) hT :
            Set (Subgroup.comap (π.comp φ) K))) =
        φL.range := by
    calc
      Subgroup.closure
          (φL '' (schreierGeneratorSet (X := X) hT :
            Set (Subgroup.comap (π.comp φ) K)))
          = (Subgroup.closure
              (schreierGeneratorSet (X := X) hT :
                Set (Subgroup.comap (π.comp φ) K))).map φL := by
                  symm
                  exact MonoidHom.map_closure φL _
      _ = (⊤ : Subgroup (Subgroup.comap (π.comp φ) K)).map φL := by
            rw [closure_schreierGeneratorSet_eq_top (X := X) hT]
      _ = φL.range := by
            rw [← MonoidHom.range_eq_map]
  have hgenImg :
      ProCGroups.Generation.TopologicallyGenerates (G := ↥(Subgroup.comap π K))
        (φL '' (schreierGeneratorSet (X := X) hT :
          Set (Subgroup.comap (π.comp φ) K))) := by
    rw [ProCGroups.Generation.topologicallyGenerates_iff_dense]
    rw [hmap]
    change Dense (Set.range φL)
    exact hφdense
  exact ProCGroups.Generation.topologicallyGenerates_mono (G := ↥(Subgroup.comap π K))
    hgenImg hsubset

end ExactRightSchreierGeneration

section WreathTargetClosures

variable {Y : Type u} [TopologicalSpace Y]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace Y] in
/--
The topological closure of the subgroup generated by the range of a map is itself topologically
generated by that range, viewed inside the closed subgroup.
-/
theorem topologicallyGenerates_topologicalClosure_of_range
    (ξ : Y → G) :
    let W : Subgroup G := (Subgroup.closure (Set.range ξ)).topologicalClosure
    let ξW : Y → W := fun y =>
      ⟨ξ y, Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨y, rfl⟩)⟩
    ProCGroups.Generation.TopologicallyGenerates (G := W) (Set.range ξW) := by
  classical
  let A : Subgroup G := Subgroup.closure (Set.range ξ)
  let W : Subgroup G := A.topologicalClosure
  let ξW : Y → W := fun y =>
    ⟨ξ y, Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨y, rfl⟩)⟩
  rw [ProCGroups.Generation.topologicallyGenerates_iff_dense]
  let B : Subgroup W := Subgroup.closure (Set.range ξW)
  let i : W →* G := W.subtype
  have hrange : i '' Set.range ξW = Set.range ξ := by
    ext g
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨ξW y, ⟨y, rfl⟩, rfl⟩
  have hmap : B.map i = A := by
    calc
      B.map i = Subgroup.closure (i '' Set.range ξW) := by
        simpa [B] using (MonoidHom.map_closure i (Set.range ξW))
      _ = A := by
        simp only [hrange, A]
  have himage : ((↑) : W → G) '' (B : Set W) = (A : Set G) := by
    change i '' (B : Set W) = (A : Set G)
    exact congrArg SetLike.coe hmap
  have hsubset :
      (W : Set G) ⊆ closure (((↑) : W → G) '' (B : Set W)) := by
    rw [himage]
    simp only [Subgroup.topologicalClosure_coe, subset_refl, W, A]
  exact (Subtype.dense_iff).2 hsubset

end WreathTargetClosures

section UniquenessOnGeneratingRanges

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type v} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]

omit [IsTopologicalGroup A] in
/--
Continuous homomorphisms into a Hausdorff topological group are determined by their values on
any topologically generating set. It is a continuity claim, checked through the topology
generated by finite-stage projections.
-/
theorem continuousMonoidHom_eq_of_agrees_on_topologicallyGeneratingSet
    {X : Set G}
    (hX : ProCGroups.Generation.TopologicallyGenerates (G := G) X)
    {f g : G →* A} (hf : Continuous f) (hg : Continuous g)
    (hfg : Set.EqOn f g X) :
    f = g := by
  let E : Subgroup G :=
    { carrier := {x | f x = g x}
      one_mem' := by simp only [mem_ofPred_eq, map_one]
      mul_mem' := by
        intro a b ha hb
        calc
          f (a * b) = f a * f b := by simp only [map_mul]
          _ = g a * g b := by rw [ha, hb]
          _ = g (a * b) := by simp only [map_mul]
      inv_mem' := by
        intro a ha
        simpa [ha] }
  have hsub : X ⊆ (E : Set G) := by
    intro x hx
    exact hfg hx
  have hclosure : Subgroup.closure X ≤ E :=
    (Subgroup.closure_le (K := E)).2 hsub
  let S : Subgroup G := Subgroup.closure X
  have hDense : DenseRange (S.subtype : S → G) := by
    have hDenseSet : Dense ((S : Subgroup G) : Set G) := by
      simpa [S] using
        (ProCGroups.Generation.topologicallyGenerates_iff_dense (G := G) (X := X)).1 hX
    simpa [DenseRange] using hDenseSet
  have hEq :
      (fun s : S => f s.1) = fun s : S => g s.1 := by
    funext s
    exact hclosure s.2
  have hfun :
      (fun x : G => f x) = fun x : G => g x := by
    apply DenseRange.equalizer (f := (S.subtype : S → G)) hDense
    · exact hf
    · exact hg
    · change (fun s : S => f s.1) = fun s : S => g s.1
      exact hEq
  ext x
  exact congrArg (fun h : G → A => h x) hfun

end UniquenessOnGeneratingRanges

section TransportedSectionPurity

variable {P : Type u} [Group P]
variable {X : Type u} [DecidableEq X]
variable {F : Type u} [Group F]
variable {A : Type v} [Group A]
variable {φ : FreeGroup X →* F} {π : F →* P} {K : Subgroup P}
variable {T : Set (FreeGroup X)}

/-- The right-coset comap carries the natural multiplication action induced by the subgroup map. -/
instance instMulActionRightCosetComap :
    MulAction F (Quotient (QuotientGroup.rightRel (Subgroup.comap π K))) :=
  rightCosetMulAction (Subgroup.comap π K)

attribute [-instance] instMulActionRightCosetComap

/--
On a transported Schreier transversal, basepoint coordinates are trivial once every tree-edge
Schreier generator maps to \(1\).
-/
theorem wreathLeftCoordinate_basepoint_of_transversalWord
    (hT : IsRightSchreierTransversal (X := X) (Subgroup.comap (π.comp φ) K) T)
    (ψ : F →* PermutationalWreathProduct A
      (Quotient (QuotientGroup.rightRel (Subgroup.comap π K))) F)
    (hψ :
      (SemidirectProduct.rightHom :
          PermutationalWreathProduct A
            (Quotient (QuotientGroup.rightRel (Subgroup.comap π K))) F →* F).comp ψ =
        MonoidHom.id F)
    (hone :
      ∀ {t : FreeGroup X}, t ∈ T → ∀ x : X,
        schreierGenerator (X := X) hT t x = 1 →
          wreathLeftCoordinate ψ
            (Quotient.mk'' (φ t) :
              Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
            (φ (FreeGroup.of x)) = 1)
    (t : FreeGroup X) (ht : t ∈ T) :
    wreathLeftCoordinate ψ
      (Quotient.mk'' (1 : F) :
        Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
      (φ t) = 1 := by
  by_cases h1 : t = 1
  · subst h1
    simp only [wreathLeftCoordinate, map_one, SemidirectProduct.one_left, Pi.one_apply]
  · rcases FreeGroup.lastLetter_cases_of_ne_one (X := X) h1 with ⟨x, hpos | hneg⟩
    · rcases hpos with ⟨hw, hlast, hmul⟩
      have hp : FreeGroup.prefixParent t ∈ T :=
        prefixParent_mem_of_mem (X := X) hT ht
      have hpure :
          wreathLeftCoordinate ψ
            (Quotient.mk'' (1 : F) :
              Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
            (φ (FreeGroup.prefixParent t)) = 1 :=
        wreathLeftCoordinate_basepoint_of_transversalWord hT ψ hψ hone
          (FreeGroup.prefixParent t) hp
      have hcoord :
          wreathLeftCoordinate ψ
            (Quotient.mk'' (φ (FreeGroup.prefixParent t)) :
              Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
            (φ (FreeGroup.of x)) = 1 := by
        exact hone hp x
          (schreierGenerator_eq_one_of_prefixParent_last_pos (X := X) hT ht hw hlast)
      have hq :
          (φ (FreeGroup.prefixParent t))⁻¹ •
              (Quotient.mk'' (1 : F) :
                Quotient (QuotientGroup.rightRel (Subgroup.comap π K))) =
            Quotient.mk'' (φ (FreeGroup.prefixParent t)) := by
        rw [rightCosetMulAction_inv_mk_smul
          (H := Subgroup.comap π K) (φ (FreeGroup.prefixParent t)) 1]
        simp only [one_mul]
      have hmulφ :
          φ (FreeGroup.prefixParent t) * φ (FreeGroup.of x) = φ t := by
        simpa [MonoidHom.map_mul] using congrArg φ hmul
      calc
        wreathLeftCoordinate ψ
            (Quotient.mk'' (1 : F) :
              Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
            (φ t)
            =
          wreathLeftCoordinate ψ
            (Quotient.mk'' (1 : F) :
              Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
            (φ (FreeGroup.prefixParent t) * φ (FreeGroup.of x)) := by
              rw [hmulφ]
        _ =
          wreathLeftCoordinate ψ
              (Quotient.mk'' (1 : F) :
                Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
              (φ (FreeGroup.prefixParent t)) *
            wreathLeftCoordinate ψ
              ((φ (FreeGroup.prefixParent t))⁻¹ •
                (Quotient.mk'' (1 : F) :
                  Quotient (QuotientGroup.rightRel (Subgroup.comap π K))))
              (φ (FreeGroup.of x)) := by
                rw [wreathLeftCoordinate_mul (ψ := ψ) hψ]
        _ = 1 * 1 := by rw [hpure, hq, hcoord]
        _ = 1 := by simp only [mul_one]
    · rcases hneg with ⟨hw, hlast, hmul⟩
      have hp : FreeGroup.prefixParent t ∈ T :=
        prefixParent_mem_of_mem (X := X) hT ht
      have hpure :
          wreathLeftCoordinate ψ
            (Quotient.mk'' (1 : F) :
              Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
            (φ (FreeGroup.prefixParent t)) = 1 :=
        wreathLeftCoordinate_basepoint_of_transversalWord hT ψ hψ hone
          (FreeGroup.prefixParent t) hp
      have hcoord :
          wreathLeftCoordinate ψ
            (Quotient.mk'' (φ t) :
              Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
            (φ (FreeGroup.of x)) = 1 := by
        exact hone ht x
          (schreierGenerator_eq_one_of_cancels (X := X) hT ht hw hlast)
      have hq :
          (φ t)⁻¹ •
              (Quotient.mk'' (1 : F) :
                Quotient (QuotientGroup.rightRel (Subgroup.comap π K))) =
            Quotient.mk'' (φ t) := by
        rw [rightCosetMulAction_inv_mk_smul (H := Subgroup.comap π K) (φ t) 1]
        simp only [one_mul]
      have hmulφ :
          φ t * φ (FreeGroup.of x) = φ (FreeGroup.prefixParent t) := by
        simpa [MonoidHom.map_mul] using congrArg φ hmul
      have hstep :
          wreathLeftCoordinate ψ
            (Quotient.mk'' (1 : F) :
              Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
            (φ (FreeGroup.prefixParent t)) =
          wreathLeftCoordinate ψ
            (Quotient.mk'' (1 : F) :
              Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
            (φ t) := by
        calc
          wreathLeftCoordinate ψ
              (Quotient.mk'' (1 : F) :
                Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
              (φ (FreeGroup.prefixParent t))
              =
            wreathLeftCoordinate ψ
              (Quotient.mk'' (1 : F) :
                Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
              (φ t * φ (FreeGroup.of x)) := by
                rw [hmulφ]
          _ =
            wreathLeftCoordinate ψ
                (Quotient.mk'' (1 : F) :
                  Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
                (φ t) *
              wreathLeftCoordinate ψ
                ((φ t)⁻¹ •
                  (Quotient.mk'' (1 : F) :
                    Quotient (QuotientGroup.rightRel (Subgroup.comap π K))))
                (φ (FreeGroup.of x)) := by
                  rw [wreathLeftCoordinate_mul (ψ := ψ) hψ]
          _ = wreathLeftCoordinate ψ
                (Quotient.mk'' (1 : F) :
                  Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
                (φ t) * 1 := by
                  rw [hq, hcoord]
          _ = wreathLeftCoordinate ψ
                (Quotient.mk'' (1 : F) :
                  Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
                (φ t) := by simp only [mul_one]
      exact hstep.symm.trans hpure
termination_by (FreeGroup.toWord t).length
decreasing_by
  all_goals
    simpa [Internal.FreeGroupWord.FreeGroup.toWord_prefixParent] using
      Internal.FreeGroupWord.FreeGroup.toWord_length_prefixParent_lt (t := t) h1

/--
The transported Schreier section has trivial basepoint coordinate whenever the tree-edge
generators do.
-/
theorem wreathLeftCoordinate_basepoint_of_rightSchreierSectionOfComap
    (hT : IsRightSchreierTransversal (X := X) (Subgroup.comap (π.comp φ) K) T)
    (hβsurj : Function.Surjective (π.comp φ))
    (ψ : F →* PermutationalWreathProduct A
      (Quotient (QuotientGroup.rightRel (Subgroup.comap π K))) F)
    (hψ :
      (SemidirectProduct.rightHom :
          PermutationalWreathProduct A
            (Quotient (QuotientGroup.rightRel (Subgroup.comap π K))) F →* F).comp ψ =
        MonoidHom.id F)
    (hone :
      ∀ {t : FreeGroup X}, t ∈ T → ∀ x : X,
        schreierGenerator (X := X) hT t x = 1 →
          wreathLeftCoordinate ψ
            (Quotient.mk'' (φ t) :
              Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
            (φ (FreeGroup.of x)) = 1)
    (q : Quotient (QuotientGroup.rightRel (Subgroup.comap π K))) :
    wreathLeftCoordinate ψ
      (Quotient.mk'' (1 : F) :
        Quotient (QuotientGroup.rightRel (Subgroup.comap π K)))
      (rightSchreierSectionOfComap π φ (π.comp φ) K rfl hβsurj hT q) = 1 := by
  let e := rightQuotientEquivOfComap π φ (π.comp φ) K rfl hβsurj
  let tT : T := hT.1.rightQuotientEquiv (e.symm q)
  have htT : ((tT : T) : FreeGroup X) ∈ T := tT.2
  have hsec :
      rightSchreierSectionOfComap π φ (π.comp φ) K rfl hβsurj hT q =
        φ ((tT : T) : FreeGroup X) := by
    simp only [rightSchreierSectionOfComap, rightTransversalSection, tT, e]
  rw [hsec]
  exact wreathLeftCoordinate_basepoint_of_transversalWord hT ψ hψ hone
    ((tT : T) : FreeGroup X) htT

end TransportedSectionPurity

section FiniteQuotientLift

open _root_.ReidemeisterSchreier.FreeGroup

/--
Concrete finite-quotient lift for the dense abstract Schreier subgroup comap (free group lift
\(\iota\)) to \(H\). It is a continuity claim, checked through the topology generated by
finite-stage projections.
-/
theorem exists_continuousFiniteQuotientLift_of_comap_freeGroupLift
    (C : ProCGroups.FiniteGroupClass.{u})
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hQuot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
      [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (H : OpenSubgroup F)
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [Finite Q] [DiscreteTopology Q]
    (hQ : C Q)
    (ψ : Subgroup.comap (FreeGroup.lift ι) (H : Subgroup F) →* Q) :
    ∃ ψBar : ↥(H : Subgroup F) →* Q,
      Continuous ψBar ∧
        ψBar.comp
          ({ toFun := fun g : Subgroup.comap (FreeGroup.lift ι) (H : Subgroup F) =>
              ⟨(FreeGroup.lift ι) g.1, g.2⟩
             map_one' := by simp only [OneMemClass.coe_one, map_one, Subgroup.mk_eq_one]
             map_mul' := by
               intro a b
               ext
               simp only [Subgroup.coe_mul, map_mul]} :
            Subgroup.comap (FreeGroup.lift ι) (H : Subgroup F) →* ↥(H : Subgroup F)) = ψ := by
  classical
  let n : ℕ := Nat.card (F ⧸ (H : Subgroup F))
  let P := openSubgroupIndexActionRange (G := F) H
    (show Nat.card (F ⧸ (H : Subgroup F)) = n by rfl)
  let ρ : F →ₜ* P :=
    openSubgroupIndexActionRangeContinuousHom (G := F) H
      (show Nat.card (F ⧸ (H : Subgroup F)) = n by rfl)
  let q0 : F ⧸ (H : Subgroup F) := QuotientGroup.mk (s := (H : Subgroup F)) (1 : F)
  let K : Subgroup P := MulAction.stabilizer P q0
  let βF : FreeGroup X →* F := FreeGroup.lift ι
  let β : FreeGroup X →* P := ρ.toMonoidHom.comp βF
  let Lk : Subgroup (FreeGroup X) := Subgroup.comap β K
  let L : Subgroup (FreeGroup X) := Subgroup.comap βF (H : Subgroup F)
  let : TopologicalSpace (FreeGroup X) := ⊥
  let : DiscreteTopology (FreeGroup X) := ⟨rfl⟩
  have hcomap : Subgroup.comap ρ.toMonoidHom K = (H : Subgroup F) := by
    ext g
    constructor
    · intro hg
      change ρ g • q0 = q0 at hg
      rw [openSubgroupIndexActionRangeContinuousHom_smul_basepoint
        (G := F) H (show Nat.card (F ⧸ (H : Subgroup F)) = n by rfl) g] at hg
      change (QuotientGroup.mk (s := (H : Subgroup F)) g : F ⧸ (H : Subgroup F)) =
          QuotientGroup.mk (s := (H : Subgroup F)) (1 : F) at hg
      simpa [QuotientGroup.eq] using hg
    · intro hg
      change ρ g • q0 = q0
      exact openSubgroupIndexActionRangeContinuousHom_smul_basepoint_of_mem
        (G := F) H (show Nat.card (F ⧸ (H : Subgroup F)) = n by rfl) hg
  have hLk : Lk = L := by
    ext w
    change β w ∈ K ↔ βF w ∈ (H : Subgroup F)
    change βF w ∈ Subgroup.comap ρ.toMonoidHom K ↔ βF w ∈ (H : Subgroup F)
    rw [hcomap]
  let Hc : OpenSubgroup F :=
    { toSubgroup := Subgroup.comap ρ.toMonoidHom K
      isOpen' := by
        rw [hcomap]
        exact H.isOpen' }
  have hHc : Hc = H := by
    ext g
    change g ∈ Subgroup.comap ρ.toMonoidHom K ↔ g ∈ (H : Subgroup F)
    rw [hcomap]
  let toK : L →* Lk :=
    { toFun := fun g => ⟨g.1, by
        have hgL : βF g.1 ∈ (H : Subgroup F) := g.2
        have hgComap : βF g.1 ∈ (Subgroup.comap ρ.toMonoidHom K : Subgroup F) := by
          exact (congrArg (fun S : Subgroup F => βF g.1 ∈ S) hcomap).mpr hgL
        change ρ (βF g.1) ∈ K
        exact hgComap⟩
      map_one' := by simp only [OneMemClass.coe_one, Subgroup.mk_eq_one]
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk]}
  let fromK : Lk →* L :=
    { toFun := fun g => ⟨g.1, by
        have hgLk : β g.1 ∈ K := g.2
        have hgComap : βF g.1 ∈ (Subgroup.comap ρ.toMonoidHom K : Subgroup F) := by
          change ρ (βF g.1) ∈ K
          simpa [β] using hgLk
        have hgH : βF g.1 ∈ (H : Subgroup F) := by
          exact (congrArg (fun S : Subgroup F => βF g.1 ∈ S) hcomap).mp hgComap
        change βF g.1 ∈ (H : Subgroup F)
        exact hgH⟩
      map_one' := by simp only [OneMemClass.coe_one, Subgroup.mk_eq_one]
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk]}
  let φOrig : L →* ↥(H : Subgroup F) :=
    { toFun := fun g => ⟨βF g.1, g.2⟩
      map_one' := by simp only [OneMemClass.coe_one, map_one, Subgroup.mk_eq_one]
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul, map_mul]}
  let φK : Lk →* ↥(Hc : Subgroup F) :=
    { toFun := fun g => ⟨βF g.1, by
        have hgLk : β g.1 ∈ K := g.2
        change ρ (βF g.1) ∈ K
        simpa [β] using hgLk⟩
      map_one' := by simp only [OneMemClass.coe_one, map_one, Subgroup.mk_eq_one]
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul, map_mul, MulMemClass.mk_mul_mk]}
  let toHc : ↥(H : Subgroup F) →* ↥(Hc : Subgroup F) :=
    { toFun := fun g => ⟨g.1, by
        have hgH : g.1 ∈ (H : Subgroup F) := g.2
        have hgComap : g.1 ∈ (Subgroup.comap ρ.toMonoidHom K : Subgroup F) := by
          exact (congrArg (fun S : Subgroup F => g.1 ∈ S) hcomap).mpr hgH
        change ρ g.1 ∈ K
        exact hgComap⟩
      map_one' := by simp only [OneMemClass.coe_one, Subgroup.mk_eq_one]
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk]}
  let ψK : Lk →* Q := ψ.comp fromK
  let : DiscreteTopology (OpenSubgroupRightQuotient Hc) :=
    discreteTopology_openSubgroupRightQuotient (F := F) Hc
  let : ContinuousSMul F (OpenSubgroupRightQuotient Hc) := by
    refine ContinuousSMul.mk ?_
    refine (continuous_prod_of_discrete_right).2 ?_
    intro q
    convert
      (continuous_rightCosetMulAction_inv_smul_of_open
        (G := F) (H := (Hc : Subgroup F)) Hc.isOpen' q).comp continuous_inv using 1
    ext g
    simp only [Function.comp_apply, inv_inv]
  have hβFdense : DenseRange βF :=
    denseRange_freeGroupLift_of_topologicallyGenerates
      (F := F) (X := X) hF.generates_range
  have hρSurj : Function.Surjective ρ := by
    intro p
    rcases p.down.2 with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    apply ULift.ext
    apply Subtype.ext
    exact hg
  have hβDense : DenseRange β := by
    simpa [β, MonoidHom.comp_apply] using
      (Function.Surjective.denseRange hρSurj).comp hβFdense ρ.continuous_toFun
  have hβSurj : Function.Surjective β :=
    surjective_of_denseRange (F := FreeGroup X) (P := P) hβDense
  obtain ⟨T, hTK⟩ := exists_rightSchreierTransversal (X := X) Lk
  let eQuot :
      Quotient (QuotientGroup.rightRel Lk) ≃ OpenSubgroupRightQuotient Hc := by
    simpa [Hc, OpenSubgroupRightQuotient] using
      (rightQuotientEquivOfComap ρ.toMonoidHom βF β K rfl hβSurj)
  let tRep : OpenSubgroupRightQuotient Hc → T := fun q =>
    hTK.1.rightQuotientEquiv (eQuot.symm q)
  have htRep_eq_of_mem {t : FreeGroup X} (ht : t ∈ T) :
      tRep (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc) = ⟨t, ht⟩ := by
    have hmk :
        (rightQuotientEquivOfComap ρ.toMonoidHom βF β K rfl hβSurj)
            (Quotient.mk'' t : Quotient (QuotientGroup.rightRel Lk)) =
          (Quotient.mk'' (βF t) :
            Quotient (QuotientGroup.rightRel (Subgroup.comap ρ.toMonoidHom K))) := by
      exact rightQuotientEquivOfComap_mk ρ.toMonoidHom βF β K rfl hβSurj t
    have hEq :
        eQuot.symm (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc) =
          (Quotient.mk'' t : Quotient (QuotientGroup.rightRel Lk)) := by
      exact eQuot.symm_apply_eq.mpr
        (by simpa [eQuot, Hc, OpenSubgroupRightQuotient] using hmk.symm)
    apply hTK.1.rightQuotientEquiv.symm.injective
    have hqt :
        (Quotient.mk'' t : Quotient (QuotientGroup.rightRel Lk)) =
          hTK.1.rightQuotientEquiv.symm ⟨t, ht⟩ := by
      simpa using
        hTK.1.mk''_rightQuotientEquiv
          (hTK.1.rightQuotientEquiv.symm ⟨t, ht⟩)
    simpa only [tRep, Equiv.symm_apply_apply] using hEq.trans hqt
  let ν :
      X → PermutationalWreathProduct Q (OpenSubgroupRightQuotient Hc) F := fun x =>
    ⟨fun q => ψK (schreierGenerator (X := X) hTK ((tRep q : T) : FreeGroup X) x), ι x⟩
  have hQproC : HasOpenNormalBasisInClass C Q := by
    exact HasOpenNormalBasisInClass.of_finite_discrete (C := C) (G := Q) hQuot hQ
  have hWreath :
      HasOpenNormalBasisInClass C
        (PermutationalWreathProduct Q (OpenSubgroupRightQuotient Hc) F) := by
    exact
      hasOpenNormalBasisInClass_permutationalWreathProduct
        (C := C) hForm hIso hExt hQproC hF.hasOpenNormalBasisInClass
  let W : Subgroup (PermutationalWreathProduct Q (OpenSubgroupRightQuotient Hc) F) :=
    (Subgroup.closure (Set.range ν)).topologicalClosure
  have hWproC : HasOpenNormalBasisInClass C W := by
    exact
      HasOpenNormalBasisInClass.of_isClosed_subgroup
        (C := C) (G := PermutationalWreathProduct Q (OpenSubgroupRightQuotient Hc) F)
        hIso hSub hWreath W (Subgroup.isClosed_topologicalClosure _)
  let hWclosed : IsClosed (W : Set (PermutationalWreathProduct Q (OpenSubgroupRightQuotient Hc)
      F)) := by
    simp [W]
  let : CompactSpace W := hWclosed.isClosedEmbedding_subtypeVal.compactSpace
  let νW : X → W := fun x =>
    ⟨ν x, Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨x, rfl⟩)⟩
  have hνWconv : FamilyConvergesToOneAlongOpenSubgroups (G := W) νW := by
    exact FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain (G := W) νW
  have hνWgen :
      ProCGroups.Generation.TopologicallyGenerates (G := W) (Set.range νW) := by
    simpa [W, νW] using topologicallyGenerates_topologicalClosure_of_range ν
  rcases hF.existsUnique_lift hWproC νW hνWconv hνWgen with
    ⟨ηW, hηW, _⟩
  let η : F →* PermutationalWreathProduct Q (OpenSubgroupRightQuotient Hc) F :=
    W.subtype.comp ηW
  have hηCont : Continuous η := by
    simpa [η] using (continuous_subtype_val.comp hηW.1)
  have hηOnGen : ∀ x : X, η (ι x) = ν x := by
    intro x
    simpa [η, νW] using congrArg Subtype.val (hηW.2 x)
  have hηRight :
      (SemidirectProduct.rightHom :
          PermutationalWreathProduct Q (OpenSubgroupRightQuotient Hc) F →* F).comp η =
        MonoidHom.id F := by
    rcases hF.existsUnique_lift hF.hasOpenNormalBasisInClass ι
        hF.convergesToOneAlongOpenSubgroups hF.generates_range with
      ⟨u, hu, huuniq⟩
    have hu_id : MonoidHom.id F = u := by
      exact
        huuniq (MonoidHom.id F)
          ⟨by simpa using (continuous_id : Continuous fun x : F => x), by intro x; rfl⟩
    have hu_η :
        (SemidirectProduct.rightHom :
            PermutationalWreathProduct Q (OpenSubgroupRightQuotient Hc) F →* F).comp η = u := by
      let v : F →* F :=
        (SemidirectProduct.rightHom :
            PermutationalWreathProduct Q (OpenSubgroupRightQuotient Hc) F →* F).comp η
      have hv_on_gen : ∀ x : X, v (ι x) = ι x := by
        intro x
        have hx := congrArg
          (fun z : PermutationalWreathProduct Q (OpenSubgroupRightQuotient Hc) F => z.right)
          (hηOnGen x)
        simpa [v, ν, MonoidHom.comp_apply] using hx
      exact huuniq v ⟨continuous_permutationalWreathProduct_right.comp hηCont, hv_on_gen⟩
    calc
      (SemidirectProduct.rightHom :
          PermutationalWreathProduct Q (OpenSubgroupRightQuotient Hc) F →* F).comp η = u := hu_η
      _ = MonoidHom.id F := hu_id.symm
  have hηCoord :
      ∀ q : OpenSubgroupRightQuotient Hc, ∀ x : X,
        wreathLeftCoordinate η q (βF (FreeGroup.of x)) =
          ψK (schreierGenerator (X := X) hTK ((tRep q : T) : FreeGroup X) x) := by
    intro q x
    simpa [wreathLeftCoordinate, βF, ν] using
      congrArg
        (fun z : PermutationalWreathProduct Q (OpenSubgroupRightQuotient Hc) F => z.left q)
        (hηOnGen x)
  have hηOne :
      ∀ {t : FreeGroup X}, t ∈ T → ∀ x : X,
        schreierGenerator (X := X) hTK t x = 1 →
          wreathLeftCoordinate η
            (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc)
            (βF (FreeGroup.of x)) = 1 := by
    intro t ht x hsg
    rw [hηCoord]
    rw [htRep_eq_of_mem (t := t) ht]
    simp only [hsg, map_one, ψK]
  have htPure :
      ∀ q : OpenSubgroupRightQuotient Hc,
        wreathLeftCoordinate η
          (Quotient.mk'' (1 : F) : OpenSubgroupRightQuotient Hc)
          (rightSchreierSectionOfComap ρ.toMonoidHom βF β K rfl hβSurj hTK q) = 1 := by
    intro q
    simpa [Hc, OpenSubgroupRightQuotient, β] using
      (wreathLeftCoordinate_basepoint_of_rightSchreierSectionOfComap
        (X := X) (φ := βF) (π := ρ.toMonoidHom) (K := K) (T := T)
        hTK hβSurj η hηRight hηOne q)
  let ψBarK : ↥(Hc : Subgroup F) →* Q :=
    rightQuotientBasepointProjectionHom (H := (Hc : Subgroup F)) η hηRight
  have hψBarKCont : Continuous ψBarK := by
    change Continuous
      ((fun z : PermutationalWreathProduct Q (OpenSubgroupRightQuotient Hc) F =>
          z.left (Quotient.mk'' (1 : F))) ∘ η ∘ Subtype.val)
    exact
      (continuous_permutationalWreathProduct_left_apply (A := Q)
        (S := OpenSubgroupRightQuotient Hc) (G := F)
        (Quotient.mk'' (1 : F) : OpenSubgroupRightQuotient Hc)).comp
          (hηCont.comp continuous_subtype_val)
  have hψBarKOnSchreier :
      ∀ s : ↥(schreierGeneratorSet (X := X) hTK),
        ψBarK (φK s) = ψK s := by
    rintro ⟨s, hs⟩
    rcases hs with ⟨t, ht, x, rfl, _hne⟩
    have hmap :
        φK (schreierGenerator (X := X) hTK t x) =
          rightQuotientSectionCocycle
            (H := (Hc : Subgroup F))
            (rightSchreierSectionOfComap ρ.toMonoidHom βF β K rfl hβSurj hTK)
            (rightSchreierSectionOfComap_spec ρ.toMonoidHom βF β K rfl hβSurj hTK)
            (βF (FreeGroup.of x))
            (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc) := by
      apply Subtype.ext
      have hcocycle :=
        congrArg Subtype.val
          (map_schreierGenerator_eq_cocycle
            (X := X) (φ := βF) (π := ρ.toMonoidHom) (K := K) hTK hβSurj ht x).symm
      change βF ↑(schreierGenerator (X := X) hTK t x) =
        ↑(rightQuotientSectionCocycle
          (H := (Hc : Subgroup F))
          (rightSchreierSectionOfComap ρ.toMonoidHom βF β K rfl hβSurj hTK)
          (rightSchreierSectionOfComap_spec
            ρ.toMonoidHom βF β K rfl hβSurj hTK)
          (βF (FreeGroup.of x))
          (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc))
      convert hcocycle using 1
    calc
      ψBarK (φK (schreierGenerator (X := X) hTK t x)) =
          ψBarK
            (rightQuotientSectionCocycle
              (H := (Hc : Subgroup F))
              (rightSchreierSectionOfComap ρ.toMonoidHom βF β K rfl hβSurj hTK)
              (rightSchreierSectionOfComap_spec
                ρ.toMonoidHom βF β K rfl hβSurj hTK)
              (βF (FreeGroup.of x))
              (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc)) := by
            rw [hmap]
      _ =
          wreathLeftCoordinate η
            (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc)
            (βF (FreeGroup.of x)) := by
            simpa [ψBarK, Hc, OpenSubgroupRightQuotient] using
              (rightQuotientBasepointProjectionHom_apply_cocycle
                (H := (Hc : Subgroup F))
                (τ := rightSchreierSectionOfComap ρ.toMonoidHom βF β K rfl hβSurj hTK)
                (hτ := rightSchreierSectionOfComap_spec
                  ρ.toMonoidHom βF β K rfl hβSurj hTK)
                (ψ := η) hηRight htPure
                (βF (FreeGroup.of x))
                (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc))
      _ = ψK (schreierGenerator (X := X) hTK t x) := by
            rw [hηCoord]
            rw [htRep_eq_of_mem (t := t) ht]
  have hψBarKFac : ψBarK.comp φK = ψK := by
    have hSchGen :
        ProCGroups.Generation.TopologicallyGenerates
          (G := Lk) (schreierGeneratorSet (X := X) hTK : Set Lk) := by
      rw [ProCGroups.Generation.topologicallyGenerates_iff_dense]
      rw [closure_schreierGeneratorSet_eq_top (X := X) hTK]
      exact dense_univ
    apply continuousMonoidHom_eq_of_agrees_on_topologicallyGeneratingSet
      (G := Lk) (A := Q) hSchGen
      (continuous_of_discreteTopology : Continuous (ψBarK.comp φK))
      (continuous_of_discreteTopology : Continuous ψK)
    intro h hh
    exact hψBarKOnSchreier ⟨h, hh⟩
  let ψBar : ↥(H : Subgroup F) →* Q := ψBarK.comp toHc
  have htoHcCont : Continuous toHc :=
    Continuous.subtype_mk continuous_subtype_val (by
      intro x
      exact (congrArg (fun S : Subgroup F => x.1 ∈ S) hcomap).mpr x.2)
  have hψBarCont : Continuous ψBar := hψBarKCont.comp htoHcCont
  refine ⟨ψBar, hψBarCont, ?_⟩
  apply MonoidHom.ext
  intro l
  have hto :
      toHc (φOrig l) = φK (toK l) := by
    ext
    rfl
  have hfrom :
      fromK (toK l) = l := by
    ext
    rfl
  have hfacK := congrArg (fun f : Lk →* Q => f (toK l)) hψBarKFac
  calc
    ψBar (φOrig l) = ψBarK (φK (toK l)) := by
      simpa [ψBar, MonoidHom.comp_apply] using congrArg ψBarK hto
    _ = ψK (toK l) := hfacK
    _ = ψ (fromK (toK l)) := rfl
    _ = ψ l := by rw [hfrom]

end FiniteQuotientLift

section ExactPointedRightSchreierGeneration

open ProCGroups.ProC

/--
An open subgroup of a pointed free pro-\(C\) group admits a compact right Schreier generator
family whose image, pointed at the distinguished generator 1, is itself a pointed free pro-\(C\)
basis of the open subgroup.
-/
theorem exists_pointedFreeRightSchreierGeneratorFamily_of_openSubgroup
    {C : ProCGroups.FiniteGroupClass.{u}}
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {x0 : X}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
      [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyPointedFreeProCGroupOn
      (C := C) X x0 F ι)
    (H : OpenSubgroup F) :
    ∃ κ : OpenSubgroupRightQuotient H × X → ↥(H : Subgroup F),
      Continuous κ ∧
      (∀ q : OpenSubgroupRightQuotient H, κ (q, x0) = 1) ∧
      κ (openSubgroupRightCoset H (1 : F), x0) = 1 ∧
      IsCompact (Set.range κ) ∧
      IsClosed (Set.range κ) ∧
      IsEpimorphicallyPointedFreeProCGroupOn
        (C := C)
        (Set.range κ)
        ⟨κ (openSubgroupRightCoset H (1 : F), x0),
          ⟨(openSubgroupRightCoset H (1 : F), x0), rfl⟩⟩
        ↥(H : Subgroup F) Subtype.val := by
  classical
  let n : ℕ := Nat.card (F ⧸ (H : Subgroup F))
  let hn : Nat.card (F ⧸ (H : Subgroup F)) = n := rfl
  let P := openSubgroupIndexActionRange (G := F) H hn
  let ρ : F →ₜ* P := openSubgroupIndexActionRangeContinuousHom (G := F) H hn
  let q0 : F ⧸ (H : Subgroup F) := QuotientGroup.mk (s := (H : Subgroup F)) (1 : F)
  let K : Subgroup P := MulAction.stabilizer P q0
  let βF : FreeGroup X →* F := FreeGroup.lift ι
  let β : FreeGroup X →* P := ρ.toMonoidHom.comp βF
  let : TopologicalSpace (FreeGroup X) := ⊥
  let : DiscreteTopology (FreeGroup X) := ⟨rfl⟩
  have hcomap : Subgroup.comap ρ.toMonoidHom K = (H : Subgroup F) := by
    ext g
    constructor
    · intro hg
      change ρ g • q0 = q0 at hg
      rw [openSubgroupIndexActionRangeContinuousHom_smul_basepoint (G := F) H hn g] at hg
      change (QuotientGroup.mk (s := (H : Subgroup F)) g : F ⧸ (H : Subgroup F)) =
          QuotientGroup.mk (s := (H : Subgroup F)) (1 : F) at hg
      simpa [QuotientGroup.eq] using hg
    · intro hg
      change ρ g • q0 = q0
      exact openSubgroupIndexActionRangeContinuousHom_smul_basepoint_of_mem (G := F) H hn hg
  have hβFdense : DenseRange βF :=
    denseRange_freeGroupLift_of_topologicallyGenerates (F := F) (X := X) hF.generates_range
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
  obtain ⟨T, hT⟩ := exists_rightSchreierTransversal (X := X) (Subgroup.comap β K)
  have hβFcomapDense :
      DenseRange
        ({ toFun := fun g : Subgroup.comap β K => ⟨βF g.1, g.2⟩
           map_one' := by
             apply Subtype.ext
             exact βF.map_one
           map_mul' := by
             intro a b
             apply Subtype.ext
             exact βF.map_mul a b} :
          Subgroup.comap β K →* ↥(Subgroup.comap ρ.toMonoidHom K)) := by
    have hρKopen : IsOpen ((Subgroup.comap ρ.toMonoidHom K : Subgroup F) : Set F) := by
      rw [hcomap]
      exact H.isOpen'
    exact denseRange_comapMap_of_openSubgroup
      (φ := βF) hβFdense (U := Subgroup.comap ρ.toMonoidHom K) hρKopen
  let Hc : OpenSubgroup F :=
    { toSubgroup := Subgroup.comap ρ.toMonoidHom K
      isOpen' := by
        rw [hcomap]
        exact H.isOpen' }
  have hHc : Hc = H := by
    ext g
    change g ∈ Subgroup.comap ρ.toMonoidHom K ↔ g ∈ (H : Subgroup F)
    rw [hcomap]
  have hκgenPre :
      let τ := rightSchreierSectionOfComap ρ.toMonoidHom βF β K rfl hβsurj hT
      let hτ := rightSchreierSectionOfComap_spec ρ.toMonoidHom βF β K rfl hβsurj hT
      let κ :
          Quotient (QuotientGroup.rightRel (Subgroup.comap ρ.toMonoidHom K)) × X →
            ↥(Subgroup.comap ρ.toMonoidHom K) :=
        fun p =>
          rightQuotientSectionCocycle
            (H := Subgroup.comap ρ.toMonoidHom K) τ hτ (βF (FreeGroup.of p.2)) p.1
      ProCGroups.Generation.TopologicallyGenerates
        (G := ↥(Subgroup.comap ρ.toMonoidHom K)) (Set.range κ) := by
    exact topologicallyGenerates_range_transportedCocycle
      (X := X) (φ := βF) (π := ρ.toMonoidHom) (K := K) hT hβsurj hβFcomapDense
  let GoalProp : OpenSubgroup F → Prop := fun J =>
    ∃ κ : OpenSubgroupRightQuotient J × X → ↥(J : Subgroup F),
      Continuous κ ∧
      (∀ q : OpenSubgroupRightQuotient J, κ (q, x0) = 1) ∧
      κ (openSubgroupRightCoset J (1 : F), x0) = 1 ∧
      IsCompact (Set.range κ) ∧
      IsClosed (Set.range κ) ∧
      IsEpimorphicallyPointedFreeProCGroupOn
        (C := C)
        (Set.range κ)
        ⟨κ (openSubgroupRightCoset J (1 : F), x0),
          ⟨(openSubgroupRightCoset J (1 : F), x0), rfl⟩⟩
        ↥(J : Subgroup F) Subtype.val
  have hMain : GoalProp Hc := by
    let : DiscreteTopology (OpenSubgroupRightQuotient Hc) :=
      discreteTopology_openSubgroupRightQuotient (F := F) Hc
    let : ContinuousSMul F (OpenSubgroupRightQuotient Hc) := by
      refine ContinuousSMul.mk ?_
      refine (continuous_prod_of_discrete_right).2 ?_
      intro q
      convert
        (continuous_rightCosetMulAction_inv_smul_of_open
          (G := F) (H := (Hc : Subgroup F)) Hc.isOpen' q).comp continuous_inv using 1
      ext g
      simp only [Function.comp_apply, inv_inv]
    let q1 : OpenSubgroupRightQuotient Hc := openSubgroupRightCoset Hc (1 : F)
    let τ : OpenSubgroupRightQuotient Hc → F := by
      simpa [Hc, OpenSubgroupRightQuotient] using
        (rightSchreierSectionOfComap ρ.toMonoidHom βF β K rfl hβsurj hT)
    have hτ : ∀ q : OpenSubgroupRightQuotient Hc, Quotient.mk'' (τ q) = q := by
      intro q
      change
        Quotient.mk'' ((rightSchreierSectionOfComap ρ.toMonoidHom βF β K rfl hβsurj hT) q) = q
      exact rightSchreierSectionOfComap_spec ρ.toMonoidHom βF β K rfl hβsurj hT q
    let κ : OpenSubgroupRightQuotient Hc × X → ↥(Hc : Subgroup F) :=
      fun p =>
        rightSchreierGenerator
          (F := F) (H := Hc) (τ := τ) (hτ := hτ) (ι := ι) p.1 p.2
    have hκgen :
        ProCGroups.Generation.TopologicallyGenerates (G := ↥(Hc : Subgroup F)) (Set.range κ) := by
      simpa [κ, rightSchreierGenerator, τ, Hc, OpenSubgroupRightQuotient, βF] using hκgenPre
    have hτcont : Continuous τ := continuous_of_discreteTopology
    have hκcont : Continuous κ := by
      exact continuous_rightSchreierGenerator
        (F := F) (H := Hc) (τ := τ) (hτ := hτ) (ι := ι) hτcont hF.continuous_ι
    have hκ1 : κ (q1, x0) = 1 := by
      simpa [κ, rightSchreierGenerator, βF] using
        (rightSchreierGenerator_eq_one
          (F := F) (H := Hc) (τ := τ) (hτ := hτ) (ι := ι) (q := q1) (x := x0) hF.map_base)
    have hκbase : ∀ q : OpenSubgroupRightQuotient Hc, κ (q, x0) = 1 := by
      intro q
      simpa [κ, rightSchreierGenerator, βF] using
        (rightSchreierGenerator_eq_one
          (F := F) (H := Hc) (τ := τ) (hτ := hτ) (ι := ι) (q := q) (x := x0) hF.map_base)
    refine ⟨κ, hκcont, hκbase, hκ1, isCompact_range hκcont, (isCompact_range hκcont).isClosed, ?_⟩
    let : CompactSpace ↥(Hc : Subgroup F) :=
      compactSpace_openSubgroupSubtype (F := F) Hc
    refine ⟨?_, continuous_subtype_val, ?_, ?_, ?_⟩
    · exact
        HasOpenNormalBasisInClass.of_isClosed_subgroup
          (C := C) (G := F) hIso hSub hF.hasOpenNormalBasisInClass (Hc : Subgroup F)
          (Subgroup.isClosed_of_isOpen (Hc : Subgroup F) Hc.isOpen')
    · simpa [hκ1]
    · have hrange :
          Set.range (Subtype.val : Set.range κ → ↥(Hc : Subgroup F)) = Set.range κ := by
        ext h
        constructor
        · rintro ⟨x, rfl⟩
          exact x.2
        · intro hh
          exact ⟨⟨h, hh⟩, rfl⟩
      simpa [hrange] using hκgen
    · intro B _ _ _ _ _ _ hB φB hφB hφB0 hgenB
      let ξ : X → PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F :=
        fun x => ⟨fun q => φB ⟨κ (q, x), ⟨(q, x), rfl⟩⟩, ι x⟩
      have hξcont : Continuous ξ := by
        refine continuous_induced_rng.2 ?_
        change Continuous fun x : X => ((ξ x).left, (ξ x).right)
        have hleft : Continuous fun x : X => (ξ x).left := by
          refine continuous_pi ?_
          intro q
          have hqcont : Continuous fun x : X => κ (q, x) := by
            change Continuous (κ ∘ fun x : X => (q, x))
            exact hκcont.comp (continuous_const.prodMk continuous_id)
          have hsub :
              Continuous fun x : X => (⟨κ (q, x), ⟨(q, x), rfl⟩⟩ : Set.range κ) :=
            Continuous.subtype_mk hqcont (by
              intro x
              exact ⟨(q, x), rfl⟩)
          change Continuous (φB ∘ fun x : X =>
            (⟨κ (q, x), ⟨(q, x), rfl⟩⟩ : Set.range κ))
          exact hφB.comp hsub
        have hright : Continuous fun x : X => (ξ x).right := by
          simpa [ξ] using hF.continuous_ι
        exact hleft.prodMk hright
      have hξ0 : ξ x0 = 1 := by
        apply SemidirectProduct.ext
        · funext q
          have hq1 : κ (q, x0) = 1 := by
            simpa [κ, rightSchreierGenerator, βF] using
              (rightSchreierGenerator_eq_one
                (F := F) (H := Hc) (τ := τ) (hτ := hτ) (ι := ι) (q := q) (x := x0)
                hF.map_base)
          have hsrc :
              (⟨κ (q, x0), ⟨(q, x0), rfl⟩⟩ : Set.range κ) =
                ⟨κ (q1, x0), ⟨(q1, x0), rfl⟩⟩ := by
            apply Subtype.ext
            exact hq1.trans hκ1.symm
          calc
            (ξ x0).left q = φB ⟨κ (q, x0), ⟨(q, x0), rfl⟩⟩ := rfl
            _ = φB ⟨κ (q1, x0), ⟨(q1, x0), rfl⟩⟩ := by rw [hsrc]
            _ = 1 := hφB0
        · simp only [hF.map_base, SemidirectProduct.one_right, ξ]
      let W : Subgroup (PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F) :=
        (Subgroup.closure (Set.range ξ)).topologicalClosure
      have hWreath :
          HasOpenNormalBasisInClass C (PermutationalWreathProduct B (OpenSubgroupRightQuotient
              Hc) F) := by
        exact
          hasOpenNormalBasisInClass_permutationalWreathProduct
            (C := C) hForm hIso hExt hB hF.hasOpenNormalBasisInClass
      have hWproC : HasOpenNormalBasisInClass C W := by
        exact
          HasOpenNormalBasisInClass.of_isClosed_subgroup
            (C := C) (G := PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F)
            hIso hSub hWreath W (Subgroup.isClosed_topologicalClosure _)
      let hWclosed : IsClosed (W : Set (PermutationalWreathProduct B (OpenSubgroupRightQuotient
          Hc) F)) := by
        simp [W]
      let : CompactSpace W := hWclosed.isClosedEmbedding_subtypeVal.compactSpace
      let ξW : X → W := fun x =>
        ⟨ξ x, Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨x, rfl⟩)⟩
      have hξWcont : Continuous ξW :=
        Continuous.subtype_mk hξcont (by
          intro x
          exact Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨x, rfl⟩))
      have hξW0 : ξW x0 = 1 := by
        apply Subtype.ext
        exact hξ0
      have hξWgen :
          ProCGroups.Generation.TopologicallyGenerates (G := W) (Set.range ξW) := by
        simpa [W, ξW] using
          topologicallyGenerates_topologicalClosure_of_range (ξ := ξ)
      rcases hF.existsUnique_lift hWproC ξW hξWcont hξW0 hξWgen with
        ⟨ηW, hηW, _⟩
      let η : F →* PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F :=
        W.subtype.comp ηW
      have hηcont : Continuous η := by
        simpa [η] using (continuous_subtype_val.comp hηW.1)
      have hηgen : ∀ x : X, η (ι x) = ξ x := by
        intro x
        simpa [η, ξW] using congrArg Subtype.val (hηW.2 x)
      have hηright :
          (SemidirectProduct.rightHom :
              PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F →* F).comp η =
            MonoidHom.id F := by
        rcases
            hF.existsUnique_lift hF.hasOpenNormalBasisInClass ι hF.continuous_ι hF.map_base
                hF.generates_range with
          ⟨u, hu, huuniq⟩
        have hu_id : MonoidHom.id F = u := by
          exact
            huuniq (MonoidHom.id F)
              ⟨by simpa using (continuous_id : Continuous fun x : F => x), by intro x; rfl⟩
        have hu_η :
            (SemidirectProduct.rightHom :
                PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F →* F).comp η =
              u := by
          let v : F →* F :=
            (SemidirectProduct.rightHom :
                PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F →* F).comp η
          have hη_on_gen :
              ∀ x : X, v (ι x) = ι x := by
            intro x
            have hx := congrArg
              (fun z : PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F => z.right)
              (hηgen x)
            simpa [v, MonoidHom.comp_apply, ξ] using hx
          have hvu : v = u := by
            exact huuniq v ⟨continuous_permutationalWreathProduct_right.comp hηcont, hη_on_gen⟩
          simpa [v] using hvu
        calc
          (SemidirectProduct.rightHom :
              PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F →* F).comp η = u :=
            hu_η
          _ = MonoidHom.id F := hu_id.symm
      have hηcoord :
          ∀ q : OpenSubgroupRightQuotient Hc, ∀ x : X,
            wreathLeftCoordinate η q (ι x) =
              φB ⟨κ (q, x), ⟨(q, x), rfl⟩⟩ := by
        intro q x
        change (η (ι x)).left q = _
        rw [hηgen]
      have hηone :
          ∀ {t : FreeGroup X}, t ∈ T → ∀ x : X,
            schreierGenerator (X := X) hT t x = 1 →
              wreathLeftCoordinate η
                (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc)
                (βF (FreeGroup.of x)) = 1 := by
        intro t ht x hsg
        have hmap :
            κ (Quotient.mk'' (βF t), x) = 1 := by
          apply Subtype.ext
          have hcocycle :=
            congrArg Subtype.val
              (map_schreierGenerator_eq_cocycle
                (X := X) (φ := βF) (π := ρ.toMonoidHom) (K := K) hT hβsurj ht x)
          change (↑(κ (Quotient.mk'' (βF t), x)) : F) = 1
          calc
            (↑(κ (Quotient.mk'' (βF t), x)) : F) =
                βF ↑(schreierGenerator (X := X) hT t x) := by
              simpa [κ, rightSchreierGenerator, τ, Hc,
                OpenSubgroupRightQuotient, β, βF] using hcocycle
            _ = 1 := by rw [hsg]; exact βF.map_one
        have hsrc :
            (⟨κ (Quotient.mk'' (βF t), x), ⟨(Quotient.mk'' (βF t), x), rfl⟩⟩ : Set.range κ) =
              ⟨κ (q1, x0), ⟨(q1, x0), rfl⟩⟩ := by
          apply Subtype.ext
          exact hmap.trans hκ1.symm
        calc
          wreathLeftCoordinate η
              (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc)
              (βF (FreeGroup.of x))
              =
            wreathLeftCoordinate η
              (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc) (ι x) := by
                simp only [FreeGroup.lift_apply_of, βF]
          _ = φB ⟨κ (Quotient.mk'' (βF t), x), ⟨(Quotient.mk'' (βF t), x), rfl⟩⟩ :=
                hηcoord _ _
          _ = φB ⟨κ (q1, x0), ⟨(q1, x0), rfl⟩⟩ := by rw [hsrc]
          _ = 1 := hφB0
      have hτpure :
          ∀ q : OpenSubgroupRightQuotient Hc,
            wreathLeftCoordinate η q1 (τ q) = 1 := by
        intro q
        simpa [q1, τ, Hc, OpenSubgroupRightQuotient, openSubgroupRightCoset,
          rightCoset, β, βF] using
          (wreathLeftCoordinate_basepoint_of_rightSchreierSectionOfComap
            (X := X) (φ := βF) (π := ρ.toMonoidHom) (K := K) hT hβsurj η hηright
            (hone := hηone) q)
      let g : ↥(Hc : Subgroup F) →* B :=
        rightQuotientBasepointProjectionHom (H := (Hc : Subgroup F)) η hηright
      have hgcont : Continuous g := by
        change Continuous
          ((fun z : PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F =>
              z.left q1) ∘ η ∘ Subtype.val)
        exact
          (continuous_permutationalWreathProduct_left_apply (A := B)
            (S := OpenSubgroupRightQuotient Hc) (G := F) q1).comp
            (hηcont.comp continuous_subtype_val)
      have hgfac : ∀ y : Set.range κ, g y.1 = φB y := by
        rintro ⟨y, ⟨⟨q, x⟩, hy⟩⟩
        subst y
        change g (κ (q, x)) = φB ⟨κ (q, x), ⟨(q, x), rfl⟩⟩
        calc
          g (κ (q, x)) = wreathLeftCoordinate η q (βF (FreeGroup.of x)) := by
            simpa [g, κ, τ, βF] using
              (rightQuotientBasepointProjectionHom_rightSchreierGenerator
                (F := F) (H := Hc) (τ := τ) (hτ := hτ) (ι := ι) η hηright hτpure q x)
          _ = wreathLeftCoordinate η q (ι x) := by simp only [FreeGroup.lift_apply_of, βF]
          _ = φB ⟨κ (q, x), ⟨(q, x), rfl⟩⟩ := hηcoord q x
      refine ⟨g, ⟨hgcont, hgfac⟩, ?_⟩
      intro g' hg'
      symm
      apply continuousMonoidHom_eq_of_agrees_on_topologicallyGeneratingSet
        (G := ↥(Hc : Subgroup F)) (A := B) hκgen hgcont hg'.1
      intro h hh
      exact (hgfac ⟨h, hh⟩).trans (hg'.2 ⟨h, hh⟩).symm
  exact cast (congrArg GoalProp hHc) hMain

end ExactPointedRightSchreierGeneration



/--
There exists a pointed free right-Schreier generator family for the open subgroup under the
minimal generator-power hypothesis.
-/
theorem exists_pointedFreeRightSchreierGeneratorFamily_of_openSubgroup_of_minimalGeneratorPower
    {C : ProCGroups.FiniteGroupClass.{u}}
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {x0 : X}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
      [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyPointedFreeProCGroupOn
      (C := C) X x0 F ι)
    (H : OpenSubgroup F) (x : X) {N : ℕ}
    (hN : 0 < N)
    (hpow : (ι x) ^ N ∈ (H : Subgroup F))
    (hmin : ∀ m : ℕ, 0 < m → m < N → (ι x) ^ m ∉ (H : Subgroup F)) :
    ∃ κ : OpenSubgroupRightQuotient H × X → ↥(H : Subgroup F),
      Continuous κ ∧
      (∀ q : OpenSubgroupRightQuotient H, κ (q, x0) = 1) ∧
      κ (openSubgroupRightCoset H (1 : F), x0) = 1 ∧
      (⟨(ι x) ^ N, hpow⟩ : ↥(H : Subgroup F)) ∈ Set.range κ ∧
      IsCompact (Set.range κ) ∧
      IsClosed (Set.range κ) ∧
      IsEpimorphicallyPointedFreeProCGroupOn
        (C := C)
        (Set.range κ)
        ⟨κ (openSubgroupRightCoset H (1 : F), x0),
          ⟨(openSubgroupRightCoset H (1 : F), x0), rfl⟩⟩
        ↥(H : Subgroup F) Subtype.val := by
  classical
  let n : ℕ := Nat.card (F ⧸ (H : Subgroup F))
  let hn : Nat.card (F ⧸ (H : Subgroup F)) = n := rfl
  let P := openSubgroupIndexActionRange (G := F) H hn
  let ρ : F →ₜ* P := openSubgroupIndexActionRangeContinuousHom (G := F) H hn
  let q0 : F ⧸ (H : Subgroup F) := QuotientGroup.mk (s := (H : Subgroup F)) (1 : F)
  let K : Subgroup P := MulAction.stabilizer P q0
  let βF : FreeGroup X →* F := FreeGroup.lift ι
  let β : FreeGroup X →* P := ρ.toMonoidHom.comp βF
  let βc : Subgroup.comap β K →* ↥(Subgroup.comap ρ.toMonoidHom K) :=
    { toFun := fun g => ⟨βF g.1, g.2⟩
      map_one' := by
        apply Subtype.ext
        exact βF.map_one
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact βF.map_mul a b}
  let : TopologicalSpace (FreeGroup X) := ⊥
  let : DiscreteTopology (FreeGroup X) := ⟨rfl⟩
  have hcomap : Subgroup.comap ρ.toMonoidHom K = (H : Subgroup F) := by
    ext g
    constructor
    · intro hg
      change ρ g • q0 = q0 at hg
      rw [openSubgroupIndexActionRangeContinuousHom_smul_basepoint (G := F) H hn g] at hg
      change (QuotientGroup.mk (s := (H : Subgroup F)) g : F ⧸ (H : Subgroup F)) =
          QuotientGroup.mk (s := (H : Subgroup F)) (1 : F) at hg
      simpa [QuotientGroup.eq] using hg
    · intro hg
      change ρ g • q0 = q0
      exact openSubgroupIndexActionRangeContinuousHom_smul_basepoint_of_mem (G := F) H hn hg
  have hβFdense : DenseRange βF :=
    denseRange_freeGroupLift_of_topologicallyGenerates (F := F) (X := X) hF.generates_range
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
  have hpowβ : (FreeGroup.of x) ^ N ∈ Subgroup.comap β K := by
    change βF ((FreeGroup.of x) ^ N) ∈ Subgroup.comap ρ.toMonoidHom K
    rw [hcomap]
    simpa [βF, MonoidHom.map_pow] using hpow
  have hminβ :
      ∀ m : ℕ, 0 < m → m < N → (FreeGroup.of x) ^ m ∉ Subgroup.comap β K := by
    intro m hm0 hmN hm
    apply hmin m hm0 hmN
    change βF ((FreeGroup.of x) ^ m) ∈ Subgroup.comap ρ.toMonoidHom K at hm
    rw [hcomap] at hm
    simpa [βF, MonoidHom.map_pow] using hm
  obtain ⟨T, hT, hpred, hsg⟩ :=
    exists_rightSchreierTransversal_of_minimalGeneratorPower
      (X := X) (L := Subgroup.comap β K) x hN hpowβ hminβ
  have hβFcomapDense : DenseRange βc := by
    have hρKopen : IsOpen ((Subgroup.comap ρ.toMonoidHom K : Subgroup F) : Set F) := by
      rw [hcomap]
      exact H.isOpen'
    change DenseRange (fun g : Subgroup.comap β K =>
      (⟨βF g.1, g.2⟩ : ↥(Subgroup.comap ρ.toMonoidHom K)))
    have hdense := denseRange_comapMap_of_openSubgroup
      (φ := βF) hβFdense (U := Subgroup.comap ρ.toMonoidHom K) hρKopen
    change DenseRange (fun g : Subgroup.comap βF (Subgroup.comap ρ.toMonoidHom K) =>
      (⟨βF g.1, g.2⟩ : ↥(Subgroup.comap ρ.toMonoidHom K))) at hdense
    simpa [β, Subgroup.comap_comap] using hdense
  let Hc : OpenSubgroup F :=
    { toSubgroup := Subgroup.comap ρ.toMonoidHom K
      isOpen' := by
        rw [hcomap]
        exact H.isOpen' }
  have hHc : Hc = H := by
    ext g
    change g ∈ Subgroup.comap ρ.toMonoidHom K ↔ g ∈ (H : Subgroup F)
    rw [hcomap]
  have hκgenPre :
      let τ := rightSchreierSectionOfComap ρ.toMonoidHom βF β K rfl hβsurj hT
      let hτ := rightSchreierSectionOfComap_spec ρ.toMonoidHom βF β K rfl hβsurj hT
      let κ :
          Quotient (QuotientGroup.rightRel (Subgroup.comap ρ.toMonoidHom K)) × X →
            ↥(Subgroup.comap ρ.toMonoidHom K) :=
        fun p =>
          rightQuotientSectionCocycle
            (H := Subgroup.comap ρ.toMonoidHom K) τ hτ (βF (FreeGroup.of p.2)) p.1
      ProCGroups.Generation.TopologicallyGenerates
        (G := ↥(Subgroup.comap ρ.toMonoidHom K)) (Set.range κ) := by
    exact topologicallyGenerates_range_transportedCocycle
      (X := X) (φ := βF) (π := ρ.toMonoidHom) (K := K) hT hβsurj hβFcomapDense
  let GoalProp : OpenSubgroup F → Prop := fun J =>
    ∃ κ : OpenSubgroupRightQuotient J × X → ↥(J : Subgroup F),
      Continuous κ ∧
      (∀ q : OpenSubgroupRightQuotient J, κ (q, x0) = 1) ∧
      κ (openSubgroupRightCoset J (1 : F), x0) = 1 ∧
      (∃ hpowJ : (ι x) ^ N ∈ (J : Subgroup F),
        (⟨(ι x) ^ N, hpowJ⟩ : ↥(J : Subgroup F)) ∈ Set.range κ) ∧
      IsCompact (Set.range κ) ∧
      IsClosed (Set.range κ) ∧
      IsEpimorphicallyPointedFreeProCGroupOn
        (C := C)
        (Set.range κ)
        ⟨κ (openSubgroupRightCoset J (1 : F), x0),
          ⟨(openSubgroupRightCoset J (1 : F), x0), rfl⟩⟩
        ↥(J : Subgroup F) Subtype.val
  have hMain : GoalProp Hc := by
    let : DiscreteTopology (OpenSubgroupRightQuotient Hc) :=
      discreteTopology_openSubgroupRightQuotient (F := F) Hc
    let : ContinuousSMul F (OpenSubgroupRightQuotient Hc) := by
      refine ContinuousSMul.mk ?_
      refine (continuous_prod_of_discrete_right).2 ?_
      intro q
      convert
        (continuous_rightCosetMulAction_inv_smul_of_open
          (G := F) (H := (Hc : Subgroup F)) Hc.isOpen' q).comp continuous_inv using 1
      ext g
      simp only [Function.comp_apply, inv_inv]
    let q1 : OpenSubgroupRightQuotient Hc := openSubgroupRightCoset Hc (1 : F)
    let τ : OpenSubgroupRightQuotient Hc → F := by
      simpa [Hc, OpenSubgroupRightQuotient] using
        (rightSchreierSectionOfComap ρ.toMonoidHom βF β K rfl hβsurj hT)
    have hτ : ∀ q : OpenSubgroupRightQuotient Hc, Quotient.mk'' (τ q) = q := by
      intro q
      change
        Quotient.mk'' ((rightSchreierSectionOfComap ρ.toMonoidHom βF β K rfl hβsurj hT) q) = q
      exact rightSchreierSectionOfComap_spec ρ.toMonoidHom βF β K rfl hβsurj hT q
    let κ : OpenSubgroupRightQuotient Hc × X → ↥(Hc : Subgroup F) :=
      fun p =>
        rightSchreierGenerator
          (F := F) (H := Hc) (τ := τ) (hτ := hτ) (ι := ι) p.1 p.2
    have hκgen :
        ProCGroups.Generation.TopologicallyGenerates (G := ↥(Hc : Subgroup F)) (Set.range κ) := by
      simpa [κ, rightSchreierGenerator, τ, Hc, OpenSubgroupRightQuotient, βF] using hκgenPre
    have hτcont : Continuous τ := continuous_of_discreteTopology
    have hκcont : Continuous κ := by
      exact continuous_rightSchreierGenerator
        (F := F) (H := Hc) (τ := τ) (hτ := hτ) (ι := ι) hτcont hF.continuous_ι
    have hκ1 : κ (q1, x0) = 1 := by
      simpa [κ, rightSchreierGenerator, βF] using
        (rightSchreierGenerator_eq_one
          (F := F) (H := Hc) (τ := τ) (hτ := hτ) (ι := ι) (q := q1) (x := x0) hF.map_base)
    have hκbase : ∀ q : OpenSubgroupRightQuotient Hc, κ (q, x0) = 1 := by
      intro q
      simpa [κ, rightSchreierGenerator, βF] using
        (rightSchreierGenerator_eq_one
          (F := F) (H := Hc) (τ := τ) (hτ := hτ) (ι := ι) (q := q) (x := x0) hF.map_base)
    have hpowHc : (ι x) ^ N ∈ (Hc : Subgroup F) := by
      change (ι x) ^ N ∈ Subgroup.comap ρ.toMonoidHom K
      rw [hcomap]
      exact hpow
    have hxNrange : (⟨(ι x) ^ N, hpowHc⟩ : ↥(Hc : Subgroup F)) ∈ Set.range κ := by
      have hmap :
          κ ((Quotient.mk'' (βF ((FreeGroup.of x) ^ (N - 1))) : OpenSubgroupRightQuotient Hc), x) =
            βc (schreierGenerator (X := X) hT ((FreeGroup.of x) ^ (N - 1)) x) := by
        apply Subtype.ext
        have hcocycle :=
          congrArg Subtype.val
            (map_schreierGenerator_eq_cocycle
              (X := X) (φ := βF) (π := ρ.toMonoidHom) (K := K) hT hβsurj hpred x)
        change (↑(κ
          ((Quotient.mk'' (βF ((FreeGroup.of x) ^ (N - 1))) :
            OpenSubgroupRightQuotient Hc), x)) : F) =
          βF ↑(schreierGenerator (X := X) hT ((FreeGroup.of x) ^ (N - 1)) x)
        simpa [βc, κ, rightSchreierGenerator, τ, Hc,
          OpenSubgroupRightQuotient, β, βF] using hcocycle
      have hβc_pow : βc ⟨(FreeGroup.of x) ^ N, hpowβ⟩ = ⟨(ι x) ^ N, hpowHc⟩ := by
        apply Subtype.ext
        change βF (FreeGroup.of x ^ N) = ι x ^ N
        rw [map_pow]
        simp only [FreeGroup.lift_apply_of, βF]
      refine
        ⟨((Quotient.mk'' (βF ((FreeGroup.of x) ^ (N - 1))) :
            OpenSubgroupRightQuotient Hc), x), ?_⟩
      calc
        κ ((Quotient.mk'' (βF ((FreeGroup.of x) ^ (N - 1))) : OpenSubgroupRightQuotient Hc), x) =
            βc (schreierGenerator (X := X) hT ((FreeGroup.of x) ^ (N - 1)) x) := hmap
        _ = βc ⟨(FreeGroup.of x) ^ N, hpowβ⟩ := by rw [hsg]
        _ = ⟨(ι x) ^ N, hpowHc⟩ := hβc_pow
    refine ⟨κ, hκcont, hκbase, hκ1, ⟨hpowHc, hxNrange⟩,
      isCompact_range hκcont, (isCompact_range hκcont).isClosed, ?_⟩
    let : CompactSpace ↥(Hc : Subgroup F) :=
      compactSpace_openSubgroupSubtype (F := F) Hc
    refine ⟨?_, continuous_subtype_val, ?_, ?_, ?_⟩
    · exact
        HasOpenNormalBasisInClass.of_isClosed_subgroup
          (C := C) (G := F) hIso hSub hF.hasOpenNormalBasisInClass (Hc : Subgroup F)
          (Subgroup.isClosed_of_isOpen (Hc : Subgroup F) Hc.isOpen')
    · simpa [hκ1]
    · have hrange :
          Set.range (Subtype.val : Set.range κ → ↥(Hc : Subgroup F)) = Set.range κ := by
        ext h
        constructor
        · rintro ⟨x, rfl⟩
          exact x.2
        · intro hh
          exact ⟨⟨h, hh⟩, rfl⟩
      simpa [hrange] using hκgen
    · intro B _ _ _ _ _ _ hB φB hφB hφB0 hgenB
      let ξ : X → PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F :=
        fun x => ⟨fun q => φB ⟨κ (q, x), ⟨(q, x), rfl⟩⟩, ι x⟩
      have hξcont : Continuous ξ := by
        refine continuous_induced_rng.2 ?_
        change Continuous fun x : X => ((ξ x).left, (ξ x).right)
        have hleft : Continuous fun x : X => (ξ x).left := by
          refine continuous_pi ?_
          intro q
          have hqcont : Continuous fun x : X => κ (q, x) := by
            change Continuous (κ ∘ fun x : X => (q, x))
            exact hκcont.comp (continuous_const.prodMk continuous_id)
          have hsub :
              Continuous fun x : X => (⟨κ (q, x), ⟨(q, x), rfl⟩⟩ : Set.range κ) :=
            Continuous.subtype_mk hqcont (by
              intro x
              exact ⟨(q, x), rfl⟩)
          change Continuous (φB ∘ fun x : X =>
            (⟨κ (q, x), ⟨(q, x), rfl⟩⟩ : Set.range κ))
          exact hφB.comp hsub
        have hright : Continuous fun x : X => (ξ x).right := by
          simpa [ξ] using hF.continuous_ι
        exact hleft.prodMk hright
      have hξ0 : ξ x0 = 1 := by
        apply SemidirectProduct.ext
        · funext q
          have hq1 : κ (q, x0) = 1 := by
            simpa [κ, rightSchreierGenerator, βF] using
              (rightSchreierGenerator_eq_one
                (F := F) (H := Hc) (τ := τ) (hτ := hτ) (ι := ι) (q := q) (x := x0)
                hF.map_base)
          have hsrc :
              (⟨κ (q, x0), ⟨(q, x0), rfl⟩⟩ : Set.range κ) =
                ⟨κ (q1, x0), ⟨(q1, x0), rfl⟩⟩ := by
            apply Subtype.ext
            exact hq1.trans hκ1.symm
          calc
            (ξ x0).left q = φB ⟨κ (q, x0), ⟨(q, x0), rfl⟩⟩ := rfl
            _ = φB ⟨κ (q1, x0), ⟨(q1, x0), rfl⟩⟩ := by rw [hsrc]
            _ = 1 := hφB0
        · simp only [hF.map_base, SemidirectProduct.one_right, ξ]
      let W : Subgroup (PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F) :=
        (Subgroup.closure (Set.range ξ)).topologicalClosure
      have hWreath :
          HasOpenNormalBasisInClass C (PermutationalWreathProduct B (OpenSubgroupRightQuotient
              Hc) F) := by
        exact
          hasOpenNormalBasisInClass_permutationalWreathProduct
            (C := C) hForm hIso hExt hB hF.hasOpenNormalBasisInClass
      have hWproC : HasOpenNormalBasisInClass C W := by
        exact
          HasOpenNormalBasisInClass.of_isClosed_subgroup
            (C := C) (G := PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F)
            hIso hSub hWreath W (Subgroup.isClosed_topologicalClosure _)
      let hWclosed : IsClosed (W : Set (PermutationalWreathProduct B (OpenSubgroupRightQuotient
          Hc) F)) := by
        simp [W]
      let : CompactSpace W := hWclosed.isClosedEmbedding_subtypeVal.compactSpace
      let ξW : X → W := fun x =>
        ⟨ξ x, Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨x, rfl⟩)⟩
      have hξWcont : Continuous ξW :=
        Continuous.subtype_mk hξcont (by
          intro x
          exact Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨x, rfl⟩))
      have hξW0 : ξW x0 = 1 := by
        apply Subtype.ext
        exact hξ0
      have hξWgen :
          ProCGroups.Generation.TopologicallyGenerates (G := W) (Set.range ξW) := by
        simpa [W, ξW] using
          topologicallyGenerates_topologicalClosure_of_range (ξ := ξ)
      rcases hF.existsUnique_lift hWproC ξW hξWcont hξW0 hξWgen with
        ⟨ηW, hηW, _⟩
      let η : F →* PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F :=
        W.subtype.comp ηW
      have hηcont : Continuous η := by
        simpa [η] using (continuous_subtype_val.comp hηW.1)
      have hηgen : ∀ x : X, η (ι x) = ξ x := by
        intro x
        simpa [η, ξW] using congrArg Subtype.val (hηW.2 x)
      have hηright :
          (SemidirectProduct.rightHom :
              PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F →* F).comp η =
            MonoidHom.id F := by
        rcases
            hF.existsUnique_lift hF.hasOpenNormalBasisInClass ι hF.continuous_ι hF.map_base
                hF.generates_range with
          ⟨u, hu, huuniq⟩
        have hu_id : MonoidHom.id F = u := by
          exact
            huuniq (MonoidHom.id F)
              ⟨by simpa using (continuous_id : Continuous fun x : F => x), by intro x; rfl⟩
        have hu_η :
            (SemidirectProduct.rightHom :
                PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F →* F).comp η =
              u := by
          let v : F →* F :=
            (SemidirectProduct.rightHom :
                PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F →* F).comp η
          have hη_on_gen :
              ∀ x : X, v (ι x) = ι x := by
            intro x
            have hx := congrArg
              (fun z : PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F => z.right)
              (hηgen x)
            simpa [v, MonoidHom.comp_apply, ξ] using hx
          have hvu : v = u := by
            exact huuniq v ⟨continuous_permutationalWreathProduct_right.comp hηcont, hη_on_gen⟩
          simpa [v] using hvu
        calc
          (SemidirectProduct.rightHom :
              PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F →* F).comp η = u :=
            hu_η
          _ = MonoidHom.id F := hu_id.symm
      have hηcoord :
          ∀ q : OpenSubgroupRightQuotient Hc, ∀ x : X,
            wreathLeftCoordinate η q (ι x) =
              φB ⟨κ (q, x), ⟨(q, x), rfl⟩⟩ := by
        intro q x
        change (η (ι x)).left q = _
        rw [hηgen]
      have hηone :
          ∀ {t : FreeGroup X}, t ∈ T → ∀ x : X,
            schreierGenerator (X := X) hT t x = 1 →
              wreathLeftCoordinate η
                (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc)
                (βF (FreeGroup.of x)) = 1 := by
        intro t ht x' hsg'
        have hmap :
            κ (Quotient.mk'' (βF t), x') = 1 := by
          apply Subtype.ext
          have hcocycle :=
            congrArg Subtype.val
              (map_schreierGenerator_eq_cocycle
                (X := X) (φ := βF) (π := ρ.toMonoidHom) (K := K) hT hβsurj ht x')
          change (↑(κ (Quotient.mk'' (βF t), x')) : F) = 1
          calc
            (↑(κ (Quotient.mk'' (βF t), x')) : F) =
                βF ↑(schreierGenerator (X := X) hT t x') := by
              simpa [κ, rightSchreierGenerator, τ, Hc,
                OpenSubgroupRightQuotient, β, βF] using hcocycle
            _ = 1 := by rw [hsg']; exact βF.map_one
        have hsrc :
            (⟨κ (Quotient.mk'' (βF t), x'), ⟨(Quotient.mk'' (βF t), x'), rfl⟩⟩ : Set.range κ) =
              ⟨κ (q1, x0), ⟨(q1, x0), rfl⟩⟩ := by
          apply Subtype.ext
          exact hmap.trans hκ1.symm
        calc
          wreathLeftCoordinate η
              (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc)
              (βF (FreeGroup.of x'))
              =
            wreathLeftCoordinate η
              (Quotient.mk'' (βF t) : OpenSubgroupRightQuotient Hc) (ι x') := by
                simp only [FreeGroup.lift_apply_of, βF]
          _ = φB ⟨κ (Quotient.mk'' (βF t), x'), ⟨(Quotient.mk'' (βF t), x'), rfl⟩⟩ :=
                hηcoord _ _
          _ = φB ⟨κ (q1, x0), ⟨(q1, x0), rfl⟩⟩ := by rw [hsrc]
          _ = 1 := hφB0
      have hτpure :
          ∀ q : OpenSubgroupRightQuotient Hc,
            wreathLeftCoordinate η q1 (τ q) = 1 := by
        intro q
        simpa [q1, τ, Hc, OpenSubgroupRightQuotient, openSubgroupRightCoset,
          rightCoset, β, βF] using
          (wreathLeftCoordinate_basepoint_of_rightSchreierSectionOfComap
            (X := X) (φ := βF) (π := ρ.toMonoidHom) (K := K) hT hβsurj η hηright
            (hone := hηone) q)
      let g : ↥(Hc : Subgroup F) →* B :=
        rightQuotientBasepointProjectionHom (H := (Hc : Subgroup F)) η hηright
      have hgcont : Continuous g := by
        change Continuous
          ((fun z : PermutationalWreathProduct B (OpenSubgroupRightQuotient Hc) F =>
              z.left q1) ∘ η ∘ Subtype.val)
        exact
          (continuous_permutationalWreathProduct_left_apply (A := B)
            (S := OpenSubgroupRightQuotient Hc) (G := F) q1).comp
            (hηcont.comp continuous_subtype_val)
      have hgfac : ∀ y : Set.range κ, g y.1 = φB y := by
        rintro ⟨y, ⟨⟨q, x'⟩, hy⟩⟩
        subst y
        change g (κ (q, x')) = φB ⟨κ (q, x'), ⟨(q, x'), rfl⟩⟩
        calc
          g (κ (q, x')) = wreathLeftCoordinate η q (βF (FreeGroup.of x')) := by
            simpa [g, κ, τ, βF] using
              (rightQuotientBasepointProjectionHom_rightSchreierGenerator
                (F := F) (H := Hc) (τ := τ) (hτ := hτ) (ι := ι) η hηright hτpure q x')
          _ = wreathLeftCoordinate η q (ι x') := by simp only [FreeGroup.lift_apply_of, βF]
          _ = φB ⟨κ (q, x'), ⟨(q, x'), rfl⟩⟩ := hηcoord q x'
      refine ⟨g, ⟨hgcont, hgfac⟩, ?_⟩
      intro g' hg'
      symm
      apply continuousMonoidHom_eq_of_agrees_on_topologicallyGeneratingSet
        (G := ↥(Hc : Subgroup F)) (A := B) hκgen hgcont hg'.1
      intro h hh
      exact (hgfac ⟨h, hh⟩).trans (hg'.2 ⟨h, hh⟩).symm
  rcases cast (congrArg GoalProp hHc) hMain with
    ⟨κ, hκcont, hκbase, hκ1, hpowRange, hκcompact, hκclosed, hκfree⟩
  rcases hpowRange with ⟨hpowH, hxNrange⟩
  refine ⟨κ, hκcont, hκbase, hκ1, ?_, hκcompact, hκclosed, hκfree⟩
  simpa using hxNrange



end Profinite
end ReidemeisterSchreier
