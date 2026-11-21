/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
public import Nyll.GaloisCohomology.Cyclic.TateFixedCycles

/-!
# Fixed representatives in degree-zero Tate cohomology

The representative, its equivariant naturality, and its Herbrand class are defined
once for any multiplicative finite-group module, independently of class field theory.
-/

@[expose] public section

open CategoryTheory

namespace CyclicCohomology.ProfiniteCohomology.Herbrand

noncomputable section

/-- The degree-zero Tate cycle represented by an actual fixed element. -/
noncomputable def tateH0FixedCycle
    {G A : Type}
    [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (a : fixedSubgroup G A) :
    (tateComplex (Rep.ofMulDistribMulAction G A)).cycles 0 :=
  TateCohomology.fixedCycle (Rep.ofMulDistribMulAction G A)
    ⟨Additive.ofMul a.1, fun g => by
      apply Additive.ofMul.injective
      exact a.2 g⟩

/-- The fixed cycle has the original fixed element as its degree-zero cochain. -/
theorem tateH0FixedCycle_iCycles
    {G A : Type}
    [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (a : fixedSubgroup G A) :
    let M := Rep.ofMulDistribMulAction G A
    (tateComplex M).iCycles 0 (tateH0FixedCycle a) =
      (groupCohomology.cochainsIso₀ M).inv
        (by
          change Additive A
          exact Additive.ofMul a.1) := by
  exact TateCohomology.fixedCycle_iCycles (Rep.ofMulDistribMulAction G A) _

/-- Equivariant homomorphisms carry fixed Tate cycles to the cycles of their images. -/
theorem tateH0FixedCycle_map
    {G A B : Type}
    [Group G] [Fintype G] [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    (f : A →* B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a)
    (a : fixedSubgroup G A) :
    let φ := equivariantRepHom f hf
    let b : fixedSubgroup G B :=
      ⟨f a, fun g ↦ by rw [← hf g a, a.2 g]⟩
    HomologicalComplex.cyclesMap (tateComplex.map φ) 0
        (tateH0FixedCycle a) =
      tateH0FixedCycle b := by
  exact TateCohomology.fixedCycle_map (equivariantRepHom f hf) _

/-- The standard degree-zero boundary comparison preserves the fixed representative. -/
theorem isoZeroBoundary_fixedCycle
    {G A : Type}
    [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (a : fixedSubgroup G A) :
    let M := Rep.ofMulDistribMulAction G A
    let S : ShortComplex (ModuleCat ℤ) :=
      ShortComplex.mk M.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ M)
        (Rep.norm_comp_d_eq_zero M)
    (TateCohomology.isoZeroBoundary M).hom
        ((tateComplex M).homologyπ 0 (tateH0FixedCycle a)) =
      S.homologyπ
        (S.moduleCatCyclesIso.inv
          (by
            change LinearMap.ker
              (groupCohomology.d₀₁
                (Rep.ofMulDistribMulAction G A)).hom
            exact ⟨Additive.ofMul a.1, by
              rw [groupCohomology.d₀₁_ker_eq_invariants]
              intro g
              apply Additive.ofMul.injective
              exact a.2 g⟩)) := by
  exact TateCohomology.isoZeroBoundary_fixedCycle (Rep.ofMulDistribMulAction G A) _

/-- The Tate-to-Herbrand comparison sends a fixed cycle to its original quotient class. -/
theorem tateH0IsoHerbrandH0_fixedCycle
    {G A : Type}
    [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (a : fixedSubgroup G A) :
    (tateH0IsoHerbrandH0 (G := G) (A := A)).hom
        ((tateComplex (Rep.ofMulDistribMulAction G A)).homologyπ 0
          (tateH0FixedCycle a)) =
      Additive.ofMul (HerbrandH0.mk a) := by
  let M := Rep.ofMulDistribMulAction G A
  let S : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk M.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ M)
      (Rep.norm_comp_d_eq_zero M)
  let x : S.moduleCatLeftHomologyData.K := by
    change LinearMap.ker
      (groupCohomology.d₀₁ (Rep.ofMulDistribMulAction G A)).hom
    exact ⟨Additive.ofMul a.1, by
      rw [groupCohomology.d₀₁_ker_eq_invariants]
      intro g
      apply Additive.ofMul.injective
      exact a.2 g⟩
  let y : S.cycles := S.moduleCatCyclesIso.inv x
  have hz :
      (TateCohomology.isoZeroBoundary M).hom
          ((tateComplex M).homologyπ 0 (tateH0FixedCycle a)) =
        S.homologyπ y := by
    exact isoZeroBoundary_fixedCycle a
  change
    (tateH0IsoHerbrandH0 (G := G) (A := A)).hom
        (show tateCohomology M 0 from
          (tateComplex M).homologyπ 0 (tateH0FixedCycle a)) =
      Additive.ofMul (HerbrandH0.mk a)
  have hy :
      S.moduleCatHomologyIso.hom (S.homologyπ y) =
        S.moduleCatLeftHomologyData.π x := by
    exact (S.π_moduleCatCyclesIso_hom_apply y).trans
      (congrArg S.moduleCatLeftHomologyData.π (Iso.inv_hom_id_apply S.moduleCatCyclesIso x))
  have hPresentation :
      ∃ eQ : S.moduleCatLeftHomologyData.H ≅
          ModuleCat.of ℤ (Additive (HerbrandH0 G A)),
        tateH0IsoHerbrandH0 (G := G) (A := A) =
            TateCohomology.isoZeroBoundary M ≪≫
              S.moduleCatHomologyIso ≪≫ eQ ∧
          eQ.hom (S.moduleCatLeftHomologyData.π x) =
            Additive.ofMul (HerbrandH0.mk a) := by
    exact ⟨_, rfl, rfl⟩
  obtain ⟨eQ, hIso, hQ⟩ := hPresentation
  calc
    (tateH0IsoHerbrandH0 (G := G) (A := A)).hom
        ((tateComplex M).homologyπ 0 (tateH0FixedCycle a)) =
      (TateCohomology.isoZeroBoundary M ≪≫
        S.moduleCatHomologyIso ≪≫ eQ).hom
          ((tateComplex M).homologyπ 0 (tateH0FixedCycle a)) :=
      congrArg
        (fun e ↦ e.hom
          ((tateComplex M).homologyπ 0 (tateH0FixedCycle a))) hIso
    _ = eQ.hom
        (S.moduleCatHomologyIso.hom
          ((TateCohomology.isoZeroBoundary M).hom
            ((tateComplex M).homologyπ 0 (tateH0FixedCycle a)))) := rfl
    _ = eQ.hom (S.moduleCatHomologyIso.hom (S.homologyπ y)) :=
      congrArg (fun z ↦ eQ.hom (S.moduleCatHomologyIso.hom z)) hz
    _ = eQ.hom (S.moduleCatLeftHomologyData.π x) :=
      congrArg (fun z ↦ eQ.hom z) hy
    _ = Additive.ofMul (HerbrandH0.mk a) := hQ

/-- The degree-zero comparison intertwines an equivariant map on each fixed class. -/
theorem tateH0IsoHerbrandH0_map_mk
    {G A B : Type} [Group G] [Fintype G] [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    (f : A →* B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a)
    (a : fixedSubgroup G A) :
    (tateH0IsoHerbrandH0 (G := G) (A := B)).hom
        (((tateCohomologyFunctor 0).map (equivariantRepHom f hf)).hom
          ((tateH0IsoHerbrandH0 (G := G) (A := A)).inv
            (Additive.ofMul (HerbrandH0.mk a)))) =
      Additive.ofMul (HerbrandH0.mk
        (⟨f a, fun g ↦ by rw [← hf g a, a.2 g]⟩ : fixedSubgroup G B)) := by
  let MA := Rep.ofMulDistribMulAction G A
  let MB := Rep.ofMulDistribMulAction G B
  let φ := equivariantRepHom f hf
  let b : fixedSubgroup G B := ⟨f a, fun g ↦ by rw [← hf g a, a.2 g]⟩
  have hpre :
      (tateH0IsoHerbrandH0 (G := G) (A := A)).inv
          (Additive.ofMul (HerbrandH0.mk a)) =
        (tateComplex MA).homologyπ 0 (tateH0FixedCycle a) := by
    let e := tateH0IsoHerbrandH0 (G := G) (A := A)
    let z : tateCohomology MA 0 := (tateComplex MA).homologyπ 0 (tateH0FixedCycle a)
    have hz : e.hom z = Additive.ofMul (HerbrandH0.mk a) := tateH0IsoHerbrandH0_fixedCycle a
    exact (congrArg e.inv hz.symm).trans (Iso.hom_inv_id_apply e z)
  have hmap :
      ((tateCohomologyFunctor 0).map φ).hom
          ((tateComplex MA).homologyπ 0 (tateH0FixedCycle a)) =
        (tateComplex MB).homologyπ 0 (tateH0FixedCycle b) := by
    change (((tateComplex MA).homologyπ 0 ≫
      HomologicalComplex.homologyMap (tateComplex.map φ) 0).hom
        (tateH0FixedCycle a)) = _
    rw [HomologicalComplex.homologyπ_naturality]
    simp only [ModuleCat.comp_apply]
    exact congrArg ((tateComplex MB).homologyπ 0) (tateH0FixedCycle_map f hf a)
  rw [hpre, hmap]
  exact tateH0IsoHerbrandH0_fixedCycle b

/-- The native degree-minus-one comparison retains the actual norm-kernel
representative and the original generator defining the augmentation boundary. -/
theorem tateHMinusOneIsoHerbrandHMinusOne_normKernelClass
    {G A : Type} [Group G] [Fintype G] [CommGroup A] [MulDistribMulAction G A]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (a : normKernelSubgroup G A) :
    let M := Rep.ofMulDistribMulAction G A
    let z : LinearMap.ker M.ρ.norm :=
      (normKernelCyclesAddEquiv (G := G) (A := A)).symm (Additive.ofMul a)
    (tateHMinusOneIsoHerbrandHMinusOne σ hgen).hom (TateCohomology.normKernelClass M z) =
      Additive.ofMul (HerbrandHMinusOne.mk σ a) := by
  intro M z
  let : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  let : CommGroup G := IsCyclic.commGroup
  let S := Rep.FiniteCyclicGroup.subCompNormHom M σ
  let w : S.moduleCatLeftHomologyData.K := z
  have hz : (TateCohomology.isoFiniteCyclicNegOne M σ hgen).hom
      (TateCohomology.normKernelClass M z) = S.homologyπ (S.moduleCatCyclesIso.inv w) :=
    TateCohomology.isoFiniteCyclicNegOne_normKernelClass M σ hgen z
  obtain ⟨eQ, he, hmk⟩ :
      ∃ eQ : S.moduleCatLeftHomologyData.H ≅ ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)),
        tateHMinusOneIsoHerbrandHMinusOne σ hgen =
          TateCohomology.isoFiniteCyclicNegOne M σ hgen ≪≫ S.moduleCatHomologyIso ≪≫ eQ ∧
        eQ.hom (S.moduleCatLeftHomologyData.π w) = Additive.ofMul (HerbrandHMinusOne.mk σ a) :=
    ⟨_, rfl, rfl⟩
  have hc : S.moduleCatHomologyIso.hom (S.homologyπ (S.moduleCatCyclesIso.inv w)) =
      S.moduleCatLeftHomologyData.π w :=
    (S.π_moduleCatCyclesIso_hom_apply (S.moduleCatCyclesIso.inv w)).trans
      (congrArg S.moduleCatLeftHomologyData.π (Iso.inv_hom_id_apply S.moduleCatCyclesIso w))
  have he' := congrArg (fun e => e.hom (TateCohomology.normKernelClass M z)) he
  exact he'.trans ((congrArg eQ.hom ((congrArg S.moduleCatHomologyIso.hom hz).trans hc)).trans hmk)

end

end CyclicCohomology.ProfiniteCohomology.Herbrand
