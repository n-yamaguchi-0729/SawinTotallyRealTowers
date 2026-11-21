/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.TateComparison
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Fixed representatives in native Tate cohomology

A fixed vector in any native representation defines its degree-zero Tate cycle.
The cycle, boundary comparison and induced class retain that actual vector.
In degree minus one the native norm-kernel representative uses the same
degree-minus-one boundary comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace TateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The degree-zero Tate cycle represented by an actual fixed element. -/
def fixedCycle (M : Rep R G) (a : M.ρ.invariants) :
    (tateComplex M).cycles 0 := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk M.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ M)
      (Rep.norm_comp_d_eq_zero M)
  let eS : (tateComplex M).sc' (-1) 0 1 ≅ S :=
    ShortComplex.isoMk
      (by exact groupHomology.chainsIso₀ M)
      (groupCohomology.cochainsIso₀ M)
      (groupCohomology.cochainsIso₁ M)
      (by
        change
          (groupHomology.chainsIso₀ M).hom ≫ M.norm.asHom.toModuleCatHom =
            M.tateNorm ≫ (groupCohomology.cochainsIso₀ M).hom
        simp only [Rep.tateNorm, Category.assoc, Iso.inv_hom_id,
          Category.comp_id])
      (groupCohomology.comp_d₀₁_eq M)
  let x : S.moduleCatLeftHomologyData.K := by
    change LinearMap.ker
      (groupCohomology.d₀₁ M).hom
    exact ⟨(a : M), by
      rw [groupCohomology.d₀₁_ker_eq_invariants]
      exact a.property⟩
  exact
    ((tateComplex M).cyclesIsoSc' (-1) 0 1
              ((ComplexShape.up ℤ).prev_eq' (by decide))
              ((ComplexShape.up ℤ).next_eq' (by decide))).inv
      ((ShortComplex.cyclesMapIso eS).inv
        (S.moduleCatCyclesIso.inv x))

/-- The fixed cycle has the original fixed element as its degree-zero cochain. -/
theorem fixedCycle_iCycles (M : Rep R G) (a : M.ρ.invariants) :
    (tateComplex M).iCycles 0 (fixedCycle M a) =
      (groupCohomology.cochainsIso₀ M).inv
        (a : M) := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk M.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ M)
      (Rep.norm_comp_d_eq_zero M)
  let eS : (tateComplex M).sc' (-1) 0 1 ≅ S :=
    ShortComplex.isoMk
      (by exact groupHomology.chainsIso₀ M)
      (groupCohomology.cochainsIso₀ M)
      (groupCohomology.cochainsIso₁ M)
      (by
        change
          (groupHomology.chainsIso₀ M).hom ≫ M.norm.asHom.toModuleCatHom =
            M.tateNorm ≫ (groupCohomology.cochainsIso₀ M).hom
        simp only [Rep.tateNorm, Category.assoc, Iso.inv_hom_id,
          Category.comp_id])
      (groupCohomology.comp_d₀₁_eq M)
  let x : S.moduleCatLeftHomologyData.K := by
    change LinearMap.ker
      (groupCohomology.d₀₁ M).hom
    exact ⟨(a : M), by
      rw [groupCohomology.d₀₁_ker_eq_invariants]
      exact a.property⟩
  change
    (((((tateComplex M).cyclesIsoSc'
            (-1) 0 1
              ((ComplexShape.up ℤ).prev_eq' (by decide))
              ((ComplexShape.up ℤ).next_eq' (by decide))).inv ≫
          (tateComplex M).iCycles 0).hom
      ((ShortComplex.cyclesMapIso eS).inv
        (S.moduleCatCyclesIso.inv x)))) =
      (groupCohomology.cochainsIso₀ M).inv
        (a : M)
  rw [HomologicalComplex.cyclesIsoSc'_inv_iCycles]
  change
    (((ShortComplex.cyclesMap eS.inv ≫
          ((tateComplex M).sc' (-1) 0 1).iCycles).hom
      (S.moduleCatCyclesIso.inv x))) =
      (groupCohomology.cochainsIso₀ M).inv
        (a : M)
  rw [ShortComplex.cyclesMap_i]
  change
    (((S.moduleCatCyclesIso.inv ≫ S.iCycles ≫ eS.inv.τ₂).hom x)) =
      (groupCohomology.cochainsIso₀ M).inv
        (a : M)
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles_assoc]
  change
    (groupCohomology.cochainsIso₀
        M).inv ((a : M)) =
      (groupCohomology.cochainsIso₀
        M).inv ((a : M))
  rfl

/-- The standard degree-zero boundary comparison preserves the fixed representative. -/
theorem isoZeroBoundary_fixedCycle (M : Rep R G) (a : M.ρ.invariants) :
    let S : ShortComplex (ModuleCat R) :=
      ShortComplex.mk M.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ M)
        (Rep.norm_comp_d_eq_zero M)
    (TateCohomology.isoZeroBoundary M).hom
        ((tateComplex M).homologyπ 0 (fixedCycle M a)) =
      S.homologyπ
        (S.moduleCatCyclesIso.inv
          (by
            change LinearMap.ker
              (groupCohomology.d₀₁
                M).hom
            exact ⟨(a : M), by
              rw [groupCohomology.d₀₁_ker_eq_invariants]
              exact a.property⟩)) := by
  intro S
  let eSc :
      (tateComplex M).sc 0 ≅ (tateComplex M).sc' (-1) 0 1 :=
    (tateComplex M).isoSc' (-1) 0 1
              ((ComplexShape.up ℤ).prev_eq' (by decide))
              ((ComplexShape.up ℤ).next_eq' (by decide))
  let eS : (tateComplex M).sc' (-1) 0 1 ≅ S :=
    ShortComplex.isoMk
      (by exact groupHomology.chainsIso₀ M)
      (groupCohomology.cochainsIso₀ M)
      (groupCohomology.cochainsIso₁ M)
      (by
        change
          (groupHomology.chainsIso₀ M).hom ≫ M.norm.asHom.toModuleCatHom =
            M.tateNorm ≫ (groupCohomology.cochainsIso₀ M).hom
        simp only [Rep.tateNorm, Category.assoc, Iso.inv_hom_id,
          Category.comp_id])
      (groupCohomology.comp_d₀₁_eq M)
  let x : S.moduleCatLeftHomologyData.K := by
    change LinearMap.ker
      (groupCohomology.d₀₁ M).hom
    exact ⟨(a : M), by
      rw [groupCohomology.d₀₁_ker_eq_invariants]
      exact a.property⟩
  let y : S.cycles := S.moduleCatCyclesIso.inv x
  have hcycle :
      ShortComplex.cyclesMap eS.hom
          (((tateComplex M).cyclesIsoSc'
            (-1) 0 1
              ((ComplexShape.up ℤ).prev_eq' (by decide))
              ((ComplexShape.up ℤ).next_eq' (by decide))).hom
            (fixedCycle M a)) =
        y := by
    rw [show
      fixedCycle M a =
        ((tateComplex M).cyclesIsoSc'
          (-1) 0 1
              ((ComplexShape.up ℤ).prev_eq' (by decide))
              ((ComplexShape.up ℤ).next_eq' (by decide))).inv
          ((ShortComplex.cyclesMapIso eS).inv y) by
      rfl]
    change
      (ShortComplex.cyclesMapIso eS).hom
          (((tateComplex M).cyclesIsoSc'
              (-1) 0 1
              ((ComplexShape.up ℤ).prev_eq' (by decide))
              ((ComplexShape.up ℤ).next_eq' (by decide))).hom
            (((tateComplex M).cyclesIsoSc'
                (-1) 0 1
              ((ComplexShape.up ℤ).prev_eq' (by decide))
              ((ComplexShape.up ℤ).next_eq' (by decide))).inv
              ((ShortComplex.cyclesMapIso eS).inv y))) =
        y
    rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  have hIso :
      (TateCohomology.isoZeroBoundary M).hom =
        ((tateComplex M).homologyIsoSc'
            (-1) 0 1
              ((ComplexShape.up ℤ).prev_eq' (by decide))
              ((ComplexShape.up ℤ).next_eq' (by decide))).hom ≫
          ShortComplex.homologyMap eS.hom := by
    change
      ShortComplex.homologyMap ((eSc ≪≫ eS).hom) =
        ShortComplex.homologyMap eSc.hom ≫
          ShortComplex.homologyMap eS.hom
    rw [Iso.trans_hom, ShortComplex.homologyMap_comp]
  rw [hIso]
  change
    ((((tateComplex M).homologyπ 0 ≫
        ((tateComplex M).homologyIsoSc'
          (-1) 0 1
              ((ComplexShape.up ℤ).prev_eq' (by decide))
              ((ComplexShape.up ℤ).next_eq' (by decide))).hom) ≫
      ShortComplex.homologyMap eS.hom).hom
        (fixedCycle M a)) =
    S.homologyπ y
  rw [HomologicalComplex.π_homologyIsoSc'_hom]
  rw [Category.assoc, ShortComplex.homologyπ_naturality]
  simp only [ModuleCat.comp_apply]
  exact congrArg (fun z : S.cycles ↦ S.homologyπ z) hcycle


/-- Equivariant maps carry fixed Tate cycles to the cycles of their actual images. -/
theorem fixedCycle_map {M N : Rep R G} (f : M ⟶ N) (a : M.ρ.invariants) :
    HomologicalComplex.cyclesMap (tateComplex.map f) 0 (fixedCycle M a) =
      fixedCycle N ⟨f a, fun g => by rw [← Rep.hom_comm_apply, a.2 g]⟩ := by
  let b : N.ρ.invariants := ⟨f a, fun g => by rw [← Rep.hom_comm_apply, a.2 g]⟩
  apply (ModuleCat.mono_iff_injective ((tateComplex N).iCycles 0)).1 inferInstance
  change (((HomologicalComplex.cyclesMap (tateComplex.map f) 0 ≫
    (tateComplex N).iCycles 0).hom (fixedCycle M a))) =
      (tateComplex N).iCycles 0 (fixedCycle N b)
  rw [HomologicalComplex.cyclesMap_i]
  simp only [ModuleCat.comp_apply]
  rw [fixedCycle_iCycles M a, fixedCycle_iCycles N b]
  apply (ModuleCat.mono_iff_injective (groupCohomology.cochainsIso₀ N).hom).1 inferInstance
  change (((groupCohomology.cochainsMap (.id G) f).f 0 ≫
    (groupCohomology.cochainsIso₀ N).hom).hom
      ((groupCohomology.cochainsIso₀ M).inv (a : M))) =
    (groupCohomology.cochainsIso₀ N).hom
      ((groupCohomology.cochainsIso₀ N).inv (b : N))
  rw [groupCohomology.cochainsMap_f_0_comp_cochainsIso₀]
  rfl

/-- The actual Tate class of a fixed vector. -/
def fixedClass (M : Rep R G) (a : M.ρ.invariants) : tateCohomology M 0 :=
  (tateComplex M).homologyπ 0 (fixedCycle M a)

/-- Naturality of the actual degree-zero Tate class on fixed representatives. -/
theorem fixedClass_map {M N : Rep R G} (f : M ⟶ N) (a : M.ρ.invariants) :
    (tateCohomologyFunctor 0).map f (fixedClass M a) =
      fixedClass N ⟨f a, fun g => by rw [← Rep.hom_comm_apply, a.2 g]⟩ := by
  change (((tateComplex M).homologyπ 0 ≫
    HomologicalComplex.homologyMap (tateComplex.map f) 0).hom (fixedCycle M a)) = _
  rw [HomologicalComplex.homologyπ_naturality]
  simp only [ModuleCat.comp_apply]
  exact congrArg ((tateComplex N).homologyπ 0) (fixedCycle_map f a)

/-- The cyclic comparison takes the original fixed vector to the same cycle
for the specified generator minus the identity. -/
theorem isoFiniteCyclicZero_fixedClass {H : Type u} [CommGroup H] [Fintype H]
    (M : Rep R H) (g : H) (hg : ∀ h, h ∈ Subgroup.zpowers g) (a : M.ρ.invariants) :
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    (isoFiniteCyclicZero M g hg).hom (fixedClass M a) =
      T.homologyπ (T.moduleCatCyclesIso.inv
        ⟨(a : M), sub_eq_zero.mpr (a.property g)⟩) := by
  intro T
  let S : ShortComplex (ModuleCat R) :=
    .mk M.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ M) (Rep.norm_comp_d_eq_zero M)
  let x : LinearMap.ker S.g.hom := ⟨(a : M), by
    change (a : M) ∈ LinearMap.ker (groupCohomology.d₀₁ M).hom
    rw [groupCohomology.d₀₁_ker_eq_invariants]
    exact a.property⟩
  let y : LinearMap.ker T.g.hom := ⟨(a : M), sub_eq_zero.mpr (a.property g)⟩
  have hx : (isoZeroBoundary M).hom (fixedClass M a) =
      S.homologyπ (S.moduleCatCyclesIso.inv x) := isoZeroBoundary_fixedCycle M a
  obtain ⟨eQ, heQ, hπ⟩ :
      ∃ eQ : S.moduleCatLeftHomologyData.H ≅ T.moduleCatLeftHomologyData.H,
        isoFiniteCyclicZero M g hg = isoZeroBoundary M ≪≫ S.moduleCatHomologyIso ≪≫
          eQ ≪≫ T.moduleCatHomologyIso.symm ∧
        eQ.hom (S.moduleCatLeftHomologyData.π x) = T.moduleCatLeftHomologyData.π y :=
    ⟨_, rfl, rfl⟩
  rw [heQ]
  change T.moduleCatHomologyIso.inv
    (eQ.hom (S.moduleCatHomologyIso.hom ((isoZeroBoundary M).hom (fixedClass M a)))) = _
  have hcycle : S.moduleCatCyclesIso.hom (S.moduleCatCyclesIso.inv x) = x :=
    Iso.inv_hom_id_apply S.moduleCatCyclesIso x
  have hclass : S.moduleCatHomologyIso.hom (S.homologyπ (S.moduleCatCyclesIso.inv x)) =
      S.moduleCatLeftHomologyData.π x :=
    (ShortComplex.π_moduleCatCyclesIso_hom_apply S (S.moduleCatCyclesIso.inv x)).trans
      (congrArg (fun z : S.moduleCatLeftHomologyData.K => S.moduleCatLeftHomologyData.π z) hcycle)
  calc
    _ = T.moduleCatHomologyIso.inv (eQ.hom (S.moduleCatLeftHomologyData.π x)) :=
      congrArg (fun z : S.moduleCatLeftHomologyData.H => T.moduleCatHomologyIso.inv (eQ.hom z))
        ((congrArg S.moduleCatHomologyIso.hom hx).trans hclass)
    _ = T.moduleCatHomologyIso.inv (T.moduleCatLeftHomologyData.π y) :=
      congrArg T.moduleCatHomologyIso.inv hπ
    _ = _ := (ShortComplex.moduleCatCyclesIso_inv_π_apply T y).symm

/-- The class of a norm-kernel vector in the native Tate group in degree minus one. -/
def normKernelClass (M : Rep R G) (a : LinearMap.ker M.ρ.norm) : tateCohomology M (-1) :=
  let S := ShortComplex.mk (groupHomology.d₁₀ M) M.norm.asHom.toModuleCatHom
    (Rep.comp_eq_zero M)
  (isoNegOneBoundary M).inv (S.homologyπ (S.moduleCatCyclesIso.inv a))

/-- The cyclic comparison sends a norm-kernel class to its original vector in
the reverse norm complex with the specified generator-minus-identity map. -/
theorem isoFiniteCyclicNegOne_normKernelClass {H : Type u} [CommGroup H] [Fintype H]
    (M : Rep R H) (g : H) (hg : ∀ h, h ∈ Subgroup.zpowers g) (a : LinearMap.ker M.ρ.norm) :
    let T := Rep.FiniteCyclicGroup.subCompNormHom M g
    (isoFiniteCyclicNegOne M g hg).hom (normKernelClass M a) =
      T.homologyπ (T.moduleCatCyclesIso.inv a) := by
  intro T
  let S := ShortComplex.mk (groupHomology.d₁₀ M) M.norm.asHom.toModuleCatHom
    (Rep.comp_eq_zero M)
  have hS : (isoNegOneBoundary M).hom (normKernelClass M a) =
      S.homologyπ (S.moduleCatCyclesIso.inv a) := Iso.inv_hom_id_apply _ _
  obtain ⟨eQ, heQ, hπ⟩ :
      ∃ eQ : S.moduleCatLeftHomologyData.H ≅ T.moduleCatLeftHomologyData.H,
        isoFiniteCyclicNegOne M g hg = isoNegOneBoundary M ≪≫ S.moduleCatHomologyIso ≪≫
          eQ ≪≫ T.moduleCatHomologyIso.symm ∧
        eQ.hom (S.moduleCatLeftHomologyData.π a) = T.moduleCatLeftHomologyData.π a :=
    ⟨_, rfl, rfl⟩
  rw [heQ]
  change T.moduleCatHomologyIso.inv
    (eQ.hom (S.moduleCatHomologyIso.hom ((isoNegOneBoundary M).hom (normKernelClass M a)))) = _
  have hcycle : S.moduleCatCyclesIso.hom (S.moduleCatCyclesIso.inv a) = a :=
    Iso.inv_hom_id_apply S.moduleCatCyclesIso a
  have hclass : S.moduleCatHomologyIso.hom (S.homologyπ (S.moduleCatCyclesIso.inv a)) =
      S.moduleCatLeftHomologyData.π a :=
    (ShortComplex.π_moduleCatCyclesIso_hom_apply S (S.moduleCatCyclesIso.inv a)).trans
      (congrArg (fun z : S.moduleCatLeftHomologyData.K => S.moduleCatLeftHomologyData.π z) hcycle)
  calc
    _ = T.moduleCatHomologyIso.inv (eQ.hom (S.moduleCatLeftHomologyData.π a)) :=
      congrArg (fun z : S.moduleCatLeftHomologyData.H => T.moduleCatHomologyIso.inv (eQ.hom z))
        ((congrArg S.moduleCatHomologyIso.hom hS).trans hclass)
    _ = T.moduleCatHomologyIso.inv (T.moduleCatLeftHomologyData.π a) :=
      congrArg T.moduleCatHomologyIso.inv hπ
    _ = _ := (ShortComplex.moduleCatCyclesIso_inv_π_apply T a).symm

end TateCohomology
