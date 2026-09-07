import GaloisCohomology.ProP.FiniteCyclicBarPeriodicChainComparison

set_option autoImplicit false
/-!
# Canonical degree-two bar--periodic comparison for finite cyclic groups

This module identifies the normalized finite-cyclic carry cocycle in bar
cohomology with the canonical even-degree class from the periodic resolution.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace ClassFieldTower.Cohomology

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- The contravariant cochain map induced by a map of projective resolutions. -/
def resolutionLinearYonedaMap
    {X X' : Rep R G} {f : X ⟶ X'}
    (P : ProjectiveResolution X) (P' : ProjectiveResolution X')
    (phi : ProjectiveResolution.Hom P P' f) (A : Rep R G) :
    P'.complex.linearYonedaObj R A ⟶ P.complex.linearYonedaObj R A :=
  (HomologicalComplex.unopFunctor
      (ModuleCat.{u} R) (ComplexShape.down ℕ)).map
    (((((linearYoneda R (Rep R G)).obj A).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map phi.hom).op)

omit [Fintype G] in
@[simp]
theorem resolutionLinearYonedaMap_f
    {X X' : Rep R G} {f : X ⟶ X'}
    (P : ProjectiveResolution X) (P' : ProjectiveResolution X')
    (phi : ProjectiveResolution.Hom P P' f) (A : Rep R G) (n : ℕ) :
    (resolutionLinearYonedaMap P P' phi A).f n =
      ModuleCat.ofHom (Linear.leftComp R A (phi.hom.f n)) := rfl

omit [Fintype G] in
theorem resolution_isoExt_hom_naturality
    {X X' : Rep R G} {f : X ⟶ X'}
    (P : ProjectiveResolution X) (P' : ProjectiveResolution X')
    (phi : ProjectiveResolution.Hom P P' f) (A : Rep R G) (i : ℕ) :
    (((_root_.Ext R (Rep R G) i).map f.op).app A) ≫ (P.isoExt i A).hom =
      (P'.isoExt i A).hom ≫
        HomologicalComplex.homologyMap
          (resolutionLinearYonedaMap P P' phi A) i := by
  dsimp [ProjectiveResolution.isoExt, _root_.Ext]
  have h := ProjectiveResolution.isoLeftDerivedObj_inv_naturality
    f P P' phi.hom phi.hom_f_zero_comp_π_f_zero
      ((linearYoneda R (Rep R G)).obj A).rightOp i
  have hUnop := congr_arg Quiver.Hom.unop h
  have hLeftDerivedRaw :
      ((((linearYoneda R (Rep R G)).obj A).rightOp.leftDerived i).map f).unop ≫
        (P.isoLeftDerivedObj
          ((linearYoneda R (Rep R G)).obj A).rightOp i).inv.unop =
      (P'.isoLeftDerivedObj
          ((linearYoneda R (Rep R G)).obj A).rightOp i).inv.unop ≫
        ((((linearYoneda R (Rep R G)).obj A).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor
            (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) i).map phi.hom).unop := by
    simpa only [unop_comp] using hUnop
  let FP := ((linearYoneda R (Rep R G)).obj A).rightOp.mapHomologicalComplex
    (ComplexShape.down ℕ)
  let KP := FP.obj P.complex
  let KP' := FP.obj P'.complex
  let eP : KP.unop.homology i ≅
      unop ((HomologicalComplex.homologyFunctor
        (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) i).obj KP) :=
    by
      simpa only [HomologicalComplex.homologyFunctor_obj] using KP.homologyUnop i
  let eP' : KP'.unop.homology i ≅
      unop ((HomologicalComplex.homologyFunctor
        (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) i).obj KP') :=
    by
      simpa only [HomologicalComplex.homologyFunctor_obj] using KP'.homologyUnop i
  let hMap : KP'.unop.homology i ⟶ KP.unop.homology i := by
    change
      (P'.complex.linearYonedaObj R A).homology i ⟶
        (P.complex.linearYonedaObj R A).homology i
    exact HomologicalComplex.homologyMap
      (resolutionLinearYonedaMap P P' phi A) i
  have hOp := HomologicalComplex.homologyOp_hom_naturality
    (resolutionLinearYonedaMap P P' phi A) i
  have hOp' := congr_arg Quiver.Hom.unop hOp
  have hNaturality :
      eP'.hom ≫
        ((((linearYoneda R (Rep R G)).obj A).rightOp.mapHomologicalComplex
              (ComplexShape.down ℕ) ⋙
            HomologicalComplex.homologyFunctor
              (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) i).map phi.hom).unop =
        hMap ≫ eP.hom := by
    change
      (HomologicalComplex.homologyMap
          ((HomologicalComplex.opFunctor
            (ModuleCat.{u} R) (ComplexShape.up ℕ)).map
              (resolutionLinearYonedaMap P P' phi A).op) i ≫
        (HomologicalComplex.homologyOp
          (P'.complex.linearYonedaObj R A) i).hom).unop =
      ((HomologicalComplex.homologyOp
          (P.complex.linearYonedaObj R A) i).hom ≫
        (HomologicalComplex.homologyMap
          (resolutionLinearYonedaMap P P' phi A) i).op).unop
    exact hOp'
  change
    ((((linearYoneda R (Rep R G)).obj A).rightOp.leftDerived i).map f).unop ≫
        (P.isoLeftDerivedObj
          ((linearYoneda R (Rep R G)).obj A).rightOp i).inv.unop ≫
        eP.inv =
      (P'.isoLeftDerivedObj
          ((linearYoneda R (Rep R G)).obj A).rightOp i).inv.unop ≫
        eP'.inv ≫
        hMap
  rw [← Category.assoc, hLeftDerivedRaw]
  simp only [Category.assoc]
  apply (cancel_epi
    (P'.isoLeftDerivedObj
      ((linearYoneda R (Rep R G)).obj A).rightOp i).inv.unop).mpr
  apply (cancel_epi eP'.hom).mp
  rw [
    ← Category.assoc, hNaturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.hom_inv_id_assoc]

omit [Fintype G] in
theorem groupCohomologyIso_hom_naturality
    (P P' : ProjectiveResolution (Rep.trivial R G R))
    (phi : ProjectiveResolution.Hom P P' (𝟙 _))
    (A : Rep R G) (i : ℕ) :
    (groupCohomologyIso A i P).hom =
      (groupCohomologyIso A i P').hom ≫
        HomologicalComplex.homologyMap
          (resolutionLinearYonedaMap P P' phi A) i := by
  have hIsoExt :
      (P.isoExt i A).hom =
        (P'.isoExt i A).hom ≫
          HomologicalComplex.homologyMap
            (resolutionLinearYonedaMap P P' phi A) i := by
    simpa using resolution_isoExt_hom_naturality P P' phi A i
  change
    (groupCohomologyIsoExt A i).hom ≫ (P.isoExt i A).hom =
      ((groupCohomologyIsoExt A i).hom ≫ (P'.isoExt i A).hom) ≫
        HomologicalComplex.homologyMap
          (resolutionLinearYonedaMap P P' phi A) i
  rw [hIsoExt, Category.assoc]

/-- The identity bridge between the homological-complex and short-complex owners of homology. -/
private noncomputable def cyclicPeriodicH2HomologyOwnerIso
    (A : Rep R G) (g : G) :
    (Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).homology 2 ≅
      ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2).homology :=
  eqToIso (by rfl)

private theorem cyclicPeriodicH2HomologyOwnerIso_hom
    (A : Rep R G) (g : G) :
    (cyclicPeriodicH2HomologyOwnerIso A g).hom =
      𝟙 ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).homology 2) := by
  rfl

private theorem cyclicPeriodicH2HomologyOwnerIso_eq_refl
    (A : Rep R G) (g : G) :
    cyclicPeriodicH2HomologyOwnerIso A g =
      Iso.refl
        ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).homology 2) := by
  apply Iso.ext
  exact cyclicPeriodicH2HomologyOwnerIso_hom A g

/-- The short-complex isomorphism underlying `cyclicPeriodicH2Iso`. -/
noncomputable def cyclicPeriodicH2ScIso (A : Rep R G) (g : G) :
    (Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2 ≅
      Rep.FiniteCyclicGroup.normHomCompSub A g :=
  HomologicalComplex.alternatingConstScIsoEven
    (ModuleCat.of R A.V)
    (by ext; simp [Rep.sub_hom])
    (by ext; simp [Rep.sub_hom])
    (by simp) (by simp) (by simp) (by simp)

/-- The periodic degree-two homology model occurring in `groupCohomologyIsoEven`. -/
noncomputable def cyclicPeriodicH2Iso
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj R A).homology 2 ≅
      (Rep.FiniteCyclicGroup.normHomCompSub A g).homology :=
  HomologicalComplex.homologyMapIso
      (Rep.FiniteCyclicGroup.homResolutionIso A g hg) 2 ≪≫
    cyclicPeriodicH2HomologyOwnerIso A g ≪≫
    ShortComplex.homologyMapIso (cyclicPeriodicH2ScIso A g)

@[simp]
theorem cyclicPeriodicH2ScIso_inv_τ₂ (A : Rep R G) (g : G) :
    (cyclicPeriodicH2ScIso A g).inv.τ₂ = 𝟙 _ := rfl

theorem cyclicPeriodicH2Iso_eq
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    cyclicPeriodicH2Iso A g hg =
      HomologicalComplex.homologyMapIso
          (Rep.FiniteCyclicGroup.homResolutionIso A g hg) 2 ≪≫
        ShortComplex.homologyMapIso (cyclicPeriodicH2ScIso A g) := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private noncomputable def cyclicPeriodicH2KernelIso
    (A : Rep R G) (g : G) :
    ModuleCat.of R
        (LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) ≅
      (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatLeftHomologyData.K :=
  eqToIso (by rfl)

private theorem cyclicPeriodicH2KernelIso_hom
    (A : Rep R G) (g : G) :
    (cyclicPeriodicH2KernelIso A g).hom =
      𝟙 (ModuleCat.of R
        (LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)) := by
  rfl

/-- The identity bridge between the short-complex and homological-complex owners of cycles. -/
private noncomputable def cyclicPeriodicH2CyclesOwnerIso
    (A : Rep R G) (g : G) :
    ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2).cycles ≅
      (Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).cycles 2 :=
  eqToIso (by rfl)

private theorem cyclicPeriodicH2CyclesOwnerIso_hom
    (A : Rep R G) (g : G) :
    (cyclicPeriodicH2CyclesOwnerIso A g).hom =
      𝟙 ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).cycles 2) := by
  rfl

/-- The identity bridge from the middle object of the short complex to degree two. -/
private noncomputable def cyclicPeriodicH2DegreeOwnerIso
    (A : Rep R G) (g : G) :
    ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2).X₂ ≅
      (Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).X 2 :=
  eqToIso (by rfl)

private theorem cyclicPeriodicH2DegreeOwnerIso_hom
    (A : Rep R G) (g : G) :
    (cyclicPeriodicH2DegreeOwnerIso A g).hom =
      𝟙 ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).X 2) := by
  rfl

private theorem cyclicPeriodicH2CyclesOwnerIso_hom_iCycles
    (A : Rep R G) (g : G) :
    (cyclicPeriodicH2CyclesOwnerIso A g).hom ≫
        (Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).iCycles 2 =
      ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2).iCycles ≫
        (cyclicPeriodicH2DegreeOwnerIso A g).hom := by
  change
    (𝟙 (((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2).cycles)) ≫
        ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2).iCycles =
      ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2).iCycles ≫
        𝟙 ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2).X₂
  simp only [Category.id_comp, Category.comp_id]

private theorem cyclicPeriodicH2DegreeOwners_comp_homResolutionIso_inv
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (cyclicPeriodicH2ScIso A g).inv.τ₂ ≫
        (cyclicPeriodicH2DegreeOwnerIso A g).hom ≫
        (Rep.FiniteCyclicGroup.homResolutionIso A g hg).inv.f 2 =
      (Rep.FiniteCyclicGroup.homResolutionIso A g hg).inv.f 2 := by
  have hNative :
      𝟙 ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).X 2) ≫
          𝟙 ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).X 2) ≫
          (Rep.FiniteCyclicGroup.homResolutionIso A g hg).inv.f 2 =
        (Rep.FiniteCyclicGroup.homResolutionIso A g hg).inv.f 2 := by
    simp only [Category.id_comp]
  have hOwner :
      (𝟙 ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).X 2) ≫
            𝟙 ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).X 2) ≫
            (Rep.FiniteCyclicGroup.homResolutionIso A g hg).inv.f 2 =
          (Rep.FiniteCyclicGroup.homResolutionIso A g hg).inv.f 2) =
        ((cyclicPeriodicH2ScIso A g).inv.τ₂ ≫
            (cyclicPeriodicH2DegreeOwnerIso A g).hom ≫
            (Rep.FiniteCyclicGroup.homResolutionIso A g hg).inv.f 2 =
          (Rep.FiniteCyclicGroup.homResolutionIso A g hg).inv.f 2) := by
    rfl
  exact hOwner.mp hNative

private theorem cyclicPeriodicH2OwnerIso_homologyπ
    (A : Rep R G) (g : G) :
    (cyclicPeriodicH2CyclesOwnerIso A g).hom ≫
        (Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).homologyπ 2 ≫
        (cyclicPeriodicH2HomologyOwnerIso A g).hom =
      ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2).homologyπ := by
  change
    (𝟙 (((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2).cycles)) ≫
        ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2).homologyπ ≫
        𝟙 (((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2).homology) =
      ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).sc 2).homologyπ
  simp only [Category.id_comp, Category.comp_id]

private theorem cyclicPeriodicH2Iso_hom_owner
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (cyclicPeriodicH2Iso A g hg).hom =
      (HomologicalComplex.homologyMapIso
        (Rep.FiniteCyclicGroup.homResolutionIso A g hg) 2).hom ≫
      (cyclicPeriodicH2HomologyOwnerIso A g).hom ≫
      (ShortComplex.homologyMapIso (cyclicPeriodicH2ScIso A g)).hom := by
  rfl

/-- The concrete even cycles transported back to the periodic `Hom` complex. -/
noncomputable def cyclicPeriodicH2CyclesMap
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ModuleCat.of R
        (LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) ⟶
      ((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj R A).cycles 2 :=
  (cyclicPeriodicH2KernelIso A g).hom ≫
    (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatCyclesIso.inv ≫
    (ShortComplex.cyclesMapIso (cyclicPeriodicH2ScIso A g)).inv ≫
    (cyclicPeriodicH2CyclesOwnerIso A g).hom ≫
    (HomologicalComplex.cyclesMapIso
      (Rep.FiniteCyclicGroup.homResolutionIso A g hg) 2).inv

theorem cyclicPeriodicH2CyclesMap_iCycles
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    cyclicPeriodicH2CyclesMap A g hg ≫
        ((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj R A).iCycles 2 =
      (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatLeftHomologyData.i ≫
        (Rep.FiniteCyclicGroup.homResolutionIso A g hg).inv.f 2 := by
  change
    cyclicPeriodicH2CyclesMap A g hg ≫
        ((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj R A).iCycles 2 =
      (cyclicPeriodicH2KernelIso A g).hom ≫
        ((Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatLeftHomologyData.i ≫
          (Rep.FiniteCyclicGroup.homResolutionIso A g hg).inv.f 2)
  unfold cyclicPeriodicH2CyclesMap
  simp only [HomologicalComplex.cyclesMapIso_inv,
    ShortComplex.cyclesMapIso_inv, Category.assoc]
  slice_lhs 5 6 =>
    erw [HomologicalComplex.cyclesMap_i]
  slice_lhs 4 5 =>
    erw [cyclicPeriodicH2CyclesOwnerIso_hom_iCycles]
  slice_lhs 3 4 =>
    erw [ShortComplex.cyclesMap_i]
  slice_lhs 2 3 =>
    erw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
  slice_lhs 3 5 =>
    exact cyclicPeriodicH2DegreeOwners_comp_homResolutionIso_inv A g hg

theorem cyclicPeriodicH2CyclesMap_iCycles_apply
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    (((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj R A).iCycles 2).hom
        ((cyclicPeriodicH2CyclesMap A g hg).hom a) =
      ((Rep.FiniteCyclicGroup.homResolutionIso A g hg).inv.f 2).hom a.1 := by
  exact congrArg (fun f ↦ f.hom a)
    (cyclicPeriodicH2CyclesMap_iCycles A g hg)

theorem cyclicPeriodicH2CyclesMap_homologyπ
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    cyclicPeriodicH2CyclesMap A g hg ≫
        ((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj R A).homologyπ 2 ≫
        (cyclicPeriodicH2Iso A g hg).hom =
      (ShortComplex.moduleCatCyclesIso
        (Rep.FiniteCyclicGroup.normHomCompSub A g)).inv ≫
        ShortComplex.homologyπ
          (Rep.FiniteCyclicGroup.normHomCompSub A g) := by
  change
    cyclicPeriodicH2CyclesMap A g hg ≫
        ((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj R A).homologyπ 2 ≫
        (cyclicPeriodicH2Iso A g hg).hom =
      (cyclicPeriodicH2KernelIso A g).hom ≫
        ((ShortComplex.moduleCatCyclesIso
          (Rep.FiniteCyclicGroup.normHomCompSub A g)).inv ≫
          ShortComplex.homologyπ
            (Rep.FiniteCyclicGroup.normHomCompSub A g))
  unfold cyclicPeriodicH2CyclesMap
  rw [cyclicPeriodicH2Iso_hom_owner]
  simp only [HomologicalComplex.cyclesMapIso_inv,
    ShortComplex.cyclesMapIso_inv,
    HomologicalComplex.homologyMapIso_hom,
    ShortComplex.homologyMapIso_hom, Category.assoc]
  slice_lhs 6 7 =>
    exact HomologicalComplex.homologyπ_naturality
      (Rep.FiniteCyclicGroup.homResolutionIso A g hg).hom 2
  slice_lhs 5 6 =>
    change
      (HomologicalComplex.cyclesMapIso
          (Rep.FiniteCyclicGroup.homResolutionIso A g hg) 2).inv ≫
        (HomologicalComplex.cyclesMapIso
          (Rep.FiniteCyclicGroup.homResolutionIso A g hg) 2).hom
    exact Iso.inv_hom_id _
  simp only [Category.id_comp, Category.assoc]
  slice_lhs 4 6 =>
    exact cyclicPeriodicH2OwnerIso_homologyπ A g
  slice_lhs 4 5 =>
    exact ShortComplex.homologyπ_naturality
      (cyclicPeriodicH2ScIso A g).hom
  slice_lhs 3 4 =>
    change
      (ShortComplex.cyclesMapIso (cyclicPeriodicH2ScIso A g)).inv ≫
        (ShortComplex.cyclesMapIso (cyclicPeriodicH2ScIso A g)).hom
    exact Iso.inv_hom_id _
  simp only [Category.id_comp]

/-- The periodic representative maps to Mathlib's canonical even cohomology class. -/
theorem cyclicPeriodicH2CyclesMap_groupCohomologyIso_inv
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    cyclicPeriodicH2CyclesMap A g hg ≫
        ((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj R A).homologyπ 2 ≫
        (groupCohomologyIso A 2
          (Rep.FiniteCyclicGroup.resolution R g hg)).inv =
      Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 (by simp) := by
  change
    cyclicPeriodicH2CyclesMap A g hg ≫
        ((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj R A).homologyπ 2 ≫
      (groupCohomologyIso A 2
          (Rep.FiniteCyclicGroup.resolution R g hg)).inv =
      (ShortComplex.moduleCatCyclesIso
        (Rep.FiniteCyclicGroup.normHomCompSub A g)).inv ≫
        ShortComplex.homologyπ
          (Rep.FiniteCyclicGroup.normHomCompSub A g) ≫
        (Rep.FiniteCyclicGroup.groupCohomologyIsoEven
          A g hg 2 (by simp)).inv
  rw [show Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 (by simp) =
    groupCohomologyIso A 2
        (Rep.FiniteCyclicGroup.resolution R g hg) ≪≫
      cyclicPeriodicH2Iso A g hg by
        rw [cyclicPeriodicH2Iso_eq]
        rfl]
  simp only [Iso.trans_inv]
  let f :
      ModuleCat.of R
          (LinearMap.ker
            (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) ⟶
        ((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj
          R A).homology 2 :=
    cyclicPeriodicH2CyclesMap A g hg ≫
      ((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj
        R A).homologyπ 2
  let n :
      ModuleCat.of R
          (LinearMap.ker
            (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) ⟶
        (Rep.FiniteCyclicGroup.normHomCompSub A g).homology :=
    (cyclicPeriodicH2KernelIso A g).hom ≫
      (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatCyclesIso.inv ≫
      (Rep.FiniteCyclicGroup.normHomCompSub A g).homologyπ
  let e := cyclicPeriodicH2Iso A g hg
  let j := (groupCohomologyIso A 2
    (Rep.FiniteCyclicGroup.resolution R g hg)).inv
  have hfe : f ≫ e.hom = n := by
    exact Eq.mp (by rfl)
      (cyclicPeriodicH2CyclesMap_homologyπ A g hg)
  have hRaw : f ≫ j = (n ≫ e.inv) ≫ j := by
    calc
      f ≫ j = f ≫ (e.hom ≫ e.inv ≫ j) :=
        congrArg (fun k ↦ f ≫ k) (Iso.hom_inv_id_assoc e j).symm
      _ = (f ≫ e.hom) ≫ (e.inv ≫ j) :=
        (Category.assoc f e.hom (e.inv ≫ j)).symm
      _ = n ≫ (e.inv ≫ j) :=
        congrArg (fun k ↦ k ≫ (e.inv ≫ j)) hfe
      _ = (n ≫ e.inv) ≫ j :=
        (Category.assoc n e.inv j).symm
  exact Eq.mp (by rfl) hRaw

theorem cyclicPeriodicH2CyclesMap_groupCohomologyIso_inv_apply
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    (groupCohomologyIso A 2
      (Rep.FiniteCyclicGroup.resolution R g hg)).inv.hom
        ((((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj R A).homologyπ 2).hom
          ((cyclicPeriodicH2CyclesMap A g hg).hom a)) =
      (Rep.FiniteCyclicGroup.groupCohomologyπEven
        A g hg 2 (by simp)).hom a := by
  exact congrArg (fun f ↦ f.hom a)
    (cyclicPeriodicH2CyclesMap_groupCohomologyIso_inv A g hg)

/-- Applying `Hom(-, A)` to the explicit bar-to-periodic comparison. -/
noncomputable def finiteCyclicBarToPeriodicLinearYonedaMap
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj R A ⟶
      (Rep.barResolution R G).complex.linearYonedaObj R A :=
  resolutionLinearYonedaMap
    (Rep.barResolution R G)
    (Rep.FiniteCyclicGroup.resolution R g hg)
    (finiteCyclicBarToPeriodicResolutionHom (R := R) g hg) A

@[simp]
theorem finiteCyclicBarToPeriodicLinearYonedaMap_f
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (n : ℕ) :
    (finiteCyclicBarToPeriodicLinearYonedaMap A g hg).f n =
      ModuleCat.ofHom (Linear.leftComp R A
        ((finiteCyclicBarToPeriodicComparison (R := R) g hg).f n)) := rfl

/-- The canonical cohomology identifications commute with the explicit comparison. -/
theorem finiteCyclicBarToPeriodic_groupCohomologyIso_hom
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) :
    (groupCohomologyIso A i (Rep.barResolution R G)).hom =
      (groupCohomologyIso A i
          (Rep.FiniteCyclicGroup.resolution R g hg)).hom ≫
        HomologicalComplex.homologyMap
          (finiteCyclicBarToPeriodicLinearYonedaMap A g hg) i := by
  change
    (groupCohomologyIso A i (Rep.barResolution R G)).hom =
      (groupCohomologyIso A i
          (Rep.FiniteCyclicGroup.resolution R g hg)).hom ≫
        HomologicalComplex.homologyMap
          (resolutionLinearYonedaMap
            (Rep.barResolution R G)
            (Rep.FiniteCyclicGroup.resolution R g hg)
            (finiteCyclicBarToPeriodicResolutionHom (R := R) g hg) A) i
  exact groupCohomologyIso_hom_naturality
    (Rep.barResolution R G)
    (Rep.FiniteCyclicGroup.resolution R g hg)
    (finiteCyclicBarToPeriodicResolutionHom (R := R) g hg) A i

/-- The contravariant cochain map obtained from a map of chain complexes. -/
def chainLinearYonedaMap
    {B P : ChainComplex (Rep R G) ℕ} (phi : B ⟶ P) (A : Rep R G) :
    P.linearYonedaObj R A ⟶ B.linearYonedaObj R A :=
  (HomologicalComplex.unopFunctor
      (ModuleCat R) (ComplexShape.down ℕ)).map
    (((((linearYoneda R (Rep R G)).obj A).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map phi).op)

/-- The cochain map induced by the explicit finite-cyclic bar--periodic comparison. -/
noncomputable def finiteCyclicBarPeriodicCochainMap
    (A : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    ((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj R A) ⟶
      ((Rep.barComplex R G).linearYonedaObj R A) :=
  chainLinearYonedaMap
    (finiteCyclicBarToPeriodicComparison (R := R) g hg) A

theorem finiteCyclicBarPeriodicCochainMap_two_carry
    (A : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    Rep.freeLiftLEquiv R G (Fin 2 → G) A
        (((finiteCyclicBarPeriodicCochainMap A g hg).f 2).hom
          (((Rep.FiniteCyclicGroup.homResolutionIso A g hg).inv.f 2).hom
            a.1)) =
      (groupCohomology.cochainsIso₂ A).inv
        (finiteCyclicCarryTwoCocycle A g hg a) := by
  funext x
  change
    ((finiteCyclicBarToPeriodicTwo (R := R) g hg ≫
        Rep.leftRegularHom A a.1).hom
      (Finsupp.single x (MonoidAlgebra.single 1 1))) =
        finiteCyclicCarry g hg (x 0) (x 1) • a.1
  rw [Rep.hom_comp]
  simp only [Representation.IntertwiningMap.comp_apply]
  rw [finiteCyclicBarToPeriodicTwo_generator]
  simp [Nat.cast_smul_eq_nsmul]

/-- The bar-complex cycle represented by the normalized finite-cyclic carry cocycle. -/
noncomputable def finiteCyclicBarCarryCycle
    (A : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    ((Rep.barComplex R G).linearYonedaObj R A).cycles 2 :=
  HomologicalComplex.cyclesMap
    (groupCohomology.inhomogeneousCochainsIso A).hom 2
    ((groupCohomology.isoCocycles₂ A).inv
      (finiteCyclicCarryTwoCocycle A g hg a))

theorem finiteCyclicBarCarryCycle_i
    (A : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    Rep.freeLiftLEquiv R G (Fin 2 → G) A
        (((Rep.barComplex R G).linearYonedaObj R A).iCycles 2
          (finiteCyclicBarCarryCycle A g hg a)) =
      (groupCohomology.cochainsIso₂ A).inv
        (finiteCyclicCarryTwoCocycle A g hg a) := by
  unfold finiteCyclicBarCarryCycle
  have hi := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (groupCohomology.inhomogeneousCochainsIso A).hom 2)
    ((groupCohomology.isoCocycles₂ A).inv
      (finiteCyclicCarryTwoCocycle A g hg a))
  have hi' :
      ((Rep.barComplex R G).linearYonedaObj R A).iCycles 2
          (HomologicalComplex.cyclesMap
            (groupCohomology.inhomogeneousCochainsIso A).hom 2
            ((groupCohomology.isoCocycles₂ A).inv
              (finiteCyclicCarryTwoCocycle A g hg a))) =
        ((groupCohomology.inhomogeneousCochainsIso A).hom.f 2)
          ((groupCohomology.inhomogeneousCochains A).iCycles 2
            ((groupCohomology.isoCocycles₂ A).inv
              (finiteCyclicCarryTwoCocycle A g hg a))) := by
    simpa only [ConcreteCategory.comp_apply] using hi
  rw [hi', groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply]
  simp [groupCohomology.inhomogeneousCochainsIso]
  change
    Rep.freeLiftLEquiv R G (Fin 2 → G) A
        ((Rep.freeLiftLEquiv R G (Fin 2 → G) A).symm
          ((groupCohomology.cochainsIso₂ A).inv
            (finiteCyclicCarryTwoCocycle A g hg a))) = _
  exact LinearEquiv.apply_symm_apply _ _

theorem finiteCyclicBarPeriodic_cyclesMap_eq
    (A : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    HomologicalComplex.cyclesMap
        (finiteCyclicBarPeriodicCochainMap A g hg) 2
        ((cyclicPeriodicH2CyclesMap A g hg).hom a) =
      finiteCyclicBarCarryCycle A g hg a := by
  apply (ModuleCat.mono_iff_injective
    (((Rep.barComplex R G).linearYonedaObj R A).iCycles 2)).1 inferInstance
  apply (Rep.freeLiftLEquiv R G (Fin 2 → G) A).injective
  rw [finiteCyclicBarCarryCycle_i]
  have hi := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (finiteCyclicBarPeriodicCochainMap A g hg) 2)
    ((cyclicPeriodicH2CyclesMap A g hg).hom a)
  have hi' :
      ((Rep.barComplex R G).linearYonedaObj R A).iCycles 2
          (HomologicalComplex.cyclesMap
            (finiteCyclicBarPeriodicCochainMap A g hg) 2
            ((cyclicPeriodicH2CyclesMap A g hg).hom a)) =
        ((finiteCyclicBarPeriodicCochainMap A g hg).f 2)
          ((((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj
            R A).iCycles 2)
              ((cyclicPeriodicH2CyclesMap A g hg).hom a)) := by
    simpa only [ConcreteCategory.comp_apply] using hi
  rw [hi', cyclicPeriodicH2CyclesMap_iCycles_apply]
  exact finiteCyclicBarPeriodicCochainMap_two_carry A g hg a

omit [Fintype G] in
theorem groupCohomologyIso_bar_hom_eq_homologyMap
    (A : Rep R G) :
    (groupCohomologyIso A 2 (Rep.barResolution R G)).hom =
      HomologicalComplex.homologyMap
        (groupCohomology.inhomogeneousCochainsIso A).hom 2 := by
  change
    (groupCohomologyIsoExt A 2).hom ≫
        (Rep.barResolution.extIso R G A 2).hom = _
  rw [show groupCohomologyIsoExt A 2 =
    isoOfQuasiIsoAt
        (HomotopyEquiv.ofIso
          (groupCohomology.inhomogeneousCochainsIso A)).hom 2 ≪≫
      (Rep.barResolution.extIso R G A 2).symm from rfl]
  simp only [Iso.trans_hom]
  let e := Rep.barResolution.extIso R G A 2
  let q := isoOfQuasiIsoAt
    (HomotopyEquiv.ofIso
      (groupCohomology.inhomogeneousCochainsIso A)).hom 2
  calc
    ((q.hom ≫ e.inv) ≫ e.hom) =
        q.hom ≫ (e.inv ≫ e.hom) :=
      Category.assoc q.hom e.inv e.hom
    _ = q.hom ≫ 𝟙 _ :=
      congrArg (fun f ↦ q.hom ≫ f) e.inv_hom_id
    _ = q.hom := Category.comp_id q.hom
    _ = _ := isoOfQuasiIsoAt_hom _ _

theorem groupCohomologyIso_bar_H2π_carry
    (A : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    (groupCohomologyIso A 2 (Rep.barResolution R G)).hom
        (groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a)) =
      ((Rep.barComplex R G).linearYonedaObj R A).homologyπ 2
        (finiteCyclicBarCarryCycle A g hg a) := by
  rw [groupCohomologyIso_bar_hom_eq_homologyMap]
  change
    (((groupCohomology.inhomogeneousCochains A).homologyπ 2 ≫
      HomologicalComplex.homologyMap
        (groupCohomology.inhomogeneousCochainsIso A).hom 2)
        ((groupCohomology.isoCocycles₂ A).inv
          (finiteCyclicCarryTwoCocycle A g hg a))) = _
  rw [HomologicalComplex.homologyπ_naturality]
  rfl

theorem finiteCyclicBarPeriodic_homologyMap_carry
    (A : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    HomologicalComplex.homologyMap
        (finiteCyclicBarPeriodicCochainMap A g hg) 2
        ((((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj
          R A).homologyπ 2)
            ((cyclicPeriodicH2CyclesMap A g hg).hom a)) =
      (groupCohomologyIso A 2 (Rep.barResolution R G)).hom
        (groupCohomology.H2π A
          (finiteCyclicCarryTwoCocycle A g hg a)) := by
  change
    ((((Rep.FiniteCyclicGroup.resolution R g hg).complex.linearYonedaObj
      R A).homologyπ 2 ≫
      HomologicalComplex.homologyMap
        (finiteCyclicBarPeriodicCochainMap A g hg) 2)
      ((cyclicPeriodicH2CyclesMap A g hg).hom a)) = _
  rw [HomologicalComplex.homologyπ_naturality]
  change
    ((Rep.barComplex R G).linearYonedaObj R A).homologyπ 2
        (HomologicalComplex.cyclesMap
          (finiteCyclicBarPeriodicCochainMap A g hg) 2
          ((cyclicPeriodicH2CyclesMap A g hg).hom a)) = _
  rw [finiteCyclicBarPeriodic_cyclesMap_eq]
  exact (groupCohomologyIso_bar_H2π_carry A g hg a).symm

theorem finiteCyclicBarPeriodicCochainMap_eq
    (A : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    finiteCyclicBarPeriodicCochainMap A g hg =
      finiteCyclicBarToPeriodicLinearYonedaMap A g hg := by
  rfl

/-- The normalized carry cocycle represents the periodic class of its
generator-fixed coefficient. -/
theorem H2π_finiteCyclicCarryTwoCocycle
    (A : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a) =
      Rep.FiniteCyclicGroup.groupCohomologyπEven
        A g hg 2 (by simp) a := by
  apply (ModuleCat.mono_iff_injective
    ((groupCohomologyIso A 2 (Rep.barResolution R G)).hom)).1
      inferInstance
  rw [← finiteCyclicBarPeriodic_homologyMap_carry]
  rw [finiteCyclicBarPeriodicCochainMap_eq]
  rw [finiteCyclicBarToPeriodic_groupCohomologyIso_hom A g hg 2]
  rw [ConcreteCategory.comp_apply]
  rw [← cyclicPeriodicH2CyclesMap_groupCohomologyIso_inv_apply
    A g hg a]
  rw [Iso.inv_hom_id_apply]
  rfl

end ClassFieldTower.Cohomology
