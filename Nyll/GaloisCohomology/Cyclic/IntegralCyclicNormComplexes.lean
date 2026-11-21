/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RepresentationTheory.Homological.FiniteCyclic
public import Nyll.GaloisCohomology.Cyclic.IntegralNormKernelVanishing
public import Nyll.GaloisCohomology.Cyclic.IntegralTateFixedCycles
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology
public import Nyll.GaloisCohomology.Cyclic.TateComparison
public import Nyll.GaloisCohomology.Cyclic.TateFixedCycles
public import Nyll.SchemeTheory.HomologicalAlgebra.HomologySequenceExactFunctor

/-!
# Original cyclic norm complexes and integral Tate cohomology

The acting group and the integer representation carrier have independent universes. The two
short complexes use the original norm and the original action minus the identity. Lifting their
carriers gives the native finite-cyclic short complexes of the same lifted representation,
with scalars restricted back to integers. The induced homology equivalences therefore connect
the original norm quotients and exactness assertions to actual integral Tate cohomology.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable {G : Type u}

section Finite

variable [Group G] [Fintype G]

/-- The original integer norm followed by the original action minus the identity. -/
def normHomCompSub (A : Rep.{v} ℤ G) (g : G) : ShortComplex (ModuleCat.{v} ℤ) :=
  ShortComplex.mk (ModuleCat.ofHom A.norm.asHom.hom.toLinearMap)
    (ModuleCat.ofHom (A.ρ g - LinearMap.id)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change A.ρ g (A.ρ.norm x) - A.ρ.norm x = 0
      exact sub_eq_zero.mpr (Representation.self_norm_apply A.ρ g x))

/-- The original action minus the identity followed by the original integer norm. -/
def subCompNormHom (A : Rep.{v} ℤ G) (g : G) : ShortComplex (ModuleCat.{v} ℤ) :=
  ShortComplex.mk (ModuleCat.ofHom (A.ρ g - LinearMap.id))
    (ModuleCat.ofHom A.norm.asHom.hom.toLinearMap) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change A.ρ.norm (A.ρ g x - x) = 0
      rw [map_sub, Representation.norm_self_apply, sub_self])

/-- The first differential is the actual norm of the original representation. -/
theorem normHomCompSub_f_apply (A : Rep.{v} ℤ G) (g : G) (x : A) :
    (normHomCompSub A g).f x = A.norm.asHom.hom x := rfl

/-- The second differential is the original action minus the original coefficient. -/
theorem normHomCompSub_g_apply (A : Rep.{v} ℤ G) (g : G) (x : A) :
    (normHomCompSub A g).g x = A.ρ g x - x := rfl

/-- The first differential is the original action minus the original coefficient. -/
theorem subCompNormHom_f_apply (A : Rep.{v} ℤ G) (g : G) (x : A) :
    (subCompNormHom A g).f x = A.ρ g x - x := rfl

/-- The second differential is the actual norm of the original representation. -/
theorem subCompNormHom_g_apply (A : Rep.{v} ℤ G) (g : G) (x : A) :
    (subCompNormHom A g).g x = A.norm.asHom.hom x := rfl

omit [Fintype G] in
/-- The lifted original carrier with its original integer action is the native carrier
after restricting the lifted integer coefficients. The underlying map is identity. -/
def nativeIntegerCarrierIso (A : Rep.{v} ℤ G) :
    (ModuleCat.uliftFunctor.{u, v} ℤ).obj (ModuleCat.of ℤ A) ≅
      integerScalars.obj (ModuleCat.of (ULift.{max u v} ℤ) ((nativeFunctor G).obj A)) :=
  LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.uliftFunctor.{u, v} ℤ).obj (ModuleCat.of ℤ A))
    (X₂ := integerScalars.obj (ModuleCat.of (ULift.{max u v} ℤ) ((nativeFunctor G).obj A)))
    (m₁ := ((ModuleCat.uliftFunctor.{u, v} ℤ).obj (ModuleCat.of ℤ A)).isModule)
    (m₂ := (integerScalars.obj
      (ModuleCat.of (ULift.{max u v} ℤ) ((nativeFunctor G).obj A))).isModule)
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

end Finite

section Commutative

variable [CommGroup G] [Fintype G]

/-- Lifting the original norm complex gives the actual native finite-cyclic complex
with its scalar action restricted to integers. Every component keeps the same coefficient. -/
def normHomCompSubLiftIso (A : Rep.{v} ℤ G) (g : G) :
    (normHomCompSub A g).map (ModuleCat.uliftFunctor.{u, v} ℤ) ≅
      (Rep.FiniteCyclicGroup.normHomCompSub ((nativeFunctor G).obj A)
        (ULift.up g)).map integerScalars := by
  refine ShortComplex.isoMk (nativeIntegerCarrierIso A) (nativeIntegerCarrierIso A)
    (nativeIntegerCarrierIso A) ?_ ?_
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (Equiv.ulift : ULift.{u} A ≃ A).injective
    exact nativeFunctor_norm_down A x.down
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- Lifting the original reverse norm complex gives the actual native reverse complex
with its scalar action restricted to integers. Every component keeps the same coefficient. -/
def subCompNormHomLiftIso (A : Rep.{v} ℤ G) (g : G) :
    (subCompNormHom A g).map (ModuleCat.uliftFunctor.{u, v} ℤ) ≅
      (Rep.FiniteCyclicGroup.subCompNormHom ((nativeFunctor G).obj A)
        (ULift.up g)).map integerScalars := by
  refine ShortComplex.isoMk (nativeIntegerCarrierIso A) (nativeIntegerCarrierIso A)
    (nativeIntegerCarrierIso A) ?_ ?_
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (Equiv.ulift : ULift.{u} A ≃ A).injective
    exact nativeFunctor_norm_down A x.down

end Commutative

section Cyclic

variable [Group G] [Fintype G]

private theorem homologyOfLiftIso_class
    (S : ShortComplex (ModuleCat.{v} ℤ))
    (T : ShortComplex (ModuleCat.{max u v} (ULift.{max u v} ℤ)))
    (e : S.map (ModuleCat.uliftFunctor.{u, v} ℤ) ≅ T.map integerScalars)
    (x : LinearMap.ker S.g.hom) (y : LinearMap.ker T.g.hom)
    (hxy : e.hom.τ₂ (ULift.up x.val) = y.val) :
    let F := ModuleCat.uliftFunctor.{u, v} ℤ
    let H := integerScalars.{max u v}
    (T.mapHomologyIso H).hom ((ShortComplex.homologyMapIso e).hom
      ((S.mapHomologyIso F).inv (ULift.up (S.homologyπ (S.moduleCatCyclesIso.inv x))))) =
      T.homologyπ (T.moduleCatCyclesIso.inv y) := by
  intro F H
  let zS := S.moduleCatCyclesIso.inv x
  let zT := T.moduleCatCyclesIso.inv y
  let cS := (S.mapCyclesIso F).inv (ULift.up zS)
  let cT := (T.mapCyclesIso H).inv zT
  have hs : (S.mapCyclesIso F).hom cS = ULift.up zS := Iso.inv_hom_id_apply _ _
  have ht : (T.mapCyclesIso H).hom cT = zT := Iso.inv_hom_id_apply _ _
  have hs₂ : (S.map F).iCycles cS = ULift.up x.val := by
    have h := congrArg (fun f => f cS) (S.mapCyclesIso_hom_iCycles F)
    simp only [ModuleCat.comp_apply, hs] at h
    exact h.symm.trans (congrArg ULift.up (S.moduleCatCyclesIso_inv_iCycles_apply x))
  have ht₂ : (T.map H).iCycles cT = y.val := by
    have h := congrArg (fun f => f cT) (T.mapCyclesIso_hom_iCycles H)
    simp only [ModuleCat.comp_apply, ht] at h
    exact h.symm.trans (T.moduleCatCyclesIso_inv_iCycles_apply y)
  have hcycle : ShortComplex.cyclesMap e.hom cS = cT := by
    apply (ModuleCat.mono_iff_injective (T.map H).iCycles).mp inferInstance
    have h := congrArg (fun f => f cS) (ShortComplex.cyclesMap_i e.hom)
    simp only [ModuleCat.comp_apply] at h
    exact h.trans ((congrArg e.hom.τ₂ hs₂).trans (hxy.trans ht₂.symm))
  have hSπ : (S.mapHomologyIso F).inv (ULift.up (S.homologyπ zS)) =
      (S.map F).homologyπ cS := by
    apply (ModuleCat.mono_iff_injective (S.mapHomologyIso F).hom).mp inferInstance
    let qS : F.obj S.homology := ULift.up (S.homologyπ zS)
    have h := congrArg (fun f => f cS) (S.homologyπ_mapHomologyIso_hom F)
    simp only [ModuleCat.comp_apply, hs] at h
    exact (Iso.inv_hom_id_apply (S.mapHomologyIso F) qS).trans h.symm
  have hTπ : (T.mapHomologyIso H).hom ((T.map H).homologyπ cT) = T.homologyπ zT := by
    have h := congrArg (fun f => f cT) (T.homologyπ_mapHomologyIso_hom H)
    simp only [ModuleCat.comp_apply, ht] at h
    exact h
  have hmap : (ShortComplex.homologyMapIso e).hom ((S.map F).homologyπ cS) =
      (T.map H).homologyπ cT := by
    change ((S.map F).homologyπ ≫ ShortComplex.homologyMap e.hom) cS = _
    rw [ShortComplex.homologyπ_naturality, ModuleCat.comp_apply, hcycle]
  change (T.mapHomologyIso H).hom ((ShortComplex.homologyMapIso e).hom
    ((S.mapHomologyIso F).inv (ULift.up (S.homologyπ zS)))) = T.homologyπ zT
  rw [hSπ, hmap, hTπ]

/-- The original norm complex computes the actual integral Tate object in degree zero. -/
def normHomologyEquivTateZero (A : Rep.{v} ℤ G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    (normHomCompSub A g).homology ≃+ tate A 0 := by
  let : IsCyclic G := CyclicCohomology.isCyclic_of_generator g hg
  let : CommGroup G := IsCyclic.commGroup (α := G)
  let M := (nativeFunctor G).obj A
  let S := normHomCompSub A g
  let T := Rep.FiniteCyclicGroup.normHomCompSub M (ULift.up g)
  let e : (ModuleCat.uliftFunctor.{u, v} ℤ).obj S.homology ≅ tate A 0 :=
    (S.mapHomologyIso (ModuleCat.uliftFunctor.{u, v} ℤ)).symm ≪≫
      ShortComplex.homologyMapIso (normHomCompSubLiftIso A g) ≪≫
      T.mapHomologyIso integerScalars ≪≫
      integerScalars.mapIso
        (TateCohomology.isoFiniteCyclicZero M (ULift.up g) (ulift_generator g hg)).symm
  exact (AddEquiv.ulift : ULift.{u} S.homology ≃+ S.homology).symm.trans
    e.toLinearEquiv.toAddEquiv

/-- The original cyclic norm-complex class of a fixed vector is sent to its
actual Tate class. The comparison uses the specified generator throughout. -/
theorem normHomologyEquivTateZero_fixed (A : Rep.{v} ℤ G) (g : G)
    (hg : ∀ h : G, h ∈ Subgroup.zpowers g) (a : A.ρ.invariants) :
    let S := normHomCompSub A g
    normHomologyEquivTateZero A g hg
      (S.homologyπ (S.moduleCatCyclesIso.inv
        ⟨(a : A), sub_eq_zero.mpr (a.property g)⟩)) = fixedClass A a := by
  intro S
  let : IsCyclic G := CyclicCohomology.isCyclic_of_generator g hg
  let : CommGroup G := IsCyclic.commGroup (α := G)
  let M := (nativeFunctor G).obj A
  let b := nativeFixedEquiv A a
  let T := Rep.FiniteCyclicGroup.normHomCompSub M (ULift.up g)
  let F := ModuleCat.uliftFunctor.{u, v} ℤ
  let H := integerScalars.{max u v}
  let e := normHomCompSubLiftIso A g
  let x : LinearMap.ker S.g.hom := ⟨(a : A), sub_eq_zero.mpr (a.property g)⟩
  let y : LinearMap.ker T.g.hom := ⟨(b : M), sub_eq_zero.mpr (b.property (ULift.up g))⟩
  let zS := S.moduleCatCyclesIso.inv x
  let zT := T.moduleCatCyclesIso.inv y
  let eT := TateCohomology.isoFiniteCyclicZero M (ULift.up g) (ulift_generator g hg)
  change eT.inv ((T.mapHomologyIso H).hom ((ShortComplex.homologyMapIso e).hom
    ((S.mapHomologyIso F).inv (ULift.up (S.homologyπ zS))))) = fixedClass A a
  have hcomp := homologyOfLiftIso_class S T e x y rfl
  change (T.mapHomologyIso H).hom ((ShortComplex.homologyMapIso e).hom
    ((S.mapHomologyIso F).inv (ULift.up (S.homologyπ zS)))) = T.homologyπ zT at hcomp
  let aT : tateCohomology M 0 := fixedClass A a
  have hT : eT.hom aT = T.homologyπ zT :=
    TateCohomology.isoFiniteCyclicZero_fixedClass M (ULift.up g) (ulift_generator g hg) b
  exact (congrArg eT.inv (hcomp.trans hT.symm)).trans (Iso.hom_inv_id_apply eT aT)

/-- The original reverse norm complex computes actual integral Tate cohomology
in degree minus one. -/
def subNormHomologyEquivTateMinusOne (A : Rep.{v} ℤ G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    (subCompNormHom A g).homology ≃+ tate A (-1) := by
  let : IsCyclic G := CyclicCohomology.isCyclic_of_generator g hg
  let : CommGroup G := IsCyclic.commGroup (α := G)
  let M := (nativeFunctor G).obj A
  let S := subCompNormHom A g
  let T := Rep.FiniteCyclicGroup.subCompNormHom M (ULift.up g)
  let e : (ModuleCat.uliftFunctor.{u, v} ℤ).obj S.homology ≅ tate A (-1) :=
    (S.mapHomologyIso (ModuleCat.uliftFunctor.{u, v} ℤ)).symm ≪≫
      ShortComplex.homologyMapIso (subCompNormHomLiftIso A g) ≪≫
      T.mapHomologyIso integerScalars ≪≫
      integerScalars.mapIso
        (TateCohomology.isoFiniteCyclicNegOne M (ULift.up g) (ulift_generator g hg)).symm
  exact (AddEquiv.ulift : ULift.{u} S.homology ≃+ S.homology).symm.trans
    e.toLinearEquiv.toAddEquiv

/-- The Tate class of an original norm-kernel vector in independent universes. -/
def normKernelClass (A : Rep.{v} ℤ G) (a : LinearMap.ker A.ρ.norm) : tate A (-1) :=
  TateCohomology.normKernelClass ((nativeFunctor G).obj A)
    ⟨ULift.up (a : A), by
      apply ULift.ext
      exact (nativeFunctor_norm_down A (a : A)).trans a.property⟩

/-- The reverse norm complex and the actual Tate complex give the same class
of the original norm-kernel vector for the specified generator. -/
theorem subNormHomologyEquivTateMinusOne_normKernel (A : Rep.{v} ℤ G) (g : G)
    (hg : ∀ h : G, h ∈ Subgroup.zpowers g) (a : LinearMap.ker A.ρ.norm) :
    let S := subCompNormHom A g
    subNormHomologyEquivTateMinusOne A g hg
      (S.homologyπ (S.moduleCatCyclesIso.inv a)) = normKernelClass A a := by
  intro S
  let : IsCyclic G := CyclicCohomology.isCyclic_of_generator g hg
  let : CommGroup G := IsCyclic.commGroup (α := G)
  let M := (nativeFunctor G).obj A
  let T := Rep.FiniteCyclicGroup.subCompNormHom M (ULift.up g)
  let F := ModuleCat.uliftFunctor.{u, v} ℤ
  let H := integerScalars.{max u v}
  let e := subCompNormHomLiftIso A g
  let b : LinearMap.ker M.ρ.norm := ⟨ULift.up (a : A), by
    apply ULift.ext
    exact (nativeFunctor_norm_down A (a : A)).trans a.property⟩
  let eT := TateCohomology.isoFiniteCyclicNegOne M (ULift.up g) (ulift_generator g hg)
  let zS := S.moduleCatCyclesIso.inv a
  let zT := T.moduleCatCyclesIso.inv b
  change eT.inv ((T.mapHomologyIso H).hom ((ShortComplex.homologyMapIso e).hom
    ((S.mapHomologyIso F).inv (ULift.up (S.homologyπ zS))))) = normKernelClass A a
  have hcomp := homologyOfLiftIso_class S T e a b rfl
  change (T.mapHomologyIso H).hom ((ShortComplex.homologyMapIso e).hom
    ((S.mapHomologyIso F).inv (ULift.up (S.homologyπ zS)))) = T.homologyπ zT at hcomp
  let aT : tateCohomology M (-1) := normKernelClass A a
  have hT : eT.hom aT = T.homologyπ zT :=
    TateCohomology.isoFiniteCyclicNegOne_normKernelClass M (ULift.up g)
      (ulift_generator g hg) b
  exact (congrArg eT.inv (hcomp.trans hT.symm)).trans (Iso.hom_inv_id_apply eT aT)

/-- Actual degree-zero Tate vanishing is exactness of the original norm and action maps. -/
theorem isZero_tateZero_iff_exact (A : Rep.{v} ℤ G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Limits.IsZero (tate A 0) ↔ (normHomCompSub A g).Exact := by
  let e := normHomologyEquivTateZero A g hg
  constructor
  · intro h
    let : Subsingleton (tate A 0) := ModuleCat.subsingleton_of_isZero h
    let : Subsingleton (normHomCompSub A g).homology :=
      ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩
    exact (normHomCompSub A g).exact_iff_isZero_homology.mpr
      (ModuleCat.isZero_of_subsingleton _)
  · intro h
    let : Subsingleton (normHomCompSub A g).homology :=
      ModuleCat.subsingleton_of_isZero ((normHomCompSub A g).exact_iff_isZero_homology.mp h)
    let : Subsingleton (tate A 0) :=
      ⟨fun x y => e.symm.injective (Subsingleton.elim (e.symm x) (e.symm y))⟩
    exact ModuleCat.isZero_of_subsingleton _

/-- Actual degree-minus-one Tate vanishing is exactness of the original action and norm maps. -/
theorem isZero_tateMinusOne_iff_exact (A : Rep.{v} ℤ G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Limits.IsZero (tate A (-1)) ↔ (subCompNormHom A g).Exact := by
  let e := subNormHomologyEquivTateMinusOne A g hg
  constructor
  · intro h
    let : Subsingleton (tate A (-1)) := ModuleCat.subsingleton_of_isZero h
    let : Subsingleton (subCompNormHom A g).homology :=
      ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩
    exact (subCompNormHom A g).exact_iff_isZero_homology.mpr
      (ModuleCat.isZero_of_subsingleton _)
  · intro h
    let : Subsingleton (subCompNormHom A g).homology :=
      ModuleCat.subsingleton_of_isZero ((subCompNormHom A g).exact_iff_isZero_homology.mp h)
    let : Subsingleton (tate A (-1)) :=
      ⟨fun x y => e.symm.injective (Subsingleton.elim (e.symm x) (e.symm y))⟩
    exact ModuleCat.isZero_of_subsingleton _

end Cyclic

section Original

variable {H : Type} [CommGroup H] [Fintype H] (A : Rep.{0} ℤ H) (g : H)

/-- In universe zero the original norm complex is exactly the pinned native short complex. -/
theorem normHomCompSub_eq_native :
    normHomCompSub A g = Rep.FiniteCyclicGroup.normHomCompSub A g := rfl

/-- In universe zero the original reverse complex is exactly the pinned native short complex. -/
theorem subCompNormHom_eq_native :
    subCompNormHom A g = Rep.FiniteCyclicGroup.subCompNormHom A g := rfl

end Original

end IntegralGroupCohomology.Universe
