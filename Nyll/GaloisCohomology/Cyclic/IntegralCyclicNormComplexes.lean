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
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology
public import Nyll.GaloisCohomology.Cyclic.TateComparison

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
