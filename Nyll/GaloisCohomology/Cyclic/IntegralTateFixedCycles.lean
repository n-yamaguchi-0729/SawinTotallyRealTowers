/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology
public import Nyll.GaloisCohomology.Cyclic.TateFixedCycles
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Integral Tate fixed representatives in independent universes

The existing native lift carries each original fixed vector to its actual
degree-zero Tate class. Equivariant maps retain the original vector values.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace IntegralGroupCohomology.Universe

universe u v

variable {G : Type u} [Group G] [Fintype G]

/-- The native representation lift carries the same invariants across the
independent group and coefficient universes. -/
def nativeFixedEquiv (A : Rep.{v} ℤ G) :
    A.ρ.invariants ≃+ ((nativeFunctor G).obj A).ρ.invariants where
  toFun a := ⟨ULift.up (a : A), fun g => ULift.ext (a.property g.down)⟩
  invFun a := ⟨(show ULift.{u} A from a.val).down, fun g =>
    congrArg (fun x : (nativeFunctor G).obj A => (show ULift.{u} A from x).down)
      (a.property (ULift.up g))⟩
  left_inv a := Subtype.ext (by rfl)
  right_inv a := Subtype.ext (by rfl)
  map_add' a b := Subtype.ext (by rfl)

/-- The fixed cycle of an original vector, in the existing native Tate complex. -/
def fixedCycle (A : Rep.{v} ℤ G) (a : A.ρ.invariants) :
    (tateComplex ((nativeFunctor G).obj A)).cycles 0 :=
  TateCohomology.fixedCycle ((nativeFunctor G).obj A)
    (nativeFixedEquiv A a)

/-- Its degree-zero cochain is precisely the lift of the original vector. -/
theorem fixedCycle_iCycles (A : Rep.{v} ℤ G) (a : A.ρ.invariants) :
    (tateComplex ((nativeFunctor G).obj A)).iCycles 0 (fixedCycle A a) =
      (groupCohomology.cochainsIso₀ ((nativeFunctor G).obj A)).inv
        (ULift.up (a : A)) :=
  TateCohomology.fixedCycle_iCycles ((nativeFunctor G).obj A) _

/-- The native cycle map preserves the actual lifted image of a fixed vector. -/
theorem fixedCycle_map {A B : Rep.{v} ℤ G} (f : A ⟶ B) (a : A.ρ.invariants) :
    HomologicalComplex.cyclesMap (tateComplex.map ((nativeFunctor G).map f)) 0
        (fixedCycle A a) =
      fixedCycle B ⟨f a, fun g => by rw [← Rep.hom_comm_apply, a.2 g]⟩ :=
  TateCohomology.fixedCycle_map ((nativeFunctor G).map f) _

/-- The actual integral Tate class represented by an original fixed vector. -/
def fixedClass (A : Rep.{v} ℤ G) (a : A.ρ.invariants) : tate A 0 :=
  (tateComplex ((nativeFunctor G).obj A)).homologyπ 0 (fixedCycle A a)

/-- Equivariant naturality uses the actual integral Tate functor on fixed representatives. -/
theorem fixedClass_map {A B : Rep.{v} ℤ G} (f : A ⟶ B) (a : A.ρ.invariants) :
    (tateFunctor G 0).map f (fixedClass A a) =
      fixedClass B ⟨f a, fun g => by rw [← Rep.hom_comm_apply, a.2 g]⟩ :=
  TateCohomology.fixedClass_map ((nativeFunctor G).map f) _

/-- The range of the original finite norm inside the original invariant vectors. -/
def fixedNormSubmodule (A : Rep.{v} ℤ G) : Submodule ℤ A.ρ.invariants := by
  let i : A.ρ.invariants →ₗ[ℤ] A := {
    toFun := Subtype.val
    map_add' := fun _ _ => rfl
    map_smul' := fun n x => map_intCast_smul A.ρ.invariants.toAddSubgroup.subtype ℤ ℤ n x }
  exact (LinearMap.range A.ρ.norm).comap i

/-- The norm short complex in the existing lifted Tate representation. -/
abbrev nativeFixedNormComplex (A : Rep.{v} ℤ G) : ShortComplex (ModuleCat (ULift.{max u v} ℤ)) :=
  let M := (nativeFunctor G).obj A
  .mk M.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ M) (Rep.norm_comp_d_eq_zero M)

/-- Cycles in the concrete lifted norm complex are the original fixed vectors. -/
def nativeFixedNormCyclesEquiv (A : Rep.{v} ℤ G) :
    (nativeFixedNormComplex A).moduleCatLeftHomologyData.K ≃+ A.ρ.invariants := by
  let M := (nativeFunctor G).obj A
  exact {
    toFun := fun x => (nativeFixedEquiv A).symm ⟨x.val, fun g => by
      have hx : groupCohomology.d₀₁ M x.val = 0 := x.property
      exact sub_eq_zero.mp (congrFun hx g)⟩
    invFun := fun a => ⟨(nativeFixedEquiv A a).val, by
      change groupCohomology.d₀₁ M (nativeFixedEquiv A a).val = 0
      funext g
      exact sub_eq_zero.mpr ((nativeFixedEquiv A a).property g)⟩
    left_inv := fun _ => Subtype.ext (by rfl)
    right_inv := fun _ => Subtype.ext (by rfl)
    map_add' := fun _ _ => Subtype.ext (by rfl) }

/-- The concrete lifted homology quotient respects the original norm image. -/
def nativeFixedNormHomologyEquiv (A : Rep.{v} ℤ G) :
    (nativeFixedNormComplex A).moduleCatLeftHomologyData.H ≃+
      (A.ρ.invariants ⧸ fixedNormSubmodule A) := by
  let S := nativeFixedNormComplex A
  let eK := nativeFixedNormCyclesEquiv A
  let N : AddSubgroup S.moduleCatLeftHomologyData.K :=
    (LinearMap.range S.moduleCatLeftHomologyData.f'.hom).toAddSubgroup
  have hboundary :
      N.map eK.toAddMonoidHom = (fixedNormSubmodule A).toAddSubgroup := by
    ext a
    change a ∈ N.map eK.toAddMonoidHom ↔ (a : A) ∈ LinearMap.range A.ρ.norm
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      let w : A := (show ULift.{u} A from z).down
      exact ⟨w, (nativeFunctor_norm_down A w).symm⟩
    · rintro ⟨z, hz⟩
      refine ⟨S.moduleCatLeftHomologyData.f' (ULift.up z), ⟨ULift.up z, rfl⟩, ?_⟩
      apply Subtype.ext
      exact (nativeFunctor_norm_down A z).trans hz
  exact QuotientAddGroup.congr N (fixedNormSubmodule A).toAddSubgroup eK hboundary

/-- The norm boundary calculation identifies actual degree-zero Tate cohomology
with the original fixed vectors modulo the original norm image. -/
def tateZeroEquivFixedQuotient (A : Rep.{v} ℤ G) :
    tate A 0 ≃+ (A.ρ.invariants ⧸ fixedNormSubmodule A) :=
  let e := TateCohomology.isoZeroBoundary ((nativeFunctor G).obj A) ≪≫
    (nativeFixedNormComplex A).moduleCatHomologyIso
  e.toLinearEquiv.toAddEquiv.trans (nativeFixedNormHomologyEquiv A)

/-- The comparison evaluates an actual Tate class on its original fixed representative. -/
theorem tateZeroEquivFixedQuotient_fixedClass (A : Rep.{v} ℤ G) (a : A.ρ.invariants) :
    tateZeroEquivFixedQuotient A (fixedClass A a) = (fixedNormSubmodule A).mkQ a := by
  let M := (nativeFunctor G).obj A
  let S := nativeFixedNormComplex A
  let b := nativeFixedEquiv A a
  let x : S.moduleCatLeftHomologyData.K := ⟨b.val, by
    change groupCohomology.d₀₁ M b.val = 0
    funext g
    exact sub_eq_zero.mpr (b.property g)⟩
  have hcycle : (TateCohomology.isoZeroBoundary M).hom (fixedClass A a) =
      S.homologyπ (S.moduleCatCyclesIso.inv x) :=
    TateCohomology.isoZeroBoundary_fixedCycle M b
  have hclass :
      S.moduleCatHomologyIso.hom (S.homologyπ (S.moduleCatCyclesIso.inv x)) =
        S.moduleCatLeftHomologyData.π x :=
    (ShortComplex.π_moduleCatCyclesIso_hom_apply S (S.moduleCatCyclesIso.inv x)).trans
      (congrArg (fun z : S.moduleCatLeftHomologyData.K => S.moduleCatLeftHomologyData.π z)
        (Iso.inv_hom_id_apply S.moduleCatCyclesIso x))
  change nativeFixedNormHomologyEquiv A
      (S.moduleCatHomologyIso.hom ((TateCohomology.isoZeroBoundary M).hom (fixedClass A a))) = _
  rw [hcycle, hclass]
  have hx : nativeFixedNormCyclesEquiv A x = a := (nativeFixedEquiv A).symm_apply_apply a
  exact (congrArg (fixedNormSubmodule A).mkQ hx :
    (fixedNormSubmodule A).mkQ (nativeFixedNormCyclesEquiv A x) = (fixedNormSubmodule A).mkQ a)

/-- Every actual degree-zero Tate class has an original fixed representative. -/
theorem fixedClass_surjective (A : Rep.{v} ℤ G) : Function.Surjective (fixedClass A) := by
  intro x
  obtain ⟨a, ha⟩ := (fixedNormSubmodule A).mkQ_surjective (tateZeroEquivFixedQuotient A x)
  exact ⟨a, (tateZeroEquivFixedQuotient A).injective
    ((tateZeroEquivFixedQuotient_fixedClass A a).trans ha)⟩

end IntegralGroupCohomology.Universe
