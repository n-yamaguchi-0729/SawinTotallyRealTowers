import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.CoeffMap

set_option autoImplicit false

/-!
# Fox differential: coefficient rings — mod-\(n\) completed group algebra — in class — stage coeff map

The principal declarations in this module are:

- `modNCompletedGroupAlgebraStageCoeffMapInClass`
  The coefficient reduction map on one class-restricted finite quotient stage \(G/U\).
- `modNCompletedGroupAlgebraStageCoeffMapInClass_of`
  The class-indexed stage coefficient map sends a group-like basis element to the same support with
  its coefficient reduced modulo the target modulus.
- `modNCompletedGroupAlgebraStageCoeffMapInClass_single_apply`
  The class-indexed stage coefficient map sends a singleton to the same support with its coefficient
  reduced modulo the target modulus.
- `modNCompletedGroupAlgebraStageCoeffMapInClass_rfl`
  The class-indexed stage coefficient map for reflexive divisibility is the identity ring
  homomorphism.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u


variable {n m k : ℕ}
variable [Fact (0 < n)] [Fact (0 < m)] [Fact (0 < k)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- The coefficient reduction map on one class-restricted finite quotient stage \(G/U\). -/
abbrev modNCompletedGroupAlgebraStageCoeffMapInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) (hnm : n ∣
        m) :
    ModNCompletedGroupAlgebraStageInClass m G C U →+*
      ModNCompletedGroupAlgebraStageInClass n G C U :=
  modNCompletedGroupRingCoeffMap (n := n) (m := m)
    (CompletedGroupAlgebraQuotientInClass G C U) hnm

omit [Fact (0 < n)] [Fact (0 < m)] in
/--
The class-indexed stage coefficient map sends a group-like basis element to the same support with
its coefficient reduced modulo the target modulus.
-/
@[simp]
theorem modNCompletedGroupAlgebraStageCoeffMapInClass_of
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) (hnm : n ∣ m)
    (q : CompletedGroupAlgebraQuotientInClass G C U) :
    modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := n) (m := m) (G := G) C U hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m) _ q) =
      MonoidAlgebra.of (ModNCompletedCoeff n) _ q := by
  simpa [modNCompletedGroupAlgebraStageCoeffMapInClass] using
    modNCompletedGroupRingCoeffMap_of (n := n) (m := m)
      (H := CompletedGroupAlgebraQuotientInClass G C U) hnm q

omit [Fact (0 < n)] [Fact (0 < m)] in
/--
The class-indexed stage coefficient map sends a singleton to the same support with its coefficient
reduced modulo the target modulus.
-/
theorem modNCompletedGroupAlgebraStageCoeffMapInClass_single_apply
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) (hnm : n ∣ m)
    (q : CompletedGroupAlgebraQuotientInClass G C U)
    (a : ModNCompletedCoeff m) :
    modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := n) (m := m) (G := G) C U hnm
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single q (modNCompletedCoeffMap (n := n) (m := m) hnm a) := by
  let : Algebra (ModNCompletedCoeff m) (ModNCompletedCoeff n) :=
    ZMod.algebra' (R := ModNCompletedCoeff n) (m := n) (n := m) hnm
  let : Algebra (ModNCompletedCoeff m)
      (ModNCompletedGroupRing n (CompletedGroupAlgebraQuotientInClass G C U)) :=
    inferInstance
  have hcoeff :
      algebraMap (ModNCompletedCoeff m) (ModNCompletedCoeff n) a =
        modNCompletedCoeffMap (n := n) (m := m) hnm a := by
    rfl
  change
    MonoidAlgebra.lift (ModNCompletedCoeff m)
        (ModNCompletedGroupRing n (CompletedGroupAlgebraQuotientInClass G C U))
        (CompletedGroupAlgebraQuotientInClass G C U)
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (CompletedGroupAlgebraQuotientInClass G C U))
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single q (modNCompletedCoeffMap (n := n) (m := m) hnm a)
  rw [MonoidAlgebra.lift_single, MonoidAlgebra.of_apply,
    MonoidAlgebra.smul_single]
  change MonoidAlgebra.single q
      (algebraMap (ModNCompletedCoeff m) (ModNCompletedCoeff n) a * 1) =
    MonoidAlgebra.single q (modNCompletedCoeffMap (n := n) (m := m) hnm a)
  rw [hcoeff, mul_one]

omit [Fact (0 < n)] in
/--
The class-indexed stage coefficient map for reflexive divisibility is the identity ring
homomorphism.
-/
@[simp]
theorem modNCompletedGroupAlgebraStageCoeffMapInClass_rfl
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := n) (m := n) (G := G) C U dvd_rfl =
      RingHom.id _ := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := n) (G := G) C U dvd_rfl x = x)
    x ?_ ?_ ?_
  · intro q
    rw [modNCompletedGroupAlgebraStageCoeffMapInClass_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, hx]
    simp only [modNCompletedGroupAlgebraStageCoeffMapInClass, modNCompletedGroupRingCoeffMap,
  AlgHom.toRingHom_eq_coe, map_intCast]

omit [Fact (0 < n)] [Fact (0 < m)] [Fact (0 < k)] in
/--
Class-indexed stage coefficient maps compose according to transitivity of modulus divisibility.
-/
@[simp 900]
theorem modNCompletedGroupAlgebraStageCoeffMapInClass_comp
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C)
    (hnm : n ∣ m) (hmk : m ∣ k) :
    (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := m) (G := G) C U hnm).comp
        (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := m) (m := k) (G := G) C U hmk) =
      modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := n) (m := k) (G := G) C U (dvd_trans hnm hmk) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((modNCompletedGroupAlgebraStageCoeffMapInClass
            (n := n) (m := m) (G := G) C U hnm).comp
          (modNCompletedGroupAlgebraStageCoeffMapInClass
            (n := m) (m := k) (G := G) C U hmk)) x =
        modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := k) (G := G) C U (dvd_trans hnm hmk) x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, modNCompletedGroupAlgebraStageCoeffMapInClass_of,
      modNCompletedGroupAlgebraStageCoeffMapInClass_of,
      modNCompletedGroupAlgebraStageCoeffMapInClass_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [modNCompletedGroupAlgebraStageCoeffMapInClass, modNCompletedGroupRingCoeffMap,
  AlgHom.toRingHom_eq_coe, map_intCast, RingHom.coe_coe]

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- Class-indexed stage coefficient maps commute with finite-quotient transition maps. -/
@[simp 900]
theorem modNCompletedGroupAlgebraStageCoeffMapInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) (hnm : n ∣ m) :
    (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := m) (G := G) C U hnm).comp
        (modNCompletedGroupAlgebraTransitionInClass m G C hUV) =
      (modNCompletedGroupAlgebraTransitionInClass n G C hUV).comp
        (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := m) (G := G) C V hnm) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((modNCompletedGroupAlgebraStageCoeffMapInClass
            (n := n) (m := m) (G := G) C U hnm).comp
          (modNCompletedGroupAlgebraTransitionInClass m G C hUV)) x =
        ((modNCompletedGroupAlgebraTransitionInClass n G C hUV).comp
          (modNCompletedGroupAlgebraStageCoeffMapInClass
            (n := n) (m := m) (G := G) C V hnm)) x)
    x ?_ ?_ ?_
  · intro q
    let qU : CompletedGroupAlgebraQuotientInClass G C U :=
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q
    have htransitionM :
        modNCompletedGroupAlgebraTransitionInClass m G C hUV
            (MonoidAlgebra.of (ModNCompletedCoeff m) _ q) =
          (MonoidAlgebra.of (ModNCompletedCoeff m) _ qU :
            ModNCompletedGroupAlgebraStageInClass m G C U) := by
      exact modNCompletedGroupAlgebraTransitionInClass_of
        (n := m) (G := G) C hUV q
    have htransitionN :
        modNCompletedGroupAlgebraTransitionInClass n G C hUV
            (MonoidAlgebra.of (ModNCompletedCoeff n) _ q) =
          (MonoidAlgebra.of (ModNCompletedCoeff n) _ qU :
            ModNCompletedGroupAlgebraStageInClass n G C U) := by
      exact modNCompletedGroupAlgebraTransitionInClass_of
        (n := n) (G := G) C hUV q
    simp only [RingHom.comp_apply]
    calc
      modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := m) (G := G) C U hnm
          (modNCompletedGroupAlgebraTransitionInClass m G C hUV
            (MonoidAlgebra.of (ModNCompletedCoeff m) _ q)) =
        modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := m) (G := G) C U hnm
          (MonoidAlgebra.of (ModNCompletedCoeff m) _ qU) := congrArg _ htransitionM
      _ = MonoidAlgebra.of (ModNCompletedCoeff n) _ qU :=
        modNCompletedGroupAlgebraStageCoeffMapInClass_of
          (n := n) (m := m) (G := G) C U hnm qU
      _ = modNCompletedGroupAlgebraTransitionInClass n G C hUV
          (MonoidAlgebra.of (ModNCompletedCoeff n) _ q) := htransitionN.symm
      _ = modNCompletedGroupAlgebraTransitionInClass n G C hUV
          (modNCompletedGroupAlgebraStageCoeffMapInClass
            (n := n) (m := m) (G := G) C V hnm
            (MonoidAlgebra.of (ModNCompletedCoeff m) _ q)) :=
        congrArg (modNCompletedGroupAlgebraTransitionInClass n G C hUV)
          (modNCompletedGroupAlgebraStageCoeffMapInClass_of
            (n := n) (m := m) (G := G) C V hnm q).symm
  · intro x y hx hy
    simp only [RingHom.map_add, hx, RingHom.coe_comp, Function.comp_apply, hy]
  · intro a x hx
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    simp only [map_intCast]

omit [Fact (0 < n)] [Fact (0 < m)] in
/--
A class-indexed stage coefficient map is surjective when the target modulus divides the source
modulus.
-/
theorem modNCompletedGroupAlgebraStageCoeffMapInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) (hnm : n ∣
        m) :
    Function.Surjective
      (modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := n) (m := m) (G := G) C U hnm) := by
  intro x
  induction x using MonoidAlgebra.induction with
  | zero =>
      exact ⟨0, map_zero _⟩
  | single_add q a x _ _ ih =>
      rcases ZMod.castHom_surjective hnm a with ⟨a', ha'⟩
      have ha'' : modNCompletedCoeffMap (n := n) (m := m) hnm a' = a := by
        simpa [modNCompletedCoeffMap] using ha'
      rcases ih with ⟨y, hy⟩
      refine
        ⟨(MonoidAlgebra.single q a' : ModNCompletedGroupAlgebraStageInClass m G C U) + y,
          ?_⟩
      rw [map_add, modNCompletedGroupAlgebraStageCoeffMapInClass_single_apply, hy, ha'']



end

end FoxDifferential
