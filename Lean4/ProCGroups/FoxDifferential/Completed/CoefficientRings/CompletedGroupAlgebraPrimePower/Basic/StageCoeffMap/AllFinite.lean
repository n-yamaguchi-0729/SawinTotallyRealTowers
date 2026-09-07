import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.System.CompletionMap

set_option autoImplicit false

/-!
# Fox differential: prime-power completed group algebra — basic — stage coeff map — all finite

The principal declarations in this module are:

- `modNCompletedGroupAlgebraStageCoeffMap`
  The coefficient reduction map on one finite quotient stage \(G/U\).
- `modNCompletedGroupAlgebraStageCoeffMap_of`
  The all-finite stage coefficient map sends a group-like basis element to the same support with its
  coefficient reduced modulo the target modulus.
- `modNCompletedGroupAlgebraStageCoeffMap_rfl`
  The all-finite stage coefficient map for reflexive divisibility is the identity ring homomorphism.
- `modNCompletedGroupAlgebraStageCoeffMap_comp`
  All-finite stage coefficient maps compose according to transitivity of modulus divisibility.
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
/-- The coefficient reduction map on one finite quotient stage \(G/U\). -/
abbrev modNCompletedGroupAlgebraStageCoeffMap
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (hnm : n ∣ m) :
    ModNCompletedGroupAlgebraStage m G U →+* ModNCompletedGroupAlgebraStage n G U :=
  modNCompletedGroupRingCoeffMap (n := n) (m := m)
      (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U) hnm

omit [Fact (0 < n)] [Fact (0 < m)] in
/--
The all-finite stage coefficient map sends a group-like basis element to the same support with its
coefficient reduced modulo the target modulus.
-/
@[simp]
theorem modNCompletedGroupAlgebraStageCoeffMap_of
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (hnm : n ∣ m)
    (q : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U) :
    modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m) _ q) =
      MonoidAlgebra.of (ModNCompletedCoeff n) _ q := by
  simpa [modNCompletedGroupAlgebraStageCoeffMap] using
    modNCompletedGroupRingCoeffMap_of (n := n) (m := m)
      (H := _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U) hnm q

omit [Fact (0 < n)] in
/--
The all-finite stage coefficient map for reflexive divisibility is the identity ring homomorphism.
-/
@[simp]
theorem modNCompletedGroupAlgebraStageCoeffMap_rfl
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := n) (G := G) U dvd_rfl =
      RingHom.id _ := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := n) (G := G) U dvd_rfl x = x)
    x ?_ ?_ ?_
  · intro q
    rw [modNCompletedGroupAlgebraStageCoeffMap_of]
  · intro x y hx hy
    rw [map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, hx]
    simp only [modNCompletedGroupAlgebraStageCoeffMap, modNCompletedGroupRingCoeffMap,
        AlgHom.toRingHom_eq_coe,
  map_intCast]

omit [Fact (0 < n)] [Fact (0 < m)] [Fact (0 < k)] in
/-- All-finite stage coefficient maps compose according to transitivity of modulus divisibility. -/
@[simp 900]
theorem modNCompletedGroupAlgebraStageCoeffMap_comp
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (hnm : n ∣ m) (hmk : m ∣ k) :
    (modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm).comp
        (modNCompletedGroupAlgebraStageCoeffMap (n := m) (m := k) (G := G) U hmk) =
      modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := k) (G := G) U
        (dvd_trans hnm hmk) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm).comp
          (modNCompletedGroupAlgebraStageCoeffMap (n := m) (m := k) (G := G) U hmk)) x =
        modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := k) (G := G) U
          (dvd_trans hnm hmk) x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, modNCompletedGroupAlgebraStageCoeffMap_of,
      modNCompletedGroupAlgebraStageCoeffMap_of, modNCompletedGroupAlgebraStageCoeffMap_of]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [modNCompletedGroupAlgebraStageCoeffMap, modNCompletedGroupRingCoeffMap,
        AlgHom.toRingHom_eq_coe,
  map_intCast, RingHom.coe_coe]

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- All-finite stage coefficient maps commute with finite-quotient transition maps. -/
@[simp 900]
theorem modNCompletedGroupAlgebraStageCoeffMap_compatible
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) (hnm : n ∣ m) :
    (modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm).comp
        (modNCompletedGroupAlgebraTransition m G hUV) =
      (modNCompletedGroupAlgebraTransition n G hUV).comp
        (modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) V hnm) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm).comp
          (modNCompletedGroupAlgebraTransition m G hUV)) x =
        ((modNCompletedGroupAlgebraTransition n G hUV).comp
          (modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) V hnm)) x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, RingHom.comp_apply, modNCompletedGroupAlgebraTransition_of]
    change modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m) _
          ((OpenNormalSubgroupInClass.map
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q)) =
      (modNCompletedGroupAlgebraTransition n G hUV)
        ((modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) V hnm)
          (MonoidAlgebra.of (ModNCompletedCoeff m) _ q))
    erw [modNCompletedGroupAlgebraStageCoeffMap_of]
    erw [modNCompletedGroupAlgebraStageCoeffMap_of]
    erw [modNCompletedGroupAlgebraTransition_of]
    rfl
  · intro x y hx hy
    simp only [RingHom.map_add, hx, RingHom.coe_comp, Function.comp_apply, hy]
  · intro a x hx
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    simp only [map_intCast]

omit [Fact (0 < n)] [Fact (0 < m)] in
/--
The all-finite stage coefficient map sends a singleton to the same support with its coefficient
reduced modulo the target modulus.
-/
theorem modNCompletedGroupAlgebraStageCoeffMap_single_apply
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (hnm : n ∣ m)
    (q : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)
    (a : ModNCompletedCoeff m) :
    modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single q (modNCompletedCoeffMap (n := n) (m := m) hnm a) := by
  let : Algebra (ModNCompletedCoeff m) (ModNCompletedCoeff n) :=
    ZMod.algebra' (R := ModNCompletedCoeff n) (m := n) (n := m) hnm
  have hcoeff :
      algebraMap (ModNCompletedCoeff m) (ModNCompletedCoeff n) a =
        modNCompletedCoeffMap (n := n) (m := m) hnm a := by
    rfl
  change
    MonoidAlgebra.lift (ModNCompletedCoeff m)
        (ModNCompletedGroupRing n
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U))
        (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U))
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single q (modNCompletedCoeffMap (n := n) (m := m) hnm a)
  rw [MonoidAlgebra.lift_single, MonoidAlgebra.of_apply,
    MonoidAlgebra.smul_single]
  change MonoidAlgebra.single q
      (algebraMap (ModNCompletedCoeff m) (ModNCompletedCoeff n) a * 1) =
    MonoidAlgebra.single q (modNCompletedCoeffMap (n := n) (m := m) hnm a)
  rw [hcoeff, mul_one]

omit [Fact (0 < n)] [Fact (0 < m)] in
/--
An all-finite stage coefficient map is surjective when the target modulus divides the source
modulus.
-/
theorem modNCompletedGroupAlgebraStageCoeffMap_surjective
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (hnm : n ∣ m) :
    Function.Surjective
      (modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm) := by
  intro x
  induction x using MonoidAlgebra.induction with
  | zero =>
      exact ⟨0, map_zero _⟩
  | single_add q a x _ _ ih =>
      rcases ZMod.castHom_surjective hnm a with ⟨a', ha'⟩
      have ha'' : modNCompletedCoeffMap (n := n) (m := m) hnm a' = a := by
        simpa [modNCompletedCoeffMap] using ha'
      rcases ih with ⟨y, hy⟩
      refine ⟨(MonoidAlgebra.single q a' : ModNCompletedGroupAlgebraStage m G U) + y, ?_⟩
      rw [map_add, modNCompletedGroupAlgebraStageCoeffMap_single_apply, hy, ha'']



end

end FoxDifferential
