import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.InClass.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic

set_option autoImplicit false

/-!
# Fox differential: completed — coefficient rings — mod-\(n\) completed group algebra — coeff map

The principal declarations in this module are:

- `modNCompletedCoeffMap`
  The coefficient reduction map \(\mathbb{Z}/m\mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}\) attached to a
  divisibility relation \(n \mid m\).
- `modNCompletedGroupRingCoeffMap`
  The coefficient reduction map on one residue-coefficient group ring.
- `modNCompletedCoeffMap_rfl`
  Coefficient reduction along reflexive divisibility is the identity map.
- `modNCompletedCoeffMap_comp`
  Coefficient change is performed stagewise: supports are unchanged and coefficients are transported
  by the given ring homomorphism.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {n m k : ℕ}
variable [Fact (0 < n)] [Fact (0 < m)] [Fact (0 < k)]

omit [Fact (0 < n)] [Fact (0 < m)] in
/--
The coefficient reduction map \(\mathbb{Z}/m\mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}\) attached to
a divisibility relation \(n \mid m\).
-/
def modNCompletedCoeffMap (hnm : n ∣ m) :
    ModNCompletedCoeff m →+* ModNCompletedCoeff n :=
  ZMod.castHom hnm (ModNCompletedCoeff n)

omit [Fact (0 < n)] in
/-- Coefficient reduction along reflexive divisibility is the identity map. -/
@[simp]
theorem modNCompletedCoeffMap_rfl :
    modNCompletedCoeffMap (n := n) (m := n) dvd_rfl = RingHom.id _ := by
  ext x
  rcases ZMod.intCast_surjective x with ⟨t, rfl⟩
  simp only [modNCompletedCoeffMap, ZMod.castHom_self, map_intCast]

omit [Fact (0 < n)] [Fact (0 < m)] [Fact (0 < k)] in
/--
Coefficient change is performed stagewise: supports are unchanged and coefficients are
transported by the given ring homomorphism.
-/
@[simp]
theorem modNCompletedCoeffMap_comp (hnm : n ∣ m) (hmk : m ∣ k) :
    (modNCompletedCoeffMap (n := n) (m := m) hnm).comp
        (modNCompletedCoeffMap (n := m) (m := k) hmk) =
      modNCompletedCoeffMap (n := n) (m := k) (dvd_trans hnm hmk) := by
  ext x
  rcases ZMod.intCast_surjective x with ⟨t, rfl⟩
  simp only [modNCompletedCoeffMap, ZMod.castHom_comp, map_intCast]

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- The coefficient reduction map on one residue-coefficient group ring. -/
def modNCompletedGroupRingCoeffMap (H : Type*) [Monoid H] (hnm : n ∣ m) :
    ModNCompletedGroupRing m H →+* ModNCompletedGroupRing n H := by
  letI : Algebra (ModNCompletedCoeff m) (ModNCompletedCoeff n) :=
    ZMod.algebra' (R := ModNCompletedCoeff n) (m := n) (n := m) hnm
  letI : Algebra (ModNCompletedCoeff m) (ModNCompletedGroupRing n H) := inferInstance
  exact
    (MonoidAlgebra.lift (ModNCompletedCoeff m) (ModNCompletedGroupRing n H) H
      (MonoidAlgebra.of (ModNCompletedCoeff n) H)).toRingHom

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- Evaluation of coefficient reduction on a group-like basis element. -/
@[simp]
theorem modNCompletedGroupRingCoeffMap_of
    (H : Type*) [Monoid H] (hnm : n ∣ m) (h : H) :
    modNCompletedGroupRingCoeffMap (n := n) (m := m) H hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m) H h) =
      MonoidAlgebra.of (ModNCompletedCoeff n) H h := by
  let : Algebra (ModNCompletedCoeff m) (ModNCompletedCoeff n) :=
    ZMod.algebra' (R := ModNCompletedCoeff n) (m := n) (n := m) hnm
  let : Algebra (ModNCompletedCoeff m) (ModNCompletedGroupRing n H) := inferInstance
  change
    MonoidAlgebra.lift (ModNCompletedCoeff m) (ModNCompletedGroupRing n H) H
        (MonoidAlgebra.of (ModNCompletedCoeff n) H)
        (MonoidAlgebra.of (ModNCompletedCoeff m) H h) =
      MonoidAlgebra.of (ModNCompletedCoeff n) H h
  exact MonoidAlgebra.lift_of
    (R := ModNCompletedCoeff m) (A := ModNCompletedGroupRing n H)
    (M := H) (MonoidAlgebra.of (ModNCompletedCoeff n) H) h

end

end FoxDifferential
