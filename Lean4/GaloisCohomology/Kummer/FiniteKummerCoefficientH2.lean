import Mathlib.FieldTheory.KummerExtension
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

set_option autoImplicit false
/-!
# Finite Kummer coefficients in degree-two group cohomology

A primitive `p`-th root in the base field gives an equivariant additive map
from the trivial `ZMod p` coefficient group to the unit representation of a
finite extension.  This file constructs the resulting morphism of
`Int`-representations and its induced map on ordinary degree-two group
cohomology.

This is only the coefficient-change bridge.  It does not compare ordinary
group cohomology with the continuous lifted cup-product model, nor identify
the resulting unit class with a Hilbert symbol.
-/

open CategoryTheory

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable (p : ℕ+)

/-- The chosen primitive root, mapped to the extension field and regarded as
a unit. -/
noncomputable def finiteKummerCoefficientRootUnit
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) : Lˣ := by
  let zeta : K := hmu.choose
  let hzeta : IsPrimitiveRoot zeta (p : ℕ) :=
    (mem_primitiveRoots p.pos).mp hmu.choose_spec
  let hzetaL : IsPrimitiveRoot (algebraMap K L zeta) (p : ℕ) :=
    hzeta.map_of_injective (algebraMap K L).injective
  exact (hzetaL.isUnit p.ne_zero).unit'

@[simp]
theorem finiteKummerCoefficientRootUnit_val
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) :
    ((finiteKummerCoefficientRootUnit K L p hmu : Lˣ) : L) =
      algebraMap K L hmu.choose :=
  rfl

theorem finiteKummerCoefficientRootUnit_isPrimitiveRoot
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) :
    IsPrimitiveRoot (finiteKummerCoefficientRootUnit K L p hmu) (p : ℕ) := by
  let hzeta : IsPrimitiveRoot hmu.choose (p : ℕ) :=
    (mem_primitiveRoots p.pos).mp hmu.choose_spec
  exact (hzeta.map_of_injective (algebraMap K L).injective).isUnit_unit' p.ne_zero

/-- Additive `ZMod p` mapped to the powers of the chosen primitive root in
the extension's unit group. -/
noncomputable def finiteKummerCoefficientAddHom
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) :
    ULift (ZMod (p : ℕ)) →+ Additive Lˣ := by
  let u := finiteKummerCoefficientRootUnit K L p hmu
  let hu : IsPrimitiveRoot u (p : ℕ) :=
    finiteKummerCoefficientRootUnit_isPrimitiveRoot K L p hmu
  exact ((Subgroup.subtype (Subgroup.zpowers u)).toAdditive.comp
    hu.zmodEquivZPowers.toAddMonoidHom).comp AddEquiv.ulift.toAddMonoidHom

@[simp]
theorem finiteKummerCoefficientAddHom_intCast
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) (i : ℤ) :
    finiteKummerCoefficientAddHom K L p hmu
        (ULift.up (i : ZMod (p : ℕ))) =
      Additive.ofMul (finiteKummerCoefficientRootUnit K L p hmu ^ i) := by
  let u := finiteKummerCoefficientRootUnit K L p hmu
  let hu : IsPrimitiveRoot u (p : ℕ) :=
    finiteKummerCoefficientRootUnit_isPrimitiveRoot K L p hmu
  change Additive.ofMul
      ((hu.zmodEquivZPowers (i : ZMod (p : ℕ))).toMul : Lˣ) =
    Additive.ofMul (u ^ i)
  rw [hu.zmodEquivZPowers_apply_coe_int]
  rfl

/-- Every finite Kummer coefficient is killed by the exponent of its root of unity. -/
theorem finiteKummerCoefficientAddHom_pow_eq_one
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (z : ULift (ZMod (p : ℕ))) :
    (finiteKummerCoefficientAddHom K L p hmu z).toMul ^ (p : ℕ) = 1 := by
  rcases z with ⟨z⟩
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective z
  rw [finiteKummerCoefficientAddHom_intCast]
  let u := finiteKummerCoefficientRootUnit K L p hmu
  change (u ^ i) ^ (p : ℕ) = 1
  calc
    (u ^ i) ^ (p : ℕ) = (u ^ (p : ℕ)) ^ i := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    _ = 1 := by
      rw [(finiteKummerCoefficientRootUnit_isPrimitiveRoot K L p hmu).pow_eq_one,
        one_zpow]

/-- The chosen root coefficient is fixed by every automorphism over the
base field. -/
theorem finiteKummerCoefficientAddHom_fixed
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (sigma : Gal(L / K)) (z : ULift (ZMod (p : ℕ))) :
    (Rep.ofAlgebraAutOnUnits K L).ρ sigma
        (finiteKummerCoefficientAddHom K L p hmu z) =
      finiteKummerCoefficientAddHom K L p hmu z := by
  rcases z with ⟨z⟩
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective z
  rw [finiteKummerCoefficientAddHom_intCast]
  change Additive.ofMul
      (sigma • (finiteKummerCoefficientRootUnit K L p hmu ^ i)) =
    Additive.ofMul (finiteKummerCoefficientRootUnit K L p hmu ^ i)
  apply congrArg Additive.ofMul
  rw [AlgEquiv.smul_units_def, map_zpow]
  congr 1
  apply Units.ext
  simp only [Units.coe_map]
  rw [finiteKummerCoefficientRootUnit_val]
  exact sigma.commutes hmu.choose

/-- The primitive-root inclusion as a morphism from the trivial `Int`-linear
`ZMod p` representation to the extension-unit representation. -/
noncomputable def finiteKummerCoefficientRepHom
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) :
    Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ))) ⟶
      Rep.ofAlgebraAutOnUnits K L := by
  apply Rep.ofHom
  refine ⟨(finiteKummerCoefficientAddHom K L p hmu).toIntLinearMap, ?_⟩
  intro sigma
  apply LinearMap.ext
  intro z
  change finiteKummerCoefficientAddHom K L p hmu z =
    (Rep.ofAlgebraAutOnUnits K L).ρ sigma
      (finiteKummerCoefficientAddHom K L p hmu z)
  exact (finiteKummerCoefficientAddHom_fixed K L p hmu sigma z).symm

/-- Change coefficients from trivial mod-`p` coefficients to extension units
in ordinary degree-two group cohomology. -/
noncomputable def finiteKummerCoefficientH2Map
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) :
    groupCohomology
        (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 :=
  groupCohomology.map (MonoidHom.id (Gal(L / K)))
    (finiteKummerCoefficientRepHom K L p hmu) 2

/-- On an inhomogeneous cocycle representative, coefficient change applies
the chosen-root homomorphism pointwise. -/
theorem finiteKummerCoefficientCocyclesMap_apply
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (z : groupCohomology.cocycles
      (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) 2)
    (x : Fin 2 → Gal(L / K)) :
    groupCohomology.iCocycles (Rep.ofAlgebraAutOnUnits K L) 2
        (groupCohomology.cocyclesMap (MonoidHom.id (Gal(L / K)))
          (finiteKummerCoefficientRepHom K L p hmu) 2 z) x =
      finiteKummerCoefficientAddHom K L p hmu
        (groupCohomology.iCocycles
          (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) 2 z x) := by
  rw [← ConcreteCategory.comp_apply,
    HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  rfl

/-- Naturality of the quotient map for the finite Kummer coefficient
change. -/
theorem finiteKummerCoefficientH2Map_quotient
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (z : groupCohomology.cocycles
      (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) 2) :
    finiteKummerCoefficientH2Map K L p hmu
        (groupCohomology.π
          (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) 2 z) =
      groupCohomology.π (Rep.ofAlgebraAutOnUnits K L) 2
        (groupCohomology.cocyclesMap (MonoidHom.id (Gal(L / K)))
          (finiteKummerCoefficientRepHom K L p hmu) 2 z) := by
  change
    (groupCohomology.π
        (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) 2 ≫
      groupCohomology.map (MonoidHom.id (Gal(L / K)))
        (finiteKummerCoefficientRepHom K L p hmu) 2) z = _
  rw [groupCohomology.π_map]
  rfl

end ClassFieldTower.Martinet.Shafarevich
