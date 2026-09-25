/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FiniteCyclicLocalUnitsH2
import GaloisCohomology.Kummer.FiniteKummerCoefficientH2

set_option autoImplicit false
/-!
# Finite cyclic Kummer H² and the norm quotient

For a finite cyclic extension whose base contains a primitive `p`-th root,
the primitive-root coefficient morphism sends ordinary mod-`p` degree-two
cohomology to unit cohomology.  Finite-cyclic periodicity then places the
result in the field norm quotient.

No assertion is made here that a particular cup class maps to a prescribed
norm class or Hilbert symbol.
-/

open CategoryTheory

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]
variable (p : ℕ+)

/-- Ordinary mod-`p` degree-two cohomology mapped to the field norm
quotient through the primitive-root coefficient inclusion and the existing
finite-cyclic units comparison. -/
noncomputable def finiteCyclicKummerH2ToNormQuotient
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (g : Gal(L / K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g) :
    groupCohomology
        (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) 2 ⟶
      ModuleCat.of ℤ (Additive (LocalFieldTheory.NormQuotient K L)) :=
  finiteKummerCoefficientH2Map K L p hmu ≫
    (finiteCyclicUnitsH2IsoNormQuotient K L g hg).hom

/-- The norm-quotient map on a cocycle class is obtained by first applying
the chosen-root coefficient homomorphism pointwise. -/
theorem finiteCyclicKummerH2ToNormQuotient_quotient
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (g : Gal(L / K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g)
    (z : groupCohomology.cocycles
      (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) 2) :
    finiteCyclicKummerH2ToNormQuotient K L p hmu g hg
        (groupCohomology.π
          (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) 2 z) =
      (finiteCyclicUnitsH2IsoNormQuotient K L g hg).hom
        (groupCohomology.π (Rep.ofAlgebraAutOnUnits K L) 2
          (groupCohomology.cocyclesMap (MonoidHom.id (Gal(L / K)))
            (finiteKummerCoefficientRepHom K L p hmu) 2 z)) := by
  change (finiteCyclicUnitsH2IsoNormQuotient K L g hg).hom
      (finiteKummerCoefficientH2Map K L p hmu
        (groupCohomology.π
          (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) 2 z)) = _
  rw [finiteKummerCoefficientH2Map_quotient]

end ClassFieldTower.Martinet.Shafarevich
