/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.ExtensionRoundTrip
import Nyll.GaloisCohomology.Kummer.Concrete.InfiniteInverse

/-!
# Kummer subgroup-extension correspondence

For a fixed separable closure `Omega/K`, a positive integer `n`, and enough
`n`-th roots of unity in `K`, admissible subgroups of `Kˣ` correspond to
abelian Galois intermediate extensions whose Galois groups have exponent
dividing `n`.
-/

noncomputable section

namespace KummerTheory

variable {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]

/-- An extension-side object in the Kummer correspondence.

The structure stores only an intermediate field, its Galois and abelian
properties, and the exponent bound.  Radical generation and both round-trip
equalities are derived theorems. -/
structure KummerExtension (K Omega : Type*) [Field K] [Field Omega]
    [Algebra K Omega] (n : ℕ+) where
  /-- The intermediate field of `Omega/K` represented by this extension-side object. -/
  toIntermediateField : IntermediateField K Omega
  /-- The represented intermediate field is Galois over `K`. -/
  toIsGalois : IsGalois K toIntermediateField
  /-- The Galois group of the represented intermediate field is commutative. -/
  toIsMulCommutative : IsMulCommutative Gal(toIntermediateField/K)
  /-- Every Galois automorphism has order dividing `n`. -/
  exponent : ∀ sigma : Gal(toIntermediateField/K), sigma ^ (n : ℕ) = 1

namespace KummerExtension

variable {n : ℕ+}

/-- A Kummer extension supplies a Galois structure on its intermediate field. -/
instance (E : KummerExtension K Omega n) :
    IsGalois K E.toIntermediateField := E.toIsGalois

/-- The Galois group of a Kummer extension is commutative. -/
instance (E : KummerExtension K Omega n) :
    IsMulCommutative Gal(E.toIntermediateField/K) := E.toIsMulCommutative

/-- Extension-side objects are equal when their intermediate fields are
equal; the remaining fields are propositions. -/
@[ext]
theorem ext {E F : KummerExtension K Omega n}
    (h : E.toIntermediateField = F.toIntermediateField) : E = F := by
  cases E
  cases F
  cases h
  rfl

/-- The base-field radical subgroup attached to an extension-side object. -/
def toKummerSubgroup (E : KummerExtension K Omega n) : KummerSubgroup K n :=
  ⟨finiteKummerRadicalSubgroup
      (K := K) (L := E.toIntermediateField) n, by
    intro a ha
    obtain ⟨b, hb⟩ := (mem_unitNthPowersSubgroup_iff n).1 ha
    refine ⟨Units.map
      (algebraMap K E.toIntermediateField).toMonoidHom b, ?_⟩
    rw [← map_pow, hb]⟩

/-- The subgroup recovered from a Kummer extension has the extension's defining
radical as carrier. -/
@[simp]
theorem toKummerSubgroup_carrier (E : KummerExtension K Omega n) :
    (E.toKummerSubgroup).1 =
      finiteKummerRadicalSubgroup
        (K := K) (L := E.toIntermediateField) n :=
  rfl

end KummerExtension

variable [IsSepClosure K Omega]

/-- Construct the radical extension attached to an admissible Kummer
subgroup. -/
def kummerExtensionOfSubgroup
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n) : KummerExtension K Omega n where
  toIntermediateField :=
    kummerRadicalExtension (K := K) (Omega := Omega) n Delta.1
  toIsGalois := kummerRadicalExtension_isGalois n Delta.1
  toIsMulCommutative :=
    kummerRadicalExtension_isMulCommutative n hmu Delta.1
  exponent := kummerRadicalExtension_galois_pow_eq_one n hmu Delta.1

/-- The extension built from a Kummer subgroup has the expected intermediate field. -/
@[simp]
theorem kummerExtensionOfSubgroup_toIntermediateField
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n) :
    (kummerExtensionOfSubgroup
      (K := K) (Omega := Omega) n hmu Delta).toIntermediateField =
      kummerRadicalExtension (K := K) (Omega := Omega) n Delta.1 :=
  rfl

/-- Admissible Kummer subgroups are equivalent to abelian Galois
intermediate extensions whose Galois groups have exponent dividing `n`. -/
def kummerSubgroupEquivKummerExtension
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    KummerSubgroup K n ≃ KummerExtension K Omega n where
  toFun := kummerExtensionOfSubgroup n hmu
  invFun := KummerExtension.toKummerSubgroup
  left_inv Delta := by
    apply Subtype.ext
    exact finiteKummerRadicalSubgroup_kummerRadicalExtension_eq
      (K := K) (Omega := Omega) n hn hmu Delta
  right_inv E := by
    apply KummerExtension.ext
    exact kummerRadicalExtension_finiteKummerRadicalSubgroup_eq
      E.toIntermediateField n hmu E.exponent

/-- The Kummer correspondence sends a subgroup to the intermediate field it generates. -/
@[simp]
theorem kummerSubgroupEquivKummerExtension_apply_toIntermediateField
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n) :
    ((kummerSubgroupEquivKummerExtension
      (K := K) (Omega := Omega) n hn hmu) Delta).toIntermediateField =
      kummerRadicalExtension (K := K) (Omega := Omega) n Delta.1 :=
  rfl

/-- The inverse Kummer correspondence recovers the radical subgroup carrier. -/
@[simp]
theorem kummerSubgroupEquivKummerExtension_symm_apply_carrier
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (E : KummerExtension K Omega n) :
    ((kummerSubgroupEquivKummerExtension
      (K := K) (Omega := Omega) n hn hmu).symm E).1 =
      finiteKummerRadicalSubgroup
        (K := K) (L := E.toIntermediateField) n :=
  rfl

end KummerTheory
