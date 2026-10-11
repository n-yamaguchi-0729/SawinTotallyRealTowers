/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.FiniteDualSeparation

/-!
# Finite Galois-side Kummer duality

For a finite abelian Galois extension of exponent dividing `n`, the Kummer
pairing identifies the Galois group with the character group of the actual
radical quotient.
-/

noncomputable section

namespace KummerTheory

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The Galois group of a finite abelian Kummer extension is canonically
dual to its radical quotient. -/
def finiteKummerGaloisCharacterEquiv
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(L/K), sigma ^ (n : ℕ) = 1) :
    Gal(L/K) ≃*
      ((chosenFiniteKummerRadicalDatum (K := K) (L := L) n).RadicalQuotient →*
        nthRootsSubgroup L (n : ℕ)) := by
  let _ : CommGroup Gal(L/K) :=
    CommGroup.mk (fun a b => IsMulCommutative.is_comm.comm a b)
  let hbase : NthRootsOfUnityInBase (K := K) (L := L) n :=
    nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := L) n hmu
  exact transposeCharacterMulEquiv n hmu hexponent
    (finiteKummerCharacterEquiv (K := K) (L := L) n hbase)

/-- The forward map evaluates the Kummer character attached to a radical
class at the given Galois automorphism. -/
@[simp] theorem finiteKummerGaloisCharacterEquiv_apply
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(L/K), sigma ^ (n : ℕ) = 1)
    (sigma : Gal(L/K))
    (q : (chosenFiniteKummerRadicalDatum (K := K) (L := L) n).RadicalQuotient) :
    finiteKummerGaloisCharacterEquiv n hmu hexponent sigma q =
      finiteKummerCharacterEquiv n
        (nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := L) n hmu) q sigma :=
  by
    let _ : CommGroup Gal(L/K) :=
      CommGroup.mk (fun a b => IsMulCommutative.is_comm.comm a b)
    rfl

end KummerTheory
