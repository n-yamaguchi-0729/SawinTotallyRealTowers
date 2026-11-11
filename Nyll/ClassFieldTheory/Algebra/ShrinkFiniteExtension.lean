/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.RingTheory.Finiteness.Basic
public import Nyll.ClassFieldTheory.Algebra.AbelianGaloisEquiv

/-!
# Compatible small representatives of finite field extensions

The algebra, finite-dimensional and Galois structures use the same two `Shrink` equivalences.
These existing suppliers are independent of ramification and reciprocity. Their original names
and bodies are retained so every consumer uses exactly the same transported structures.
-/

@[expose] public section

noncomputable section

namespace HasseArf

/-! ## Compatible small representatives of finite extensions -/

/-- The algebra structure on the two small representatives, transported from
the original field extension. -/
@[instance_reducible]
noncomputable def shrinkAlgebra
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    Algebra (Shrink.{0} K) (Shrink.{0} L) :=
  ((Shrink.ringEquiv L).symm.toRingHom.comp
    ((algebraMap K L).comp (Shrink.ringEquiv K).toRingHom)).toAlgebra

/-- The two `Shrink` equivalences commute with the algebra maps. -/
theorem shrinkAlgebra_commutes
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    let : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    (algebraMap (Shrink.{0} K) (Shrink.{0} L)).comp
      (Shrink.ringEquiv K).symm.toRingHom =
        (Shrink.ringEquiv L).symm.toRingHom.comp (algebraMap K L) := by
  intro reusedStructure1
  exact by
    apply RingHom.ext
    intro x
    change (Shrink.ringEquiv L).symm
      (algebraMap K L (Shrink.ringEquiv K ((Shrink.ringEquiv K).symm x))) =
        (Shrink.ringEquiv L).symm (algebraMap K L x)
    rw [RingEquiv.apply_symm_apply]

/-- Finite-dimensionality survives simultaneous shrinking of the base and
extension fields. -/
theorem shrink_finiteDimensional
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Small.{0} K] [Small.{0} L] :
    let : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) := by
  intro reusedStructure1
  exact Module.Finite.of_equiv_equiv
    (Shrink.ringEquiv K).symm (Shrink.ringEquiv L).symm
    (shrinkAlgebra_commutes K L)

/-- Abelian Galois structure survives simultaneous shrinking of both fields. -/
theorem shrink_isAbelianGalois
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [IsAbelianGalois K L] [Small.{0} K] [Small.{0} L] :
    let : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    IsAbelianGalois (Shrink.{0} K) (Shrink.{0} L) := by
  intro reusedStructure1
  exact ClassFieldTheory.isAbelianGalois_of_equiv_equiv
    (Shrink.ringEquiv K).symm (Shrink.ringEquiv L).symm
    (shrinkAlgebra_commutes K L)

/-- Galois automorphisms of a finite extension are identified with those of
its simultaneous small representatives. -/
noncomputable def shrinkGalEquiv
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    let : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    Gal(Shrink.{0} L / Shrink.{0} K) ≃ Gal(L/K) := by
  intro reusedStructure1
  exact ClassFieldTheory.galEquiv_of_equiv_equiv
    (Shrink.ringEquiv K).symm (Shrink.ringEquiv L).symm
    (shrinkAlgebra_commutes K L)

/-- The Galois equivalence acts by conjugating with the field equivalence. -/
theorem shrinkGalEquiv_apply
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    let : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    ∀ (σ : Gal(Shrink.{0} L / Shrink.{0} K)) (x : Shrink.{0} L),
      shrinkGalEquiv K L σ (Shrink.ringEquiv L x) =
        Shrink.ringEquiv L (σ x) := by
  intro reusedStructure1 σ x
  change Shrink.ringEquiv L
      (σ ((Shrink.ringEquiv L).symm (Shrink.ringEquiv L x))) =
    Shrink.ringEquiv L (σ x)
  rw [RingEquiv.symm_apply_apply]

/-- The same Galois conjugation respects multiplication of automorphisms. -/
noncomputable def shrinkGalMulEquiv
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    let : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    Gal(Shrink.{0} L / Shrink.{0} K) ≃* Gal(L/K) := by
  intro sharedAlgebra
  refine { shrinkGalEquiv K L with map_mul' := ?_ }
  intro σ τ
  ext x
  obtain ⟨y, rfl⟩ := (Shrink.ringEquiv L).surjective x
  change Shrink.ringEquiv L ((σ * τ) ((Shrink.ringEquiv L).symm
    (Shrink.ringEquiv L y))) = Shrink.ringEquiv L
      (σ ((Shrink.ringEquiv L).symm (Shrink.ringEquiv L
        (τ ((Shrink.ringEquiv L).symm (Shrink.ringEquiv L y))))))
  simp only [RingEquiv.symm_apply_apply, AlgEquiv.mul_apply]

/-- The shared small algebra embedding is the original embedding through the same equivalences. -/
theorem shrinkAlgebra_apply
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    let : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    ∀ x : Shrink.{0} K,
      Shrink.ringEquiv L (algebraMap (Shrink.{0} K) (Shrink.{0} L) x) =
        algebraMap K L (Shrink.ringEquiv K x) := by
  intro sharedAlgebra x
  change Shrink.ringEquiv L ((Shrink.ringEquiv L).symm
    (algebraMap K L (Shrink.ringEquiv K x))) = _
  exact (Shrink.ringEquiv L).apply_symm_apply _

/-- Simultaneously shrinking a tower preserves the actual three algebra embeddings. -/
theorem shrink_isScalarTower
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [Small.{0} K] [Small.{0} E] [Small.{0} L] :
    let : Algebra (Shrink.{0} K) (Shrink.{0} E) := shrinkAlgebra K E
    let : Algebra (Shrink.{0} E) (Shrink.{0} L) := shrinkAlgebra E L
    let : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    IsScalarTower (Shrink.{0} K) (Shrink.{0} E) (Shrink.{0} L) := by
  intro sharedKE sharedEL sharedKL
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  apply (Shrink.ringEquiv L).injective
  rw [RingHom.comp_apply, shrinkAlgebra_apply, shrinkAlgebra_apply, shrinkAlgebra_apply]
  exact IsScalarTower.algebraMap_apply K E L (Shrink.ringEquiv K x)

end HasseArf
