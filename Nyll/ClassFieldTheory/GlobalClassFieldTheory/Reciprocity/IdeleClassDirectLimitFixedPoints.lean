/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFixedDescent
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimit
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitAction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteLevelCore
public import Nyll.GaloisCohomology.Kummer.Abstract.KummerDelta
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.EmbeddingNorm
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup

/-!
# Fixed points of the rational idele-class direct limit

The actual idele class group of a finite rational intermediate field is
identified with the corresponding fixed subgroup of the direct limit.
-/



@[expose] public section

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance] ideleClassDirectLimitSMul

/-- The map from an intermediate idele class group to the direct limit
intertwines compatible finite and absolute Galois actions. -/
theorem rationalIntermediateIdeleClassToDirectLimit_conjugation
    (E : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ E]
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ : E ≃ₐ[ℚ] E)
    (hστ : ∀ x : E,
      ((τ x : E) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    σ • rationalIntermediateIdeleClassToDirectLimit E
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) c) =
      rationalIntermediateIdeleClassToDirectLimit E
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) (τ • c)) := by
  rw [relativeIdeleClassBaseChangeMulEquiv_smul_congr]
  exact intermediateIdeleClassToDirectLimit_conjugation ℚ E σ τ hστ
    (relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E) c)

/-- The canonical direct-limit realization of idèle classes is natural
under an equivalence between two finite rational intermediate fields
which is induced by an automorphism of the rational separable closure. -/
theorem rationalIntermediateIdeleClassToDirectLimit_ambientAlgEquiv
    {E F : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ F]
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (e : E ≃ₐ[ℚ] F)
    (hσe : ∀ x : E,
      ((e x : F) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (c : IdeleClassGroup E) :
    σ • rationalIntermediateIdeleClassToDirectLimit E c =
      rationalIntermediateIdeleClassToDirectLimit F
        (ideleClassCongr e c) :=
  intermediateIdeleClassToDirectLimit_ambientAlgEquiv ℚ σ e hσe c

/-- The image in the direct limit of an idele class over `K` is fixed by
the absolute Galois subgroup fixing `K`. -/
theorem rationalIntermediateIdeleClassToDirectLimit_fixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : IdeleClassGroup K)
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (hσ : σ ∈ K.fixingSubgroup) :
    σ • rationalIntermediateIdeleClassToDirectLimit K c =
      rationalIntermediateIdeleClassToDirectLimit K c :=
  intermediateIdeleClassToDirectLimit_fixed ℚ K σ hσ c

/-- Additive idele classes map into the fixed subgroup of the rational
idele-class representation. -/
theorem rationalIntermediateIdeleClassToDirectLimit_mem_fixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : Additive (IdeleClassGroup K)) :
    MonoidHom.toAdditive
        (rationalIntermediateIdeleClassToDirectLimit K) c ∈
      KummerTheory.ambientFixedAddSubgroup
        (ideleClassRepresentation ℚ)
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K) := by
  change
    (show (ideleClassRepresentation ℚ) from
      MonoidHom.toAdditive
        (rationalIntermediateIdeleClassToDirectLimit K) c) ∈
      KummerTheory.ambientFixedAddSubgroup
        (ideleClassRepresentation ℚ)
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
  rw [KummerTheory.mem_ambientFixedAddSubgroup_iff]
  intro σ
  change
    Additive.ofMul
        (σ.1 •
          rationalIntermediateIdeleClassToDirectLimit K
            (Additive.toMul c)) =
      Additive.ofMul
        (rationalIntermediateIdeleClassToDirectLimit K
          (Additive.toMul c))
  exact congrArg Additive.ofMul
    (rationalIntermediateIdeleClassToDirectLimit_fixed
      K (Additive.toMul c) σ.1 σ.2)

/-- The canonical additive homomorphism from the idele class group of a
finite rational intermediate field to the corresponding fixed subgroup. -/
noncomputable abbrev rationalIntermediateIdeleClassToFixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    Additive (IdeleClassGroup K) →+
      KummerTheory.ambientFixedAddSubgroup
        (ideleClassRepresentation ℚ)
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K) :=
  intermediateIdeleClassToFixed ℚ K

/-- The canonical map from a finite rational idele class group to the
corresponding fixed subgroup is injective. -/
theorem rationalIntermediateIdeleClassToFixed_injective
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    Function.Injective
      (rationalIntermediateIdeleClassToFixed K) :=
  intermediateIdeleClassToFixed_injective ℚ K

/-- The canonical map from a finite rational idele class group to the
corresponding fixed subgroup is surjective. -/
theorem rationalIntermediateIdeleClassToFixed_surjective
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    Function.Surjective
      (rationalIntermediateIdeleClassToFixed K) :=
  intermediateIdeleClassToFixed_surjective ℚ K

/-- The subgroup of the absolute idele-class direct limit fixed by the
absolute Galois group over a finite rational intermediate field is
exactly that field's actual idele class group. -/
noncomputable abbrev rationalIdeleClassEquivFixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    Additive (IdeleClassGroup K) ≃+
      KummerTheory.ambientFixedAddSubgroup
        (ideleClassRepresentation ℚ)
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K) :=
  ideleClassEquivFixed ℚ K

end Reciprocity
end GlobalClassFieldTheory
