/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Components
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMapCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.DivisorAbsoluteNorm

/-!
# Absolute norms on the standard adele-unit carriers

The finite valuation vector and archimedean unit projections define the same
prime-norm convention on the finite, infinite, and full standard carriers.
-/

@[expose] public section

open scoped NumberField NNReal
open NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The norm of a unit in a normed field, as a positive real unit. -/
def nnnormUnitHom (F : Type*) [NormedField F] :
    Fˣ →* ℝ≥0ˣ :=
  Units.map (nnNormHom : F →*₀ ℝ≥0).toMonoidHom

@[simp]
theorem nnnormUnitHom_val (F : Type*) [NormedField F] (x : Fˣ) :
    ((nnnormUnitHom F x : ℝ≥0ˣ) : ℝ≥0) = ‖(x : F)‖₊ :=
  rfl

namespace NumberField.InfiniteAdeleRing

/-- The product of the normalized norms of all archimedean components. -/
def absoluteNorm :
    (InfiniteAdeleRing K)ˣ →* ℝ≥0ˣ where
  toFun a := ∏ w : InfinitePlace K,
    nnnormUnitHom w.Completion (unitComponent w a) ^ w.mult
  map_one' := by
    apply Finset.prod_eq_one
    intro w _
    rw [map_one, map_one, one_pow]
  map_mul' a b := by
    simp only [map_mul, Finset.prod_mul_distrib, mul_pow]

@[simp]
theorem absoluteNorm_apply (a : (InfiniteAdeleRing K)ˣ) :
    absoluteNorm a =
      ∏ w : InfinitePlace K,
        nnnormUnitHom w.Completion (unitComponent w a) ^ w.mult :=
  rfl

end NumberField.InfiniteAdeleRing

namespace IsDedekindDomain.FiniteAdeleRing

/-- The finite absolute norm, obtained from the normalized valuation vector. -/
def absoluteNorm : (FiniteAdeleRing (𝓞 K) K)ˣ →* ℝ≥0ˣ :=
  (NumberField.divisorAbsoluteNorm (K := K)).comp (valuationVector (R := 𝓞 K) (K := K))

/-- The finite norm is the absolute norm of the associated fractional ideal. -/
theorem absoluteNorm_eq_fractionalIdealAbsoluteNorm (a : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    absoluteNorm a = NumberField.fractionalIdealAbsoluteNorm (fractionalIdeal a) :=
  (NumberField.fractionalIdealAbsoluteNorm_factorization (valuationVector a)).symm

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.IdeleGroup

/-- The absolute norm on the standard adele-unit carrier. Finite uniformizers
contribute their prime norms, and the archimedean factor occurs inversely. -/
def absoluteNorm : IdeleGroup (𝓞 K) K →* ℝ≥0ˣ :=
  MonoidHom.mk'
    (fun a => FiniteAdeleRing.absoluteNorm (finitePart a) *
      (InfiniteAdeleRing.absoluteNorm (infinitePart a))⁻¹)
    fun a b => by
      simp only [map_mul, mul_inv_rev]
      ac_rfl

/-- Evaluation by the canonical finite and archimedean projections. -/
theorem absoluteNorm_apply (a : IdeleGroup (𝓞 K) K) :
    absoluteNorm a = FiniteAdeleRing.absoluteNorm (finitePart a) *
      (InfiniteAdeleRing.absoluteNorm (infinitePart a))⁻¹ := rfl

/-- The actual kernel of the standard absolute norm. -/
def normOneSubgroup : Subgroup (IdeleGroup (𝓞 K) K) := (absoluteNorm (K := K)).ker

end NumberField.IdeleGroup
