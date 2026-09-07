import SawinTotallyRealTowers.QuadraticBasis
import SawinTotallyRealTowers.QuadraticIntegerRepresentation
import SawinTotallyRealTowers.QuadraticIntegralGenerator
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-!
# Integral bases of squarefree quadratic number fields

The square-root generator is integral. When its square is one modulo four,
its half-integer translate is integral as well. Integer-coordinate
classification gives spanning, and the concrete rational quadratic basis
gives linear independence. These produce actual bases of the full ring of
integers, with the two expected basis vectors.
-/

open scoped NumberField
open NumberField

universe u

namespace ClassFieldTower.Sawin

/-- The integral square-root generator as an element of the ring of integers. -/
def quadraticIntegerGenerator
    (L : Type u) [Field L] [NumberField L] (d : ℤ) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ)) : 𝓞 L :=
  ⟨α, isIntegral_int_of_sq_eq_int L d hSquare⟩

/-- Coercing the integral square-root generator recovers the original element. -/
theorem coe_quadraticIntegerGenerator
    (L : Type u) [Field L] [NumberField L] (d : ℤ) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ)) :
    (quadraticIntegerGenerator L d α hSquare : L) = α :=
  RingOfIntegers.coe_mk (isIntegral_int_of_sq_eq_int L d hSquare)

/-- The half-integer generator is integral when its square parameter is
one modulo four. -/
def quadraticHalfIntegerGenerator
    (L : Type u) [Field L] [NumberField L] (d : ℤ) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ)) (hMod : d % 4 = 1) : 𝓞 L :=
  ⟨(1 + α) / 2, by
    apply (mem_integralClosure_iff ℤ L).mpr
    have hDiv : (4 : ℤ) ∣ 1 ^ 2 - d * 1 ^ 2 := by
      apply Int.dvd_iff_emod_eq_zero.mpr
      simpa only [one_pow, mul_one] using (show (1 - d) % 4 = 0 by omega)
    simpa only [Int.cast_one, map_one, one_mul] using
      isIntegral_half_int_linear_combination_of_four_dvd L d 1 1 hSquare hDiv⟩

/-- Coercing the half-integer generator recovers its field expression. -/
theorem coe_quadraticHalfIntegerGenerator
    (L : Type u) [Field L] [NumberField L] (d : ℤ) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ)) (hMod : d % 4 = 1) :
    (quadraticHalfIntegerGenerator L d α hSquare hMod : L) = (1 + α) / 2 := by
  change (1 + α) / 2 = (1 + α) / 2
  rfl

/-- Replacing a primitive element by its half-integer translate preserves
its generated field over ℚ. -/
theorem adjoin_half_quadraticGenerator_eq_top
    (L : Type u) [Field L] [Algebra ℚ L] (α : L)
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) :
    IntermediateField.adjoin ℚ ({(1 + α) / 2} : Set L) = ⊤ := by
  let : CharZero L := Algebra.charZero_of_charZero ℚ L
  let E : IntermediateField ℚ L := IntermediateField.adjoin ℚ {(1 + α) / 2}
  apply top_unique
  rw [← hGenerate]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  have hxα : x = α := Set.mem_singleton_iff.mp hx
  subst x
  have hβ : (1 + α) / 2 ∈ E := IntermediateField.mem_adjoin_simple_self ℚ _
  have hRecover : 2 * ((1 + α) / 2) - 1 = α := by ring
  have hα : 2 * ((1 + α) / 2) - 1 ∈ E :=
    E.sub_mem (E.mul_mem (E.natCast_mem 2) hβ) E.one_mem
  rw [hRecover] at hα
  exact hα

private theorem linearIndependent_one_integer_generator
    (L : Type u) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (β : 𝓞 L)
    (hGenerate : IntermediateField.adjoin ℚ ({(β : L)} : Set L) = ⊤) :
    LinearIndependent ℤ ![(1 : 𝓞 L), β] := by
  have hBasis : (fun i : Fin 2 ↦ ((![1, β] i : 𝓞 L) : L)) =
      quadraticBasis L (β : L) hGenerate := by
    funext i
    fin_cases i
    · simp only [Fin.mk_zero, Matrix.cons_val_zero, quadraticBasis_apply_zero,
        RingOfIntegers.coe_eq_algebraMap, map_one]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        quadraticBasis_apply_one]
  have hQ : LinearIndependent ℚ
      (fun i : Fin 2 ↦ ((![1, β] i : 𝓞 L) : L)) := by
    rw [hBasis]
    exact (quadraticBasis L (β : L) hGenerate).linearIndependent
  apply LinearIndependent.of_comp
    (algebraMap (𝓞 L) L).toAddMonoidHom.toIntLinearMap
  exact hQ.restrict_scalars' ℤ

/-- The integral basis `1, α` when the signed squarefree radicand is not
one modulo four. -/
noncomputable def quadraticIntegerBasisOfModFourNeOne
    (L : Type u) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℤ) (hd : Squarefree d.natAbs) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤)
    (hMod : d % 4 ≠ 1) : Module.Basis (Fin 2) ℤ (𝓞 L) := by
  let β : 𝓞 L := quadraticIntegerGenerator L d α hSquare
  have hβ : (β : L) = α := coe_quadraticIntegerGenerator L d α hSquare
  have hLI : LinearIndependent ℤ ![(1 : 𝓞 L), β] :=
    linearIndependent_one_integer_generator L β (by simpa only [hβ] using hGenerate)
  refine Module.Basis.mk hLI ?_
  intro x _
  obtain ⟨m, n, hx⟩ := exists_int_linear_combination_of_mod_four_ne_one
    L d hd α hSquare hGenerate hMod x
  have hxO : x = m • (1 : 𝓞 L) + n • β := by
    apply RingOfIntegers.ext
    simpa only [RingOfIntegers.coe_eq_algebraMap, zsmul_eq_mul,
      map_add, map_mul, map_intCast, mul_one, hβ] using hx
  rw [hxO]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ m (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ n (Submodule.subset_span ⟨1, rfl⟩))

/-- The first basis vector is one in the non-one-modulo-four case. -/
theorem quadraticIntegerBasisOfModFourNeOne_apply_zero
    (L : Type u) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℤ) (hd : Squarefree d.natAbs) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) (hMod : d % 4 ≠ 1) :
    quadraticIntegerBasisOfModFourNeOne L d hd α hSquare hGenerate hMod 0 = 1 := by
  simp only [quadraticIntegerBasisOfModFourNeOne, Module.Basis.mk_apply, Matrix.cons_val_zero]

/-- The second basis vector is the integral square-root generator. -/
theorem quadraticIntegerBasisOfModFourNeOne_apply_one
    (L : Type u) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℤ) (hd : Squarefree d.natAbs) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) (hMod : d % 4 ≠ 1) :
    quadraticIntegerBasisOfModFourNeOne L d hd α hSquare hGenerate hMod 1 =
      quadraticIntegerGenerator L d α hSquare := by
  simp only [quadraticIntegerBasisOfModFourNeOne, Module.Basis.mk_apply,
    Matrix.cons_val_one, Matrix.cons_val_zero]

/-- The integral basis `1, (1 + α) / 2` when the signed squarefree radicand
is one modulo four. -/
noncomputable def quadraticIntegerBasisOfModFourEqOne
    (L : Type u) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℤ) (hd : Squarefree d.natAbs) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤)
    (hMod : d % 4 = 1) : Module.Basis (Fin 2) ℤ (𝓞 L) := by
  let β : 𝓞 L := quadraticHalfIntegerGenerator L d α hSquare hMod
  have hβ : (β : L) = (1 + α) / 2 := coe_quadraticHalfIntegerGenerator L d α hSquare hMod
  have hLI : LinearIndependent ℤ ![(1 : 𝓞 L), β] :=
    linearIndependent_one_integer_generator L β (by
      simpa only [hβ] using adjoin_half_quadraticGenerator_eq_top L α hGenerate)
  refine Module.Basis.mk hLI ?_
  intro x _
  obtain ⟨m, n, hx⟩ := exists_int_linear_combination_of_half_quadraticGenerator
    L d hd α hSquare hGenerate x
  have hxO : x = m • (1 : 𝓞 L) + n • β := by
    apply RingOfIntegers.ext
    simpa only [RingOfIntegers.coe_eq_algebraMap, zsmul_eq_mul,
      map_add, map_mul, map_intCast, mul_one, hβ] using hx
  rw [hxO]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ m (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ n (Submodule.subset_span ⟨1, rfl⟩))

/-- The first basis vector is one in the one-modulo-four case. -/
theorem quadraticIntegerBasisOfModFourEqOne_apply_zero
    (L : Type u) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℤ) (hd : Squarefree d.natAbs) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) (hMod : d % 4 = 1) :
    quadraticIntegerBasisOfModFourEqOne L d hd α hSquare hGenerate hMod 0 = 1 := by
  simp only [quadraticIntegerBasisOfModFourEqOne, Module.Basis.mk_apply, Matrix.cons_val_zero]

/-- The second basis vector is the integral half-integer generator. -/
theorem quadraticIntegerBasisOfModFourEqOne_apply_one
    (L : Type u) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℤ) (hd : Squarefree d.natAbs) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) (hMod : d % 4 = 1) :
    quadraticIntegerBasisOfModFourEqOne L d hd α hSquare hGenerate hMod 1 =
      quadraticHalfIntegerGenerator L d α hSquare hMod := by
  simp only [quadraticIntegerBasisOfModFourEqOne, Module.Basis.mk_apply,
    Matrix.cons_val_one, Matrix.cons_val_zero]

end ClassFieldTower.Sawin
