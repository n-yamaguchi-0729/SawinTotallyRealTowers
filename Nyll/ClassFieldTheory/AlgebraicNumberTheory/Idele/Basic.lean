/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Components
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Ideles of a number field

Ideles are units in the adele ring. Their finite restricted-product
coordinates record the local units and the almost-everywhere integrality
condition.
-/

@[expose] public section

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

/-- The finite idele group attached to a Dedekind domain and its fraction
field.  The number-field definition below specializes this to the ring of
integers. -/
abbrev FiniteIdeleGroupOf
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F] :=
  Πʳ v : HeightOneSpectrum R,
    [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units]

/-- The group of finite ideles of a number field. -/
abbrev FiniteIdeleGroup :=
  FiniteIdeleGroupOf (𝓞 K) K

/-- The product of the multiplicative groups of the archimedean completions. -/
abbrev InfiniteIdeleGroup :=
  (NumberField.InfiniteAdeleRing K)ˣ

/-- The idele group `I_K`. -/
abbrev IdeleGroup :=
  NumberField.IdeleGroup (𝓞 K) K

namespace IdeleGroup

variable {K}

/-- The two restricted-product coordinates of an idele, as a multiplicative equivalence. -/
def componentsEquiv : IdeleGroup K ≃* (InfiniteIdeleGroup K × FiniteIdeleGroup K) :=
  MulEquiv.prodUnits.trans ((MulEquiv.refl _).prodCongr FiniteAdeleRing.unitComponentsEquiv)

/-- The archimedean unit part of an idele. -/
abbrev infinitePart : IdeleGroup K →* InfiniteIdeleGroup K :=
  NumberField.IdeleGroup.infinitePart

/-- A finite adele unit expressed as a restricted product of local units. -/
def finiteCoordinates : IdeleGroup K →* FiniteIdeleGroup K :=
  FiniteAdeleRing.unitComponentsEquiv.toMonoidHom.comp NumberField.IdeleGroup.finitePart

/-- Assemble an idele from its archimedean units and finite coordinates. -/
abbrev ofComponents (a : InfiniteIdeleGroup K) (b : FiniteIdeleGroup K) : IdeleGroup K :=
  componentsEquiv.symm (a, b)

@[simp]
theorem componentsEquiv_apply (a : IdeleGroup K) :
    componentsEquiv a = (infinitePart a, finiteCoordinates a) := rfl

@[simp]
theorem componentsEquiv_symm_apply (a : InfiniteIdeleGroup K × FiniteIdeleGroup K) :
    componentsEquiv.symm a = ofComponents a.1 a.2 := rfl

/-- Reading the archimedean part recovers the first argument of the idele constructor. -/
@[simp]
theorem infinitePart_ofComponents (a : InfiniteIdeleGroup K) (b : FiniteIdeleGroup K) :
    infinitePart (ofComponents a b) = a :=
  congrArg Prod.fst (componentsEquiv.apply_symm_apply (a, b))

/-- Reading the finite coordinates recovers the second argument of the idele constructor. -/
@[simp]
theorem finiteCoordinates_ofComponents (a : InfiniteIdeleGroup K) (b : FiniteIdeleGroup K) :
    finiteCoordinates (ofComponents a b) = b :=
  congrArg Prod.snd (componentsEquiv.apply_symm_apply (a, b))

/-- The archimedean and finite parts determine an idele. -/
theorem ext_parts {a b : IdeleGroup K}
    (hInfinite : infinitePart a = infinitePart b)
    (hFinite : finiteCoordinates a = finiteCoordinates b) : a = b :=
  componentsEquiv.injective (Prod.ext hInfinite hFinite)

/-- Reassembling the two parts of an idele gives the original idele. -/
@[simp]
theorem ofComponents_parts (a : IdeleGroup K) :
    ofComponents (infinitePart a) (finiteCoordinates a) = a :=
  componentsEquiv.symm_apply_apply a

/-- The subgroup defined by independent restrictions on the two parts of an idele. -/
def partsSubgroup (I : Subgroup (InfiniteIdeleGroup K)) (F : Subgroup (FiniteIdeleGroup K)) :
    Subgroup (IdeleGroup K) :=
  I.comap infinitePart ⊓ F.comap finiteCoordinates

@[simp]
theorem mem_partsSubgroup (I : Subgroup (InfiniteIdeleGroup K)) (F : Subgroup (FiniteIdeleGroup K))
    (a : IdeleGroup K) : a ∈ partsSubgroup I F ↔ infinitePart a ∈ I ∧ finiteCoordinates a ∈ F :=
  Iff.rfl

@[simp]
theorem ofComponents_one : ofComponents (1 : InfiniteIdeleGroup K) 1 = 1 :=
  map_one componentsEquiv.symm

/-- An idele is the product of its pure archimedean and finite parts. -/
theorem eq_ofComponents_mul (a : IdeleGroup K) :
    a = ofComponents (infinitePart a) 1 * ofComponents 1 (finiteCoordinates a) :=
  ext_parts (by simp only [map_mul, infinitePart_ofComponents, mul_one])
    (by simp only [map_mul, finiteCoordinates_ofComponents, one_mul])

/-- Algebraically, the finite ideles over a Dedekind domain are the units of
its finite adele ring. -/
def finiteEquivFiniteAdeleUnitsOf
  (R : Type*) [CommRing R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F] :
    FiniteIdeleGroupOf R F ≃*
    (IsDedekindDomain.FiniteAdeleRing R F)ˣ :=
  (FiniteAdeleRing.unitComponentsEquiv (R := R) (K := F)).symm

/-- Algebraically, the finite ideles are the units of the finite adele ring.
The topology on the left is the restricted-product topology and is not
transported through this equivalence. -/
def finiteEquivFiniteAdeleUnits :
    FiniteIdeleGroup K ≃*
      (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ :=
  finiteEquivFiniteAdeleUnitsOf (𝓞 K) K

end IdeleGroup

namespace FiniteIdeleGroup

variable {K}

/-- Evaluation of a finite idele at a finite place. -/
def component (v : HeightOneSpectrum (𝓞 K)) :
    FiniteIdeleGroup K →* (v.adicCompletion K)ˣ :=
  (FiniteAdeleRing.unitComponent v).comp
    (IdeleGroup.finiteEquivFiniteAdeleUnits (K := K)).toMonoidHom

@[simp]
theorem component_apply (a : FiniteIdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    component v a = a v :=
  rfl

/-- A finite idele is a local integral unit at all but finitely many finite
places. -/
theorem eventually_mem_localUnits (a : FiniteIdeleGroup K) :
    ∀ᶠ v in Filter.cofinite,
      a v ∈ (v.adicCompletionIntegers K).units :=
  FiniteAdeleRing.eventually_unitComponent_mem
    (IdeleGroup.finiteEquivFiniteAdeleUnits (K := K) a)

end FiniteIdeleGroup

namespace InfiniteIdeleGroup

variable {K}

/-- The component of an infinite idele at an archimedean place. -/
def component (v : InfinitePlace K) :
    InfiniteIdeleGroup K →* v.Completionˣ :=
  NumberField.InfiniteAdeleRing.unitComponent v

omit [NumberField K] in
@[simp]
theorem component_apply (a : InfiniteIdeleGroup K) (v : InfinitePlace K) :
    component v a = ContinuousMulEquiv.piUnits a v :=
  rfl

end InfiniteIdeleGroup

namespace IdeleGroup

variable {K}

/-- The component of an idele at an archimedean place. -/
abbrev infiniteComponent (v : InfinitePlace K) :
    IdeleGroup K →* v.Completionˣ :=
  NumberField.IdeleGroup.infiniteComponent v

/-- The component of an idele at a finite place. -/
abbrev finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup K →* (v.adicCompletion K)ˣ :=
  NumberField.IdeleGroup.finiteComponent v

@[simp]
theorem infiniteComponent_apply (a : IdeleGroup K) (v : InfinitePlace K) :
    infiniteComponent v a = ContinuousMulEquiv.piUnits (infinitePart a) v :=
  rfl

@[simp]
theorem finiteComponent_apply (a : IdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    finiteComponent v a = finiteCoordinates a v :=
  rfl

end IdeleGroup
