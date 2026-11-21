/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Tactic.Push

/-! # Contraction of finite places in number-field towers -/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

universe u v w

variable {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- Contraction of a finite place of `L` to a finite place of `K`. -/
noncomputable def finitePlaceBelow
    (W : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum (𝓞 K) where
  asIdeal := W.asIdeal.under (𝓞 K)
  isPrime := inferInstance
  ne_bot :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := W.asIdeal.under (𝓞 K)) inferInstance
      (RingOfIntegers.not_isField K)

@[simp]
theorem finitePlaceBelow_asIdeal
    (W : HeightOneSpectrum (𝓞 L)) :
    (finitePlaceBelow (K := K) W).asIdeal =
      W.asIdeal.under (𝓞 K) :=
  rfl

/-- Contracting a finite place along the identity extension fixes it. -/
@[simp]
theorem finitePlaceBelow_self
    (W : HeightOneSpectrum (𝓞 K)) :
    finitePlaceBelow (K := K) W = W := by
  apply HeightOneSpectrum.ext
  change
    W.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K)) =
      W.asIdeal
  rw [Algebra.algebraMap_self, Ideal.comap_id]

section Tower

variable {M : Type w}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]

/-- Contraction of finite places is transitive in a tower of number
fields. -/
@[simp]
theorem finitePlaceBelow_finitePlaceBelow
    (W : HeightOneSpectrum (𝓞 L)) :
    finitePlaceBelow (K := K)
        (finitePlaceBelow (K := M) W) =
      finitePlaceBelow (K := K) W := by
  apply HeightOneSpectrum.ext
  exact
    Ideal.under_under
      (A := 𝓞 K) (B := 𝓞 M) (C := 𝓞 L) W.asIdeal

end Tower

/-- There are finitely many finite places of `L` above a fixed finite
place of `K`. -/
theorem finite_finitePlaceBelow_fibre
    (v : HeightOneSpectrum (𝓞 K)) :
    Set.Finite
      {W : HeightOneSpectrum (𝓞 L) |
        finitePlaceBelow (K := K) W = v} := by
  let : Module.Finite ℤ (𝓞 L) := Module.IsNoetherian.finite ℤ (𝓞 L)
  let : Module.Finite (𝓞 K) (𝓞 L) :=
    Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)
  apply Set.Finite.of_finite_image
  · apply
      (Algebra.QuasiFinite.finite_primesOver
        (R := 𝓞 K) (S := 𝓞 L) v.asIdeal).subset
    · rintro I ⟨W, hW, rfl⟩
      exact
        ⟨W.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hW).symm⟩⟩
  · intro W₁ _ W₂ _ h
    apply HeightOneSpectrum.ext
    exact h

/-- The inverse image of a finite set of base finite places under
contraction is finite. -/
theorem Set.Finite.preimage_finitePlaceBelow
    {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) :
    {W : HeightOneSpectrum (𝓞 L) |
      finitePlaceBelow (K := K) W ∈ S}.Finite := by
  change
    ((finitePlaceBelow (K := K)) ⁻¹' S).Finite
  exact hS.preimage'
    (fun v _ => finite_finitePlaceBelow_fibre
      (K := K) (L := L) v)

/-- Cofinite quantification over finite places of `L` is equivalent to
cofinite quantification over finite places of `K`, uniformly over every
place above the chosen base place. -/
theorem eventually_finitePlace_iff_eventually_all_above
    (P : ∀ _W : HeightOneSpectrum (𝓞 L), Prop) :
    (∀ᶠ W : HeightOneSpectrum (𝓞 L) in Filter.cofinite, P W) ↔
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
          P W.1 := by
  constructor
  · intro h
    have hbad :
        {W : HeightOneSpectrum (𝓞 L) | ¬ P W}.Finite :=
      Filter.eventually_cofinite.mp h
    have himage :
        (finitePlaceBelow (K := K) ''
          {W : HeightOneSpectrum (𝓞 L) | ¬ P W}).Finite :=
      hbad.image _
    apply Filter.eventually_cofinite.mpr
    apply himage.subset
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    rw [Set.mem_image]
    push Not at hw
    rcases hw with ⟨W, hW⟩
    exact ⟨W.1, hW, W.2⟩
  · intro h
    have htendsto :
        Filter.Tendsto
          (finitePlaceBelow (K := K))
          Filter.cofinite Filter.cofinite :=
      Filter.Tendsto.cofinite_of_finite_preimage_singleton
        (f := finitePlaceBelow (K := K) (L := L))
        (fun w => finite_finitePlaceBelow_fibre (K := K) (L := L) w)
    filter_upwards [htendsto.eventually h] with W hW
    exact hW ⟨W, rfl⟩
