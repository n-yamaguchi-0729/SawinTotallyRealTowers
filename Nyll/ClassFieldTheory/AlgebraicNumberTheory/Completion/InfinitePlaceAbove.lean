/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.AbsoluteValueConjugacy
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
public import Nyll.ValuedFieldTheory.Valuation.Completion.ExtensionFactorClassification

/-!
# Infinite places above a finite extension
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Restriction of an infinite place of `L` to the base field. -/
def infinitePlaceBelow
    (W : InfinitePlace L) : InfinitePlace K :=
  W.comap (algebraMap K L)

omit [NumberField K] in
/-- Restricting an infinite place along the identity extension fixes it. -/
@[simp]
theorem infinitePlaceBelow_self
    (W : InfinitePlace K) :
    infinitePlaceBelow (K := K) W = W := by
  rw [infinitePlaceBelow,
    Algebra.algebraMap_self, InfinitePlace.comap_id]

section InfinitePlaceTower

variable {M : Type*}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]

omit [NumberField K] [NumberField L] [NumberField M]
    [FiniteDimensional K L] in
/-- Restriction of infinite places is transitive in a tower of number
fields. -/
@[simp]
theorem infinitePlaceBelow_infinitePlaceBelow
    (W : InfinitePlace L) :
    infinitePlaceBelow (K := K)
        (infinitePlaceBelow (K := M) W) =
      infinitePlaceBelow (K := K) W := by
  rw [infinitePlaceBelow, infinitePlaceBelow, infinitePlaceBelow,
    ← InfinitePlace.comap_comp,
    IsScalarTower.algebraMap_eq K M L]

end InfinitePlaceTower

omit [NumberField K] in
/-- The map on infinite-place completions induced by the identity field
extension is the identity map. -/
@[simp]
theorem infinitePlaceCompletionMap_self_apply
    (W : InfinitePlace K)
    (x : W.Completion) :
    let : W.1.LiesOver W.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1)
        (infinitePlaceBelow_self (K := K) W)⟩
    AbsoluteValue.Completion.map W.1 W.1 x = x := by
  intro sharedOwner1
  refine AbsoluteValue.Completion.induction_on x ?_ ?_
  · exact isClosed_eq (AbsoluteValue.Completion.continuous_map W.1 W.1) continuous_id
  · intro y
    rw [AbsoluteValue.Completion.map_coe W.1 W.1]
    apply congrArg (fun z : WithAbs W.1 => (z : W.Completion))
    apply (WithAbs.equiv W.1).injective
    change algebraMap K K (WithAbs.equiv W.1 y) = WithAbs.equiv W.1 y
    exact Algebra.algebraMap_self_apply _

/-- Completion maps at infinite places compose in a tower of number
fields. -/
theorem infinitePlaceCompletionMap_comp_apply
    {M : Type*}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]
    (W : InfinitePlace L)
    (x :
      (infinitePlaceBelow
        (K := K) W).Completion) :
    let V :=
      infinitePlaceBelow (K := M) W
    let v :=
      infinitePlaceBelow (K := K) W
    let : V.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1)
        (infinitePlaceBelow_infinitePlaceBelow
          (K := K) (M := M) (L := L) W)⟩
    let : W.1.LiesOver V.1 := ⟨rfl⟩
    let : W.1.LiesOver v.1 := ⟨rfl⟩
    AbsoluteValue.Completion.map V.1 W.1
        (AbsoluteValue.Completion.map v.1 V.1 x) =
      AbsoluteValue.Completion.map v.1 W.1 x := by
  intro V v reusedStructure3 reusedStructure4 reusedStructure5
  exact AbsoluteValue.Completion.map_map v.1 V.1 W.1 x

/-- An infinite place above `w`, regarded as an exact extension of the
underlying absolute value. -/
def infinitePlaceAboveToExtension
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w}) :
    AbsoluteValueExtension w.1 L := by
  refine ⟨W.1.1, ?_⟩
  intro x
  have h :=
    congrArg (fun v : InfinitePlace K => v x) W.2
  exact h

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- For a finite Galois extension, every extension of an infinite-place
absolute value is represented by an infinite place above the base
place. -/
theorem
    infinitePlaceAboveToExtension_surjective_of_isGalois
    [IsGalois K L]
    (w : InfinitePlace K) :
    Function.Surjective
      (infinitePlaceAboveToExtension
        (K := K) (L := L) w) := by
  intro u
  obtain ⟨W₀, hW₀⟩ :=
    InfinitePlace.comap_surjective
      (k := K) (K := L) w
  let W₀' :
      {W : InfinitePlace L //
        infinitePlaceBelow (K := K) W = w} :=
    ⟨W₀, hW₀⟩
  let u₀ : AbsoluteValueExtension w.1 L :=
    infinitePlaceAboveToExtension
      (K := K) (L := L) w W₀'
  obtain ⟨σ, hσ⟩ :=
    absoluteValueConjugacy w.1 w.isNontrivial u₀ u
  let Wσ : InfinitePlace L :=
    W₀.comap σ.toRingEquiv.toRingHom
  have hWσ :
      infinitePlaceBelow (K := K) Wσ = w := by
    apply InfinitePlace.ext
    intro x
    change W₀ (σ (algebraMap K L x)) = w x
    rw [σ.commutes]
    exact congrArg (fun v : InfinitePlace K => v x) hW₀
  refine ⟨⟨Wσ, hWσ⟩, ?_⟩
  rw [hσ]
  apply Subtype.ext
  rfl

/-- Infinite places of `L` above `w` are exactly the exact extensions of
the absolute value represented by `w`. -/
noncomputable def infinitePlaceAboveEquivExtension
    (w : InfinitePlace K) :
    {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w} ≃
      AbsoluteValueExtension w.1 L := by
  apply Equiv.ofBijective
    (infinitePlaceAboveToExtension
      (K := K) (L := L) w)
  constructor
  · intro W W' h
    have habs : W.1.1 = W'.1.1 :=
      congrArg
        (fun u : AbsoluteValueExtension w.1 L => u.1) h
    apply Subtype.ext
    apply Subtype.ext
    exact habs
  · intro u
    let M := finiteNormalClosure K L
    let e : L →ₐ[K] M :=
      finiteNormalClosureEmbedding K L
    let : Algebra L M :=
      e.toRingHom.toAlgebra
    let : IsScalarTower K L M :=
      IsScalarTower.of_algebraMap_eq'
        e.comp_algebraMap.symm
    let : FiniteDimensional L M :=
      FiniteDimensional.right K L M
    let hu : u.1.IsNontrivial :=
      u.isNontrivial w.isNontrivial
    let uOverL : AbsoluteValueExtension u.1 M :=
      pullbackAbsoluteValueExtension
        u.1 hu IsAlgClosed.lift
    let uM : AbsoluteValueExtension w.1 M :=
      { val := uOverL.1
        property := by
          intro x
          rw [IsScalarTower.algebraMap_apply K L M,
            uOverL.2, u.2] }
    obtain ⟨WM, hWM⟩ :=
      infinitePlaceAboveToExtension_surjective_of_isGalois
        (K := K) (L := M) w uM
    let WL : InfinitePlace L :=
      WM.1.comap (algebraMap L M)
    have hWL :
        infinitePlaceBelow (K := K) WL = w := by
      apply InfinitePlace.ext
      intro x
      change
        WM.1
            (algebraMap L M
              (algebraMap K L x)) =
          w x
      rw [← IsScalarTower.algebraMap_apply K L M]
      exact congrArg (fun v : InfinitePlace K => v x) WM.2
    refine ⟨⟨WL, hWL⟩, ?_⟩
    apply Subtype.ext
    ext x
    have hWMval :
        WM.1.1 = uM.1 :=
      congrArg Subtype.val hWM
    change
      WM.1.1 (algebraMap L M x) = u.1 x
    rw [hWMval]
    exact uOverL.2 x

/-- The absolute value underlying the extension corresponding to an
infinite place above `w`. -/
@[simp]
theorem infinitePlaceAboveEquivExtension_apply_val
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w}) :
    (infinitePlaceAboveEquivExtension
      (K := K) (L := L) w W).1 = W.1.1 :=
  rfl
