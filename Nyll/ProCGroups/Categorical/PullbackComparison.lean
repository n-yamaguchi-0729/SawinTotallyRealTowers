/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Categorical.ProfinitePullbacks

/-!
# Pro C Groups / Categorical / Pullback Comparison

This module compares a profinite-tested continuous pullback square with its
concrete fiber product and transports bijectivity and kernel criteria across
the canonical comparison map.
-/

namespace ProCGroups.Categorical

universe u

section

open _root_.ProCGroups.ContinuousMonoidHom

variable {G H H₁ H₂ : Type u}
variable [Group G] [Group H] [Group H₁] [Group H₂]
variable [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
variable
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  [IsTopologicalGroup H₁] [IsTopologicalGroup H₂]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
variable [CompactSpace H₁] [T2Space H₁] [TotallyDisconnectedSpace H₁]
variable [CompactSpace H₂] [T2Space H₂] [TotallyDisconnectedSpace H₂]

/--
The canonical comparison map from a profinite-tested pullback square to the concrete continuous
fiber product.
-/
def toContinuousPullbackOfIsPullback
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) :
    G →ₜ* TopologicalFiberProduct.carrier β₁ β₂ :=
  TopologicalFiberProduct.lift β₁ β₂ α₁ α₂ (fun g => DFunLike.congr_fun hpb.1 g)

omit [IsTopologicalGroup H] [IsTopologicalGroup H₁] [IsTopologicalGroup H₂]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
  [CompactSpace H₁] [T2Space H₁] [TotallyDisconnectedSpace H₁]
  [CompactSpace H₂] [T2Space H₂] [TotallyDisconnectedSpace H₂] in
/--
The canonical comparison map from the concrete continuous fiber product to itself is the
identity.
-/
@[simp] theorem toContinuousPullbackOfIsPullback_self
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :
    toContinuousPullbackOfIsPullback (TopologicalFiberProduct.fst β₁ β₂)
        (TopologicalFiberProduct.snd β₁ β₂) β₁ β₂
        (TopologicalFiberProduct.hasProfiniteTestPullbackProperty β₁ β₂) =
      ContinuousMonoidHom.id (TopologicalFiberProduct.carrier β₁ β₂) := by
  change
    TopologicalFiberProduct.lift β₁ β₂ (TopologicalFiberProduct.fst β₁ β₂)
        (TopologicalFiberProduct.snd β₁ β₂)
        (fun g => DFunLike.congr_fun (TopologicalFiberProduct.hasProfiniteTestPullbackProperty
            β₁ β₂).1 g) =
      ContinuousMonoidHom.id (TopologicalFiberProduct.carrier β₁ β₂)
  exact pullbackLiftCont_eta (β₁ := β₁) (β₂ := β₂)
    (ψ := ContinuousMonoidHom.id (TopologicalFiberProduct.carrier β₁ β₂))

omit [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup H₁]
  [IsTopologicalGroup H₂]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
  [CompactSpace H₁] [T2Space H₁] [TotallyDisconnectedSpace H₁]
  [CompactSpace H₂] [T2Space H₂] [TotallyDisconnectedSpace H₂] in
/-- The first coordinate of the canonical comparison map recovers the first leg of the square. -/
@[simp] theorem TopologicalFiberProduct.fst_toContinuousPullbackOfIsPullback
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) :
    (TopologicalFiberProduct.fst β₁ β₂).comp (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb)
        = α₁ := by
  ext g
  rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup H₁]
  [IsTopologicalGroup H₂]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
  [CompactSpace H₁] [T2Space H₁] [TotallyDisconnectedSpace H₁]
  [CompactSpace H₂] [T2Space H₂] [TotallyDisconnectedSpace H₂] in
/-- The second coordinate of the canonical comparison map recovers the second leg of the square. -/
@[simp] theorem TopologicalFiberProduct.snd_toContinuousPullbackOfIsPullback
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) :
    (TopologicalFiberProduct.snd β₁ β₂).comp (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb)
        = α₂ := by
  ext g
  rfl

/--
The canonical inverse comparison map from the concrete continuous fiber product to a
profinite-tested pullback square.
-/
noncomputable def fromContinuousPullbackOfIsPullback
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) :
    TopologicalFiberProduct.carrier β₁ β₂ →ₜ* G :=
  pullbackDescCont hpb
    (TopologicalFiberProduct.fst β₁ β₂)
    (TopologicalFiberProduct.snd β₁ β₂)
    (TopologicalFiberProduct.hasProfiniteTestPullbackProperty β₁ β₂).1

omit [IsTopologicalGroup G] [IsTopologicalGroup H]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- Specification of the inverse comparison map from the concrete pullback. -/
theorem fromContinuousPullbackOfIsPullback_spec
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) :
    α₁.comp (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) =
        TopologicalFiberProduct.fst β₁ β₂ ∧
      α₂.comp (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) =
        TopologicalFiberProduct.snd β₁ β₂ := by
  change
    α₁.comp
        (pullbackDescCont hpb
          (TopologicalFiberProduct.fst β₁ β₂) (TopologicalFiberProduct.snd β₁ β₂)
          (TopologicalFiberProduct.hasProfiniteTestPullbackProperty β₁ β₂).1) =
      TopologicalFiberProduct.fst β₁ β₂ ∧
    α₂.comp
        (pullbackDescCont hpb
          (TopologicalFiberProduct.fst β₁ β₂) (TopologicalFiberProduct.snd β₁ β₂)
          (TopologicalFiberProduct.hasProfiniteTestPullbackProperty β₁ β₂).1) =
      TopologicalFiberProduct.snd β₁ β₂
  exact pullbackDescCont_spec hpb
    (TopologicalFiberProduct.fst β₁ β₂) (TopologicalFiberProduct.snd β₁ β₂)
    (TopologicalFiberProduct.hasProfiniteTestPullbackProperty β₁ β₂).1

omit [IsTopologicalGroup G] [IsTopologicalGroup H]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- Uniqueness of the inverse comparison map from the concrete pullback. -/
theorem fromContinuousPullbackOfIsPullback_uniq
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂)
    {ψ : TopologicalFiberProduct.carrier β₁ β₂ →ₜ* G}
    (hψ : α₁.comp ψ = TopologicalFiberProduct.fst β₁ β₂ ∧ α₂.comp ψ =
        TopologicalFiberProduct.snd β₁ β₂) :
    ψ = fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb := by
  simpa [fromContinuousPullbackOfIsPullback] using
    (pullbackDescCont_uniq hpb
      (TopologicalFiberProduct.fst β₁ β₂) (TopologicalFiberProduct.snd β₁ β₂)
      (TopologicalFiberProduct.hasProfiniteTestPullbackProperty β₁ β₂).1
      (ψ := ψ) hψ)

omit [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- Composing the inverse comparison map with the canonical map gives the identity. -/
theorem fromContinuousPullback_comp_toContinuousPullbackOfIsPullback
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) :
    (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).comp
        (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) =
      ContinuousMonoidHom.id G := by
  have hdesc :
      (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).comp
          (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) =
        pullbackDescCont hpb α₁ α₂ hpb.1 := by
    apply pullbackDescCont_uniq hpb α₁ α₂ hpb.1
    constructor
    · ext g
      calc
        α₁ ((fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).comp
            (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) g)
            = TopologicalFiberProduct.fst β₁ β₂
                (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb g) := by
                  simpa using congrArg
                    (fun f : TopologicalFiberProduct.carrier β₁ β₂ →ₜ* H₁ =>
                      f (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb g))
                    (fromContinuousPullbackOfIsPullback_spec α₁ α₂ β₁ β₂ hpb).1
        _ = α₁ g := by
              rfl
    · ext g
      calc
        α₂ ((fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).comp
            (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) g)
            = TopologicalFiberProduct.snd β₁ β₂
                (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb g) := by
                  simpa using congrArg
                    (fun f : TopologicalFiberProduct.carrier β₁ β₂ →ₜ* H₂ =>
                      f (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb g))
                    (fromContinuousPullbackOfIsPullback_spec α₁ α₂ β₁ β₂ hpb).2
        _ = α₂ g := by
              rfl
  have hself :
      pullbackDescCont hpb α₁ α₂ hpb.1 = ContinuousMonoidHom.id G := by
    symm
    exact pullbackDescCont_uniq hpb α₁ α₂ hpb.1
      (ψ := ContinuousMonoidHom.id G) (by
        constructor <;> ext g <;> rfl)
  exact hdesc.trans hself

omit [IsTopologicalGroup G] [IsTopologicalGroup H]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- Composing the canonical map with the inverse comparison map gives the identity. -/
theorem toContinuousPullback_comp_fromContinuousPullbackOfIsPullback
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) :
    (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).comp
        (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) =
      ContinuousMonoidHom.id (TopologicalFiberProduct.carrier β₁ β₂) := by
  apply TopologicalFiberProduct.hom_ext
  · intro x
    calc
      TopologicalFiberProduct.fst β₁ β₂
          ((toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).comp
            (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) x)
          = α₁ (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb x) := by
              rfl
      _ = TopologicalFiberProduct.fst β₁ β₂ x := by
            simpa using congrArg (fun f : TopologicalFiberProduct.carrier β₁ β₂ →ₜ* H₁ => f x)
              (fromContinuousPullbackOfIsPullback_spec α₁ α₂ β₁ β₂ hpb).1
  · intro x
    calc
      TopologicalFiberProduct.snd β₁ β₂
          ((toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).comp
            (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) x)
          = α₂ (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb x) := by
              rfl
      _ = TopologicalFiberProduct.snd β₁ β₂ x := by
            simpa using congrArg (fun f : TopologicalFiberProduct.carrier β₁ β₂ →ₜ* H₂ => f x)
              (fromContinuousPullbackOfIsPullback_spec α₁ α₂ β₁ β₂ hpb).2

omit [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- Pointwise left-inverse formula for the canonical comparison maps. -/
@[simp] theorem fromContinuousPullbackOfIsPullback_toContinuousPullbackOfIsPullback_apply
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) (g : G) :
    fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb
      (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb g) = g := by
  simpa using congrArg (fun f : G →ₜ* G => f g)
    (fromContinuousPullback_comp_toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb)

omit [IsTopologicalGroup G] [IsTopologicalGroup H]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- Pointwise right-inverse formula for the canonical comparison maps. -/
@[simp] theorem toContinuousPullbackOfIsPullback_fromContinuousPullbackOfIsPullback_apply
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) (x : TopologicalFiberProduct.carrier β₁
        β₂) :
    toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb
      (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb x) = x := by
  simpa using congrArg (fun f : TopologicalFiberProduct.carrier β₁ β₂ →ₜ*
      TopologicalFiberProduct.carrier β₁ β₂ => f x)
    (toContinuousPullback_comp_fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb)

omit [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- The canonical comparison map from a profinite-tested pullback square is bijective. -/
theorem bijective_toContinuousPullbackOfIsPullback
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) :
    Function.Bijective (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) := by
  have hleft :
      Function.LeftInverse
        (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb)
        (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) := by
    intro g
    exact fromContinuousPullbackOfIsPullback_toContinuousPullbackOfIsPullback_apply
      α₁ α₂ β₁ β₂ hpb g
  have hright :
      Function.RightInverse
        (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb)
        (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) := by
    intro x
    exact toContinuousPullbackOfIsPullback_fromContinuousPullbackOfIsPullback_apply
      α₁ α₂ β₁ β₂ hpb x
  exact ⟨hleft.injective, hright.surjective⟩


omit [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup H₁]
  [IsTopologicalGroup H₂]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
  [CompactSpace H₁] [T2Space H₁] [TotallyDisconnectedSpace H₁]
  [CompactSpace H₂] [T2Space H₂] [TotallyDisconnectedSpace H₂] in
/--
The canonical comparison map sends the chosen pullback descent map to the concrete continuous
pullback lift.
-/
@[simp 900] theorem toContinuousPullbackOfIsPullback_comp_pullbackDescCont
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂)
    (φ₁ : A →ₜ* H₁) (φ₂ : A →ₜ* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) :
    (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).comp
        (pullbackDescCont hpb φ₁ φ₂ hφ) =
      TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => DFunLike.congr_fun hφ a) := by
  apply TopologicalFiberProduct.hom_ext
  · intro a
    have hleft :
        (TopologicalFiberProduct.fst β₁ β₂).comp
            ((toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).comp
              (pullbackDescCont hpb φ₁ φ₂ hφ)) = φ₁ := by
      calc
        (TopologicalFiberProduct.fst β₁ β₂).comp
            ((toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).comp
              (pullbackDescCont hpb φ₁ φ₂ hφ)) =
            ((TopologicalFiberProduct.fst β₁ β₂).comp
              (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb)).comp
                (pullbackDescCont hpb φ₁ φ₂ hφ) := by
                  rfl
        _ = α₁.comp (pullbackDescCont hpb φ₁ φ₂ hφ) := by
              rw [TopologicalFiberProduct.fst_toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb]
        _ = φ₁ := pullbackDescCont_left hpb φ₁ φ₂ hφ
    have hright :
        (TopologicalFiberProduct.fst β₁ β₂).comp
            (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => DFunLike.congr_fun hφ a)) = φ₁ :=
      TopologicalFiberProduct.fst_lift β₁ β₂ φ₁ φ₂ (fun a => DFunLike.congr_fun hφ a)
    exact congrArg (fun f : A →ₜ* H₁ => f a) (hleft.trans hright.symm)
  · intro a
    have hleft :
        (TopologicalFiberProduct.snd β₁ β₂).comp
            ((toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).comp
              (pullbackDescCont hpb φ₁ φ₂ hφ)) = φ₂ := by
      calc
        (TopologicalFiberProduct.snd β₁ β₂).comp
            ((toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).comp
              (pullbackDescCont hpb φ₁ φ₂ hφ)) =
            ((TopologicalFiberProduct.snd β₁ β₂).comp
              (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb)).comp
                (pullbackDescCont hpb φ₁ φ₂ hφ) := by
                  rfl
        _ = α₂.comp (pullbackDescCont hpb φ₁ φ₂ hφ) := by
              rw [TopologicalFiberProduct.snd_toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb]
        _ = φ₂ := pullbackDescCont_right hpb φ₁ φ₂ hφ
    have hright :
        (TopologicalFiberProduct.snd β₁ β₂).comp
            (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => DFunLike.congr_fun hφ a)) = φ₂ :=
      TopologicalFiberProduct.snd_lift β₁ β₂ φ₁ φ₂ (fun a => DFunLike.congr_fun hφ a)
    exact congrArg (fun f : A →ₜ* H₂ => f a) (hleft.trans hright.symm)

omit [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- Surjective coordinate maps whose underlying composite kernel is the supremum of their kernels
induce a surjective descent map for a profinite-tested pullback square. -/
theorem surjective_pullbackDescCont_of_ker_eq
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂)
    (φ₁ : A →ₜ* H₁) (φ₂ : A →ₜ* H₂)
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂)
    (hker : (β₁.comp φ₁).toMonoidHom.ker = φ₁.toMonoidHom.ker ⊔ φ₂.toMonoidHom.ker) :
    Function.Surjective (pullbackDescCont hpb φ₁ φ₂ hcomp) := by
  have hbij : Function.Bijective (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) :=
    bijective_toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb
  have hsurjLift :
      Function.Surjective
        (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => DFunLike.congr_fun hcomp a)) :=
    surjective_pullbackLiftCont_of_ker_eq β₁ β₂ φ₁ φ₂ hφ₁ hφ₂ hcomp hker
  intro g
  let z : TopologicalFiberProduct.carrier β₁ β₂ := toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂
      hpb g
  rcases hsurjLift z with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply hbij.1
  calc
    toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb (pullbackDescCont hpb φ₁ φ₂ hcomp a)
        = TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hcomp k) a := by
            exact congrArg (fun f : A →ₜ* TopologicalFiberProduct.carrier β₁ β₂ => f a)
              (toContinuousPullbackOfIsPullback_comp_pullbackDescCont
                α₁ α₂ β₁ β₂ hpb φ₁ φ₂ hcomp)
    _ = z := ha
    _ = toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb g := rfl

/--
Any profinite-tested pullback square is canonically isomorphic to the concrete continuous fiber
product.
-/
noncomputable def pullbackContEquivOfIsPullback
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) :
    G ≃ₜ* TopologicalFiberProduct.carrier β₁ β₂ where
  toMulEquiv :=
    { toFun := toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb
      invFun := fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb
      left_inv := by
        intro g
        exact congrArg (fun f : G →ₜ* G => f g)
          (fromContinuousPullback_comp_toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb)
      right_inv := by
        intro x
        exact congrArg
          (fun f : TopologicalFiberProduct.carrier β₁ β₂ →ₜ* TopologicalFiberProduct.carrier β₁
              β₂ => f x)
          (toContinuousPullback_comp_fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb)
      map_mul' := by
        intro x y
        exact (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).map_mul x y }
  continuous_toFun := (toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).continuous_toFun
  continuous_invFun :=
    (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb).continuous_toFun

omit [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] in
/--
Forgetting continuity from the inverse of the canonical pullback equivalence recovers the
inverse comparison map.
-/
@[simp] theorem pullbackContEquivOfIsPullback_symm_toContinuousMonoidHom
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) :
    (ContinuousMonoidHom.toContinuousMonoidHom (pullbackContEquivOfIsPullback α₁ α₂ β₁ β₂
        hpb).symm) =
      fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb := by
  rfl


omit [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- The first coordinate of the canonical pullback equivalence recovers \(\alpha_1\). -/
@[simp] theorem pullbackContEquivOfIsPullback_fst
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) :
    (TopologicalFiberProduct.fst β₁ β₂).comp
        (ContinuousMonoidHom.toContinuousMonoidHom (pullbackContEquivOfIsPullback α₁ α₂ β₁ β₂
            hpb)) =
      α₁ := by
  rfl

omit [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- The second coordinate of the canonical pullback equivalence recovers \(\alpha_2\). -/
@[simp] theorem pullbackContEquivOfIsPullback_snd
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) :
    (TopologicalFiberProduct.snd β₁ β₂).comp
        (ContinuousMonoidHom.toContinuousMonoidHom (pullbackContEquivOfIsPullback α₁ α₂ β₁ β₂
            hpb)) =
      α₂ := by
  rfl

omit [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- Pointwise first-coordinate formula for the inverse of the canonical pullback equivalence. -/
@[simp 900] theorem pullbackContEquivOfIsPullback_symm_fst_apply
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) (x : TopologicalFiberProduct.carrier β₁
        β₂) :
    α₁ ((pullbackContEquivOfIsPullback α₁ α₂ β₁ β₂ hpb).symm x) =
      TopologicalFiberProduct.fst β₁ β₂ x := by
  have hfst :
      α₁.comp
          (ContinuousMonoidHom.toContinuousMonoidHom (pullbackContEquivOfIsPullback α₁ α₂ β₁ β₂
              hpb).symm) =
        TopologicalFiberProduct.fst β₁ β₂ := by
    calc
      α₁.comp
          (ContinuousMonoidHom.toContinuousMonoidHom (pullbackContEquivOfIsPullback α₁ α₂ β₁ β₂
              hpb).symm) =
        α₁.comp (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) := by
          rw [pullbackContEquivOfIsPullback_symm_toContinuousMonoidHom]
      _ = TopologicalFiberProduct.fst β₁ β₂ := by
        simpa using
          (fromContinuousPullbackOfIsPullback_spec α₁ α₂ β₁ β₂ hpb).1
  exact congrArg (fun f : TopologicalFiberProduct.carrier β₁ β₂ →ₜ* H₁ => f x) hfst

omit [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] in
/-- Pointwise second-coordinate formula for the inverse of the canonical pullback equivalence. -/
@[simp 900] theorem pullbackContEquivOfIsPullback_symm_snd_apply
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂) (x : TopologicalFiberProduct.carrier β₁
        β₂) :
    α₂ ((pullbackContEquivOfIsPullback α₁ α₂ β₁ β₂ hpb).symm x) =
      TopologicalFiberProduct.snd β₁ β₂ x := by
  have hsnd :
      α₂.comp
          (ContinuousMonoidHom.toContinuousMonoidHom (pullbackContEquivOfIsPullback α₁ α₂ β₁ β₂
              hpb).symm) =
        TopologicalFiberProduct.snd β₁ β₂ := by
    calc
      α₂.comp
          (ContinuousMonoidHom.toContinuousMonoidHom (pullbackContEquivOfIsPullback α₁ α₂ β₁ β₂
              hpb).symm) =
        α₂.comp (fromContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb) := by
          rw [pullbackContEquivOfIsPullback_symm_toContinuousMonoidHom]
      _ = TopologicalFiberProduct.snd β₁ β₂ := by
        simpa using
          (fromContinuousPullbackOfIsPullback_spec α₁ α₂ β₁ β₂ hpb).2
  exact congrArg (fun f : TopologicalFiberProduct.carrier β₁ β₂ →ₜ* H₂ => f x) hsnd

omit [IsTopologicalGroup H] in
/-- A commutative square has the universal property against profinite source groups if and only if
its canonical comparison map to the concrete continuous fiber product is bijective. -/
theorem hasProfiniteTestPullbackProperty_iff_bijective_toConcretePullback
    {α₁ : G →ₜ* H₁} {α₂ : G →ₜ* H₂}
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    (hcomm : β₁.comp α₁ = β₂.comp α₂) :
    HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂ ↔
      Function.Bijective
        (TopologicalFiberProduct.lift β₁ β₂ α₁ α₂ (fun g => DFunLike.congr_fun hcomm g)) := by
  constructor
  · intro hpb
    simpa [toContinuousPullbackOfIsPullback] using
      (bijective_toContinuousPullbackOfIsPullback α₁ α₂ β₁ β₂ hpb)
  · intro hbij
    exact hasProfiniteTestPullbackProperty_of_bijective_toConcretePullback
      α₁ α₂ β₁ β₂
      (TopologicalFiberProduct.lift β₁ β₂ α₁ α₂ (fun g => DFunLike.congr_fun hcomm g))
      hbij
      (TopologicalFiberProduct.fst_lift β₁ β₂ α₁ α₂ (fun g => DFunLike.congr_fun hcomm g))
      (TopologicalFiberProduct.snd_lift β₁ β₂ α₁ α₂ (fun g => DFunLike.congr_fun hcomm g))

end


end ProCGroups.Categorical
