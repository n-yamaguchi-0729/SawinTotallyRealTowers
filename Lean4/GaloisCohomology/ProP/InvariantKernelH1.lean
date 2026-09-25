/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.TrivialZModP
import ProCGroups.ProP.ContinuousH1
import ProCGroups.ProP.Presentation.Minimal
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
/-!
# Invariant continuous characters of a presentation kernel

This file packages the conjugation-invariant continuous `ZMod p` characters of the kernel of a
finite pro-`p` presentation as a `ZMod p`-submodule.  Evaluation on the displayed relators is
injective, so this invariant character space is finite-dimensional of rank at most the displayed
relation count.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

local instance continuousH1ZModModuleInstance
    {q : ℕ} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := H)) :=
  continuousH1ZModModule

/-- Minimality makes every continuous mod-`p` character of the free source vanish on the
presentation kernel. -/
theorem FiniteProPPresentation.kernel_le_character_ker
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (P : FiniteProPPresentation p d r sourceData G) (hP : P.IsMinimal)
    (chi : sourceData.carrier →ₜ* Multiplicative (ZMod p)) :
    P.quotient.toMonoidHom.ker ≤ chi.toMonoidHom.ker :=
  hP.trans (closedPowerCommutator_le_character_ker chi)

/-- Additively, every continuous degree-one class of the free source vanishes on the kernel of a
minimal presentation. -/
theorem FiniteProPPresentation.kernel_h1_eq_zero
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (P : FiniteProPPresentation p d r sourceData G) (hP : P.IsMinimal)
    (chi : ContinuousH1ZMod (p := p) (G := sourceData.carrier))
    (n : P.quotient.toMonoidHom.ker) :
    chi (Additive.ofMul n) = 0 := by
  have hn := P.kernel_le_character_ker hP (characterOfH1 chi) n.2
  exact congrArg Multiplicative.toAdd hn

/-- Continuous kernel characters fixed by conjugation from the free source. -/
def InvariantKernelCharacter
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (P : FiniteProPPresentation p d r sourceData G) :=
  {chi : P.quotient.toMonoidHom.ker →ₜ* Multiplicative (ZMod p) //
    ∀ (f : sourceData.carrier) (n : P.quotient.toMonoidHom.ker),
      chi (MulAut.conjNormal f n) = chi n}

/-- Evaluate an invariant kernel character on the displayed relators. -/
def invariantKernelCharacterRelatorEval
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (P : FiniteProPPresentation p d r sourceData G)
    (chi : InvariantKernelCharacter P) : Fin r → Multiplicative (ZMod p) :=
  fun i ↦ chi.1 ⟨P.relator i, P.relator_mem_kernel i⟩

/-- The displayed relators determine every invariant continuous kernel character. -/
theorem invariantKernelCharacterRelatorEval_injective
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (P : FiniteProPPresentation p d r sourceData G) :
    Function.Injective (invariantKernelCharacterRelatorEval P) := by
  intro chi psi heval
  apply Subtype.ext
  ext n
  let R : Subgroup sourceData.carrier := P.quotient.toMonoidHom.ker
  let E : Subgroup R := chi.1.toMonoidHom.eqLocus psi.1.toMonoidHom
  let K : Subgroup sourceData.carrier := E.map R.subtype
  have hRclosed : IsClosed (R : Set sourceData.carrier) :=
    ProCGroups.ContinuousMonoidHom.isClosed_ker P.quotient
  let _ : CompactSpace R := hRclosed.isClosedEmbedding_subtypeVal.compactSpace
  have hEclosed : IsClosed (E : Set R) :=
    isClosed_eq chi.1.continuous_toFun psi.1.continuous_toFun
  have hEcompact : IsCompact (E : Set R) := hEclosed.isCompact
  have hKclosed : IsClosed (K : Set sourceData.carrier) := by
    rw [Subgroup.coe_map]
    exact (hEcompact.image continuous_subtype_val).isClosed
  let _ : K.Normal := by
    refine ⟨?_⟩
    intro x hx f
    rcases hx with ⟨y, hy, rfl⟩
    refine ⟨MulAut.conjNormal f y, ?_, rfl⟩
    change chi.1 (MulAut.conjNormal f y) = psi.1 (MulAut.conjNormal f y)
    rw [chi.2 f y, psi.2 f y]
    exact hy
  have hrel : Set.range P.relator ⊆ K := by
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨P.relator i, P.relator_mem_kernel i⟩, ?_, rfl⟩
    exact congrFun heval i
  have hRK : R ≤ K := by
    change P.quotient.toMonoidHom.ker ≤ K
    rw [P.kernel_eq_closedNormalClosure]
    exact ProCGroups.Presentations.closedNormalClosure_le_closed_normal hKclosed hrel
  have hnK : (n : sourceData.carrier) ∈ K := hRK n.2
  rcases hnK with ⟨y, hy, hyn⟩
  have hyn' : y = n := Subtype.ext hyn
  change chi.1 y = psi.1 y at hy
  simpa [hyn'] using hy

/-- Conjugation-invariant additive degree-one classes on the presentation kernel. -/
def InvariantKernelH1
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (P : FiniteProPPresentation p d r sourceData G) :
    Submodule (ZMod p)
      (ContinuousH1ZMod (p := p) (G := P.quotient.toMonoidHom.ker)) where
  carrier := {chi | ∀ (f : sourceData.carrier) (n : P.quotient.toMonoidHom.ker),
    chi (Additive.ofMul (MulAut.conjNormal f n)) = chi (Additive.ofMul n)}
  zero_mem' := by
    change ∀ (f : sourceData.carrier) (n : P.quotient.toMonoidHom.ker),
      (0 : ContinuousH1ZMod (p := p) (G := P.quotient.toMonoidHom.ker))
          (Additive.ofMul (MulAut.conjNormal f n)) =
        (0 : ContinuousH1ZMod (p := p) (G := P.quotient.toMonoidHom.ker))
          (Additive.ofMul n)
    intros
    rfl
  add_mem' := by
    intro chi psi hchi hpsi f n
    change chi _ + psi _ = chi _ + psi _
    rw [hchi f n, hpsi f n]
  smul_mem' := by
    intro c chi hchi f n
    let evConj :
        ContinuousH1ZMod (p := p) (G := P.quotient.toMonoidHom.ker) →+ ZMod p :=
      { toFun := fun eta ↦ eta (Additive.ofMul (MulAut.conjNormal f n))
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    let ev : ContinuousH1ZMod (p := p) (G := P.quotient.toMonoidHom.ker) →+ ZMod p :=
      { toFun := fun eta ↦ eta (Additive.ofMul n)
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    exact (ZMod.map_smul evConj c chi).trans
      ((congrArg (fun z : ZMod p ↦ c • z) (hchi f n)).trans
        (ZMod.map_smul ev c chi).symm)

/-- Additive invariant classes and multiplicative invariant characters are canonically
equivalent. -/
def invariantKernelH1CharacterEquiv
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (P : FiniteProPPresentation p d r sourceData G) :
    InvariantKernelH1 P ≃ InvariantKernelCharacter P where
  toFun chi :=
    ⟨characterOfH1 chi.1, fun f n ↦ congrArg Multiplicative.ofAdd (chi.2 f n)⟩
  invFun chi :=
    ⟨h1OfCharacter chi.1, fun f n ↦ congrArg Multiplicative.toAdd (chi.2 f n)⟩
  left_inv chi := by
    apply Subtype.ext
    ext n
    rfl
  right_inv chi := by
    apply Subtype.ext
    ext n
    rfl

/-- Linear evaluation of invariant degree-one classes on the displayed relators. -/
def invariantKernelH1RelatorEval
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (P : FiniteProPPresentation p d r sourceData G) :
    InvariantKernelH1 P →ₗ[ZMod p] (Fin r → ZMod p) where
  toFun chi i := chi.1 (Additive.ofMul ⟨P.relator i, P.relator_mem_kernel i⟩)
  map_add' _ _ := rfl
  map_smul' c chi := by
    funext i
    let ev : ContinuousH1ZMod (p := p) (G := P.quotient.toMonoidHom.ker) →+ ZMod p :=
      { toFun := fun eta ↦ eta (Additive.ofMul ⟨P.relator i, P.relator_mem_kernel i⟩)
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    exact ZMod.map_smul ev c chi.1

/-- Linear evaluation on the displayed relators is injective. -/
theorem invariantKernelH1RelatorEval_injective
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (P : FiniteProPPresentation p d r sourceData G) :
    Function.Injective (invariantKernelH1RelatorEval P) := by
  intro chi psi heval
  apply (invariantKernelH1CharacterEquiv P).injective
  apply invariantKernelCharacterRelatorEval_injective P
  funext i
  exact congrArg Multiplicative.ofAdd (congrFun heval i)

/-- Invariant kernel classes are finite-dimensional for every finite displayed presentation. -/
theorem invariantKernelH1_finiteDimensional
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (P : FiniteProPPresentation p d r sourceData G) :
    FiniteDimensional (ZMod p) (InvariantKernelH1 P) :=
  FiniteDimensional.of_injective (invariantKernelH1RelatorEval P)
    (invariantKernelH1RelatorEval_injective P)

/-- The displayed relation count bounds the dimension of invariant kernel classes. -/
theorem finrank_invariantKernelH1_le_relationCard
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (P : FiniteProPPresentation p d r sourceData G) :
    Module.finrank (ZMod p) (InvariantKernelH1 P) ≤ r := by
  have hle := (invariantKernelH1RelatorEval P).finrank_le_finrank_of_injective
    (invariantKernelH1RelatorEval_injective P)
  simpa only [Module.finrank_fin_fun] using hle

end


end ClassFieldTower.ProP
