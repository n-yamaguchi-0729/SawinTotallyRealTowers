/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.AbsoluteRealKernelField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.GlobalMaximalAbelianRestriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.GlobalReciprocityCharacter
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.MaximalAbelianFiniteProjection
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
import ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.LocalBlocks
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfinitePlaceArtin
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianGlobalArtin
import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# Real Artin values and global reciprocity

Complex conjugation in the algebraic closure restricts to the chosen
negative-one Artin value in every finite abelian subextension. These finite
projections identify its maximal-abelian restriction with the actual idele
Artin value. Consequently global reciprocity preserves the real value of
an absolute character over a totally real number field.
-/

noncomputable section
namespace ClassFieldTower.Sawin
open NumberField GlobalClassFieldTheory.Reciprocity
open ClassFieldTower.Martinet.Shafarevich
open scoped NumberField IsMulCommutative

private theorem conjugation_eq_chosenArtin
    (F E : Type) [Field F] [Field E]
    [Algebra F E] [IsAbelianGalois F E]
    (v : InfinitePlace F) (phi : E →+* ℂ)
    (hw : (InfinitePlace.mk phi).comap (algebraMap F E) = v)
    (s : Gal(E/F)) (hs : ComplexEmbedding.IsConj phi s) :
    s = chosenInfinitePlaceArtinMonoidHom (K := F) (L := E)
      v (-1 : v.Completionˣ) := by
  let w : InfinitePlace E := InfinitePlace.mk phi
  let w' : InfinitePlace E := chosenInfinitePlaceAbove (L := E) v
  have hw' : w'.comap (algebraMap F E) = v := chosenInfinitePlaceAbove_comap (L := E) v
  obtain ⟨g, hg⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (hw.trans hw'.symm)
  have hmem : s ∈ MulAction.stabilizer Gal(E/F) w := by
    change s ∈ MulAction.stabilizer Gal(E/F) (InfinitePlace.mk phi)
    rw [InfinitePlace.mem_stabilizer_mk_iff]
    exact Or.inr hs
  have hmem' : s ∈ MulAction.stabilizer Gal(E/F) w' := by
    rw [← hg, MulAction.mem_stabilizer_iff]
    rw [MulAction.mem_stabilizer_iff] at hmem
    calc
      s • (g • w) = (s * g) • w := (mul_smul s g w).symm
      _ = (g * s) • w := by rw [mul_comm]
      _ = g • (s • w) := mul_smul g s w
      _ = g • w := congrArg (fun z : InfinitePlace E => g • z) hmem
  by_cases hone : s = 1
  · have hwReal : w.IsReal := by
      apply InfinitePlace.not_isComplex_iff_isReal.mp
      intro hc
      exact ((ComplexEmbedding.isConj_ne_one_iff hs).mpr
        (InfinitePlace.isComplex_mk_iff.mp hc)) hone
    have hw'Real : w'.IsReal := by
      rw [← hg, InfinitePlace.isReal_smul_iff]
      exact hwReal
    have hunram : w'.IsUnramified F := hw'Real.isUnramified (k := F)
    rw [hone]
    simp only [chosenInfinitePlaceArtinMonoidHom, infinitePlaceArtinMonoidHomOfPlace,
      show (chosenInfinitePlaceAbove (L := E) v).IsUnramified F from hunram,
      dite_true, MonoidHom.one_apply]
  · have hs' : ComplexEmbedding.IsConj w'.embedding s := by
      rw [← InfinitePlace.mk_embedding w', InfinitePlace.mem_stabilizer_mk_iff] at hmem'
      exact hmem'.resolve_left hone
    have hw'Complex : w'.IsComplex := by
      apply InfinitePlace.isComplex_iff.mpr
      exact (ComplexEmbedding.isConj_ne_one_iff hs').mp hone
    have hw'RealBase : (w'.comap (algebraMap F E)).IsReal := by
      rw [← InfinitePlace.mk_embedding w', InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff]
      exact hs'.isReal_comp
    have hr : w'.IsRamified F := InfinitePlace.isRamified_iff.mpr ⟨hw'Complex, hw'RealBase⟩
    exact hs'.ext (chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
      (K := F) (L := E) v hr)

private theorem algebraicClosure_place_complex
    (F : Type) [Field F] (w : InfinitePlace (AlgebraicClosure F)) : w.IsComplex := by
  apply InfinitePlace.not_isReal_iff_isComplex.mp
  intro hw
  let rho : AlgebraicClosure F →+* ℝ := (InfinitePlace.isReal_iff.mp hw).embedding
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure F) (by decide : 0 < 2)
  have h : rho z ^ 2 = (-1 : ℝ) := by
    rw [← map_pow, hz, map_neg, map_one]
  have hn : 0 ≤ rho z ^ 2 := sq_nonneg (rho z)
  linarith

/-- The actual real Artin generator restricts to the maximal-abelian
idele Artin value of negative one. -/
theorem absoluteInfinitePlaceArtinNegOne_maximalAbelian
    (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (v : InfinitePlace F) :
    globalMaximalAbelianRestriction F (absoluteInfinitePlaceArtinNegOne F v) =
      maximalAbelianGlobalArtin F
        (IdeleGroup.infinitePlaceIdeleClass v (-1 : v.Completionˣ)) := by
  let c : Gal(AlgebraicClosure F/F) :=
    chosenInfinitePlaceArtinMonoidHom (K := F) (L := AlgebraicClosure F)
      v (-1 : v.Completionˣ)
  let sigma : Field.absoluteGaloisGroup F := (absoluteGaloisGroupContinuousMulEquiv F).symm c
  let w : InfinitePlace (AlgebraicClosure F) := chosenInfinitePlaceAbove (L := AlgebraicClosure F) v
  have hr : w.IsRamified F := InfinitePlace.isRamified_iff.mpr
    ⟨algebraicClosure_place_complex F w, IsTotallyReal.isReal (w.comap (algebraMap F (AlgebraicClosure F)))⟩
  have hc : ComplexEmbedding.IsConj w.embedding c :=
    chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
      (K := F) (L := AlgebraicClosure F) v hr
  apply maximalAbelianGalois_ext_of_finite_restrictions F
  intro E
  have : NumberField E := NumberField.of_module_finite F E
  have hprojection : AlgEquiv.restrictNormalHom E
      (maximalAbelianGlobalArtin F (IdeleGroup.infinitePlaceIdeleClass v (-1 : v.Completionˣ))) =
      chosenInfinitePlaceArtinMonoidHom (K := F) (L := E) v (-1 : v.Completionˣ) := by
    have hfinite := maximalAbelianGlobalArtin_finiteProjection F
      (IdeleGroup.infinitePlaceIdele v (-1 : v.Completionˣ)) E
    simp only [IdeleGroup.infinitePlaceIdeleClass, MonoidHom.comp_apply]
    rw [hfinite]
    apply globalArtinMonoidHom_infinitePlaceIdele (K := F) (L := E)
  rw [hprojection]
  let i : E →ₐ[F] AlgebraicClosure F :=
    (separableClosure F (AlgebraicClosure F)).val.comp
      ((_root_.maximalAbelianExtension F).val.comp E.val)
  let t : Gal(E/F) := AlgEquiv.restrictNormalHom E (globalMaximalAbelianRestriction F sigma)
  let phi : E →+* ℂ := w.embedding.comp i.toRingHom
  have ht (z : E) : i (t z) = c (i z) := by
    let s : Gal(SeparableClosure F/F) :=
      RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv F sigma
    have hE := AlgEquiv.restrictNormal_commutes (globalMaximalAbelianRestriction F sigma) E z
    have hM := AlgEquiv.restrictNormal_commutes s (_root_.maximalAbelianExtension F)
      (algebraMap E (_root_.maximalAbelianExtension F) z)
    exact (congrArg (fun x : _root_.maximalAbelianExtension F =>
      (((x : SeparableClosure F) : AlgebraicClosure F))) hE).trans
      (congrArg (fun x : SeparableClosure F => (x : AlgebraicClosure F)) hM)
  have htConj : ComplexEmbedding.IsConj phi t := by
    apply RingHom.ext
    intro z
    change star (w.embedding (i z)) = w.embedding (i (t z))
    rw [ht, hc.eq]
  have hphi : (InfinitePlace.mk phi).comap (algebraMap F E) = v := by
    rw [InfinitePlace.comap_mk]
    have he : phi.comp (algebraMap F E) = w.embedding.comp (algebraMap F (AlgebraicClosure F)) := by
      ext x
      exact congrArg w.embedding (i.commutes x)
    rw [he, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
    exact chosenInfinitePlaceAbove_comap (L := AlgebraicClosure F) v
  exact conjugation_eq_chosenArtin F E v phi hphi t htConj

/-- The global idele character has the same real sign as its given absolute
character, through the actual Artin maps. -/
theorem globalReciprocityIdeleCharacter_infinite_neg_one
    (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (p : ℕ) [Fact p.Prime]
    (chi : Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod p))
    (v : InfinitePlace F) :
    globalReciprocityIdeleCharacter F p chi
      (IdeleGroup.infinitePlaceIdele v (-1 : v.Completionˣ)) =
      chi (absoluteInfinitePlaceArtinNegOne F v) := by
  rw [globalReciprocityIdeleCharacter_apply]
  change globalReciprocityMaximalAbelianCharacter F p chi
    (maximalAbelianGlobalArtin F (IdeleGroup.infinitePlaceIdeleClass v (-1 : v.Completionˣ))) =
      chi (absoluteInfinitePlaceArtinNegOne F v)
  rw [← absoluteInfinitePlaceArtinNegOne_maximalAbelian F v]
  exact globalReciprocityMaximalAbelianCharacter_restriction F p chi
    (absoluteInfinitePlaceArtinNegOne F v)

end ClassFieldTower.Sawin
