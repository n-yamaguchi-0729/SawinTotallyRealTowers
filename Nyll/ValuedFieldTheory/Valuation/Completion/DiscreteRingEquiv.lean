/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport
import Nyll.ValuedFieldTheory.Valuation.Completion.WithValScalars
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Topology.Algebra.UniformRing

/-!
# Completion of an isomorphism preserving discrete valuations

A field isomorphism which carries one valuation to an equivalent valuation
induces an isomorphism of the actual valued completions. The construction
preserves the original embedding of the field.
-/

namespace ValuationTheory.DiscreteValuationField.DVF

open MonoidWithZeroHom

variable {K L : Type*} [Field K] [Field L]
  (source : DVF K) (target : DVF L)

/-- Preservation of the valuation ordering makes a field isomorphism
uniformly continuous on the associated valued fields. -/
theorem withValRingEquiv_uniformContinuous (e : K ≃+* L)
    (he : source.valuation.IsEquiv (target.valuation.comap e.toRingHom)) :
    UniformContinuous (WithVal.congr source.valuation target.valuation e) := by
  let v : _root_.Valuation (WithVal source.valuation) source.ValueGroup := Valued.v
  let w : _root_.Valuation (WithVal target.valuation) target.ValueGroup := Valued.v
  let f : WithVal source.valuation ≃+* WithVal target.valuation :=
    WithVal.congr source.valuation target.valuation e
  have : w.IsRankOneDiscrete :=
    Valuation.isRankOneDiscrete_comap_ringEquiv target.valuation
      (WithVal.equiv target.valuation)
  have : MulArchimedean w.ValueGroup₀ :=
    (_root_.Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt w).symm.mulArchimedean
  obtain ⟨π, hπ⟩ := source.exists_uniformizer
  let p : WithVal source.valuation := WithVal.toVal source.valuation (π : K)
  have hp : p ≠ 0 := by
    intro hzero
    exact hπ.ne_zero (congrArg (WithVal.equiv source.valuation) hzero)
  have hfp : w.restrict (f p) < 1 := by
    apply w.restrict_lt_one_iff.mpr
    exact he.lt_one_iff_lt_one.mp hπ.val_lt_one
  change UniformContinuous f
  refine
    ((Valued.hasBasis_uniformity (WithVal source.valuation) source.ValueGroup).uniformContinuous_iff
      (Valued.hasBasis_uniformity (WithVal target.valuation) target.ValueGroup)).mpr ?_
  intro γ _
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hfp γ
  have hpn : v.restrict (p ^ n) ≠ 0 :=
    v.restrict.ne_zero_iff.mpr (pow_ne_zero n hp)
  let δ : (ValueGroup₀ (.ofClass v))ˣ := Units.mk0 (v.restrict (p ^ n)) hpn
  refine ⟨δ, trivial, ?_⟩
  intro x y hxy
  have hsource : source.valuation ((WithVal.equiv source.valuation) (y - x)) <
      source.valuation ((WithVal.equiv source.valuation) (p ^ n)) :=
    v.restrict_lt_iff.mp hxy
  have htarget : w (f (y - x)) < w (f (p ^ n)) := he.lt_iff_lt.mp hsource
  change w.restrict (f y - f x) < (γ : w.ValueGroup₀)
  rw [← map_sub]
  calc
    w.restrict (f (y - x)) < w.restrict (f (p ^ n)) := w.restrict_lt_iff.mpr htarget
    _ = w.restrict (f p) ^ n := by rw [map_pow, map_pow]
    _ < γ := hn

/-- The equivalence of completed fields induced by a valuation preserving
field isomorphism. -/
noncomputable def completionRingEquiv (e : K ≃+* L)
    (he : source.valuation.IsEquiv (target.valuation.comap e.toRingHom)) :
    source.valuation.Completion ≃+* target.valuation.Completion :=
  UniformSpace.Completion.mapRingEquiv
    (WithVal.congr source.valuation target.valuation e)
    (withValRingEquiv_uniformContinuous source target e he).continuous
    (withValRingEquiv_uniformContinuous target source e.symm (by
      intro x y
      simpa only [Valuation.comap_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, RingEquiv.apply_symm_apply] using
        (he (e.symm x) (e.symm y)).symm)).continuous

/-- The completed isomorphism restricts to the supplied isomorphism on the
original fields. -/
@[simp] theorem completionRingEquiv_algebraMap (e : K ≃+* L)
    (he : source.valuation.IsEquiv (target.valuation.comap e.toRingHom)) (x : K) :
    completionRingEquiv source target e he (algebraMap K source.valuation.Completion x) =
      algebraMap L target.valuation.Completion (e x) := by
  exact UniformSpace.Completion.mapRingHom_coe
    (withValRingEquiv_uniformContinuous source target e he).continuous
    (WithVal.toVal source.valuation x)

end ValuationTheory.DiscreteValuationField.DVF
