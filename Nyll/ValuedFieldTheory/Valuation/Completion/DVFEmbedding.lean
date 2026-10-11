/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Completion maps for extensions of discrete valuations

Powers of a ground-field uniformizer are cofinal in the target valuation
balls. The Archimedean property is used only for the actual value group of
the target valuation, which is order-isomorphic to the multiplicative
integers with zero. Thus an extension of discrete valuations induces a
uniformly continuous field map and an actual map of completions.
-/

namespace ValuationTheory.DiscreteValuationField.DVF

open MonoidWithZeroHom

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (base : DVF K) (target : DVF L) [base.valuation.HasExtension target.valuation]

/-- The actual field embedding is uniformly continuous for the two discrete
valuation topologies. No agreement of independently normalized norms is needed. -/
theorem withValMap_uniformContinuous :
    UniformContinuous (WithVal.map base.valuation target.valuation (algebraMap K L)) := by
  let v : _root_.Valuation (WithVal base.valuation) base.ValueGroup := Valued.v
  let w : _root_.Valuation (WithVal target.valuation) target.ValueGroup := Valued.v
  let f : WithVal base.valuation →+* WithVal target.valuation :=
    WithVal.map base.valuation target.valuation (algebraMap K L)
  have : w.IsRankOneDiscrete :=
    Valuation.isRankOneDiscrete_comap_ringEquiv target.valuation (WithVal.equiv target.valuation)
  have : MulArchimedean w.ValueGroup₀ :=
    (_root_.Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt w).symm.mulArchimedean
  obtain ⟨π, hπ⟩ := base.exists_uniformizer
  let p : WithVal base.valuation := WithVal.toVal base.valuation (π : K)
  have hp : p ≠ 0 := by
    intro hpzero
    exact hπ.ne_zero (congrArg (WithVal.equiv base.valuation) hpzero)
  have hfp : w.restrict (f p) < 1 := by
    apply w.restrict_lt_one_iff.mpr
    exact (_root_.Valuation.HasExtension.val_map_lt_one_iff
      base.valuation target.valuation (π : K)).mpr hπ.val_lt_one
  change UniformContinuous f
  refine
    ((Valued.hasBasis_uniformity (WithVal base.valuation) base.ValueGroup).uniformContinuous_iff
    (Valued.hasBasis_uniformity (WithVal target.valuation) target.ValueGroup)).mpr ?_
  intro γ hγ
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hfp γ
  have hpn : v.restrict (p ^ n) ≠ 0 :=
    v.restrict.ne_zero_iff.mpr (pow_ne_zero n hp)
  let δ : (ValueGroup₀ (.ofClass v))ˣ := Units.mk0 (v.restrict (p ^ n)) hpn
  refine ⟨δ, trivial, ?_⟩
  intro x y hxy
  have hsource : base.valuation ((WithVal.equiv base.valuation) (y - x)) <
      base.valuation ((WithVal.equiv base.valuation) (p ^ n)) :=
    v.restrict_lt_iff.mp hxy
  have htarget : w (f (y - x)) < w (f (p ^ n)) :=
    (_root_.Valuation.HasExtension.val_map_lt_iff base.valuation target.valuation
      ((WithVal.equiv base.valuation) (y - x))
      ((WithVal.equiv base.valuation) (p ^ n))).mpr hsource
  change w.restrict (f y - f x) < (γ : w.ValueGroup₀)
  rw [← map_sub]
  calc
    w.restrict (f (y - x)) < w.restrict (f (p ^ n)) := w.restrict_lt_iff.mpr htarget
    _ = w.restrict (f p) ^ n := by rw [map_pow, map_pow]
    _ < γ := hn

/-- The map of completions induced by an extension of discrete valuations. -/
noncomputable def completionMap : base.valuation.Completion →+* target.valuation.Completion :=
  UniformSpace.Completion.mapRingHom
    (WithVal.map base.valuation target.valuation (algebraMap K L))
    (withValMap_uniformContinuous base target).continuous

/-- The completion map agrees with the actual field embedding on `WithVal`. -/
@[simp] theorem completionMap_coe (x : WithVal base.valuation) :
    completionMap base target (x : base.valuation.Completion) =
      (WithVal.map base.valuation target.valuation (algebraMap K L) x :
        target.valuation.Completion) :=
  UniformSpace.Completion.mapRingHom_coe
    (withValMap_uniformContinuous base target).continuous x

/-- On an original ground-field element, the completion map is the algebra map. -/
@[simp] theorem completionMap_coe_base (x : K) :
    completionMap base target (x : base.valuation.Completion) =
      (algebraMap K L x : target.valuation.Completion) :=
  completionMap_coe base target (WithVal.toVal base.valuation x)

end ValuationTheory.DiscreteValuationField.DVF
