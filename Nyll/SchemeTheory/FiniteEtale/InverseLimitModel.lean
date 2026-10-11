/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.InverseLimitRawCharts
import Nyll.SchemeTheory.FiniteEtale.InverseLimitRawModel
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Finite-etale objects descend along general qcqs inverse limits

Starting with the original finite-etale object over an actual inverse
limit, construct a finite affine stage cover and recovered local models.
Actual morphism descent and eventual gluing equations then give a global
finite-etale model over an original stage, with literal native recovery.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

/-- Every finite-etale object over the actual inverse limit of qcqs schemes
with affine transition maps descends to an original stage. The recovery
isomorphism is along the literal native finite-etale pullback functor. -/
theorem exists_inverse_limit_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (X : FiniteEtale c.pt) :
    ∃ (i : I) (N : FiniteEtale (D.obj i)),
      Nonempty ((FiniteEtale.pullback (c.π.app i)).obj N ≅ X) := by
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨j, 𝒰, h𝒰, M, hAffine, hFiniteEtale, ⟨e⟩⟩ :=
    exists_recovered_raw_chart_models D c hc i X
  have : Fintype 𝒰.I₀ := h𝒰
  have : ∀ a : 𝒰.I₀, IsAffine (𝒰.X a) := hAffine
  have : ∀ a : 𝒰.I₀, IsFiniteEtale (M a).hom := hFiniteEtale
  exact exists_inverse_limit_model_of_standard_charts D c hc j 𝒰 M X e

end AlgebraicGeometry.FiniteEtale
