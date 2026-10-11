/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Algebra.FilteredColimitModel
import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.RingTheory.Etale.Finite

/-!
# Finite-etale covers of spectra of filtered ring colimits

The actual finite-etale algebra model over a stage is transferred across the
existing affine equivalence. Its native base-change comparison yields recovery
along the literal `Spec` map of the given cocone component.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteEtale

/-- Every finite-etale cover of the spectrum of a filtered ring colimit is
the native pullback of a finite-etale cover over one actual ring stage. -/
theorem exists_filtered_colimit_spec_model
    {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (X : FiniteEtale (Spec c.pt)) :
    ∃ (i : J) (Xᵢ : FiniteEtale (Spec (F.obj i))),
      Nonempty ((FiniteEtale.pullback (Spec.map (c.ι.app i))).obj Xᵢ ≅ X) := by
  let e := FiniteEtale.affineEquivalence c.pt
  let A : CommAlgCat.FiniteEtale c.pt := e.functor.obj (op X)
  have : Module.Finite c.pt A.obj := A.property.left
  have : Algebra.Etale c.pt A.obj := A.property.right
  obtain ⟨i, hi⟩ := Algebra.FiniteEtale.exists_filtered_colimit_stage_model F c hc A.obj
  let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  obtain ⟨B, hring, halgebra, hfinite, hetale, ⟨eA⟩⟩ := hi
  let : CommRing B := hring
  let : Algebra (F.obj i) B := halgebra
  let Aᵢ : CommAlgCat.FiniteEtale (F.obj i) :=
    ⟨CommAlgCat.of (F.obj i) B, hfinite, hetale⟩
  let eᵢ := FiniteEtale.affineEquivalence (F.obj i)
  let Xᵢ : FiniteEtale (Spec (F.obj i)) := (eᵢ.inverse.obj Aᵢ).unop
  let b : CommAlgCat.FiniteEtale (F.obj i) ⥤ CommAlgCat.FiniteEtale c.pt :=
    CommAlgCat.FiniteEtale.baseChange (F.obj i) c.pt
  let p : FiniteEtale (Spec (F.obj i)) ⥤ FiniteEtale (Spec c.pt) :=
    FiniteEtale.pullback (Spec.map (c.ι.app i))
  let ea : A ≅ b.obj Aᵢ :=
    ObjectProperty.isoMk _ (CommAlgCat.isoMk eA)
  let en : b.obj (eᵢ.functor.obj (op Xᵢ)) ≅ e.functor.obj (op (p.obj Xᵢ)) :=
    (FiniteEtale.affineEquivalenceCompBaseChangeIso (F.obj i) c.pt).app (op Xᵢ)
  let eb : e.functor.obj (op (p.obj Xᵢ)) ≅ e.functor.obj (op X) :=
    en.symm ≪≫ b.mapIso (eᵢ.counitIso.app Aᵢ) ≪≫ ea.symm
  let es : op (p.obj Xᵢ) ≅ op X := e.functor.preimageIso eb
  exact ⟨i, Xᵢ, ⟨es.unop.symm⟩⟩

end AlgebraicGeometry.FiniteEtale
