/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.FlatBaseChangeAffinization
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Finiteness.Descent

/-!
# Descending finite étale global sections

The algebra of global sections descends as an actual finite étale algebra
when it is finite étale after faithfully flat affine base change. The
comparison is the pushout of the four actual maps on sections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace RingHom.FiniteEtale

/-- Descent across a specified pushout of ring maps. The three scalar
structures are owned by the given maps; no second route to the same
algebra structure is introduced. -/
theorem of_isPushout
    {A B C D : CommRingCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    (i : B ⟶ D) (j : C ⟶ D) (h : IsPushout f g i j)
    (hg : g.hom.FaithfullyFlat) (hj : j.hom.FiniteEtale) : f.hom.FiniteEtale := by
  let : Algebra A B := f.hom.toAlgebra
  let : Algebra A C := g.hom.toAlgebra
  let : Algebra C D := j.hom.toAlgebra
  let : Module.FaithfullyFlat A C := hg
  let : Algebra.FiniteEtale C D := hj
  let e₀ := (CommRingCat.isPushout_tensorProduct A C B).isoPushout ≪≫
    h.flip.isoPushout.symm
  let e : C ⊗[A] B ≃ₐ[C] D :=
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv
      commutes' c := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) c = j c
        congr 2
        simp only [e₀, Iso.trans_hom, Iso.symm_hom,
          IsPushout.inl_isoPushout_hom_assoc, IsPushout.inl_isoPushout_inv] }
  let : Module.Finite C (C ⊗[A] B) := Module.Finite.equiv e.symm.toLinearEquiv
  let : Algebra.Etale C (C ⊗[A] B) := Algebra.Etale.of_equiv e.symm
  let : Algebra.Etale A B := Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat C
  let : Module.Finite A B := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat C
  exact ⟨⟩

end RingHom.FiniteEtale

namespace AlgebraicGeometry

/-- Finite étaleness of global sections descends along an affine fpqc
base change of a qcqs scheme. -/
theorem finiteEtale_appTop_of_flat_baseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [IsAffine S] [IsAffine T] [QuasiCompact f] [QuasiSeparated f]
    [Flat g] [Surjective g]
    (h : (pullback.snd f g).appTop.hom.FiniteEtale) : f.appTop.hom.FiniteEtale := by
  exact RingHom.FiniteEtale.of_isPushout f.appTop g.appTop
    (pullback.fst f g).appTop (pullback.snd f g).appTop
    (isPushout_appTop_of_flat f g)
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
      ⟨inferInstance, inferInstance⟩) h

end AlgebraicGeometry
