/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.GlobalBaseChange
public import Nyll.SchemeTheory.Affine.WeilRestriction.Local
public import Nyll.SchemeTheory.WeilRestriction.BaseChange
public import Nyll.SchemeTheory.WeilRestriction.Congr
public import Nyll.SchemeTheory.Affine.WeilRestriction.Global

/-!
# Local representers of the restricted global internal Hom

The local tensor-product construction represents the restriction of one fixed
presheaf on schemes over `Spec R`. The comparison combines geometric base change
with the spectrum of a tensor product. This provides the local witnesses needed
for gluing without assuming compatibility of separately constructed functors.
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section

universe u

namespace SchemeTheory.Affine

/-- Restricting the affine internal Hom to `Spec S` agrees with scalar extension
of its two input algebras. No freeness or finiteness is needed for this comparison. -/
def globalInternalHomRestrictionBaseChangeIso
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap R S)))).op ⋙
        globalInternalHomFunctor (R := R) (A := A) (B := B) ≅
      globalInternalHomFunctor (R := S) (A := S ⊗[R] A) (B := S ⊗[R] B) :=
  (SchemeTheory.WeilRestriction.relativeInternalHomBaseChangeIso
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (specAOver (R := R) (A := A)) (specBOver (R := R) (B := B))).trans <|
      SchemeTheory.WeilRestriction.relativeInternalHomIso
        (specOverBaseChangeIso R S A) (specOverBaseChangeIso R S B)

/-- Each point has a principal neighborhood on which the restriction of the
global relative internal Hom is represented by a finite étale scheme. -/
theorem exists_finiteEtaleInternalHomRepresentable_restrict_away
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Module.Finite R A] [Algebra.Etale R A]
    [Module.Finite R B] [Algebra.Etale R B] (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧
      ∃ W : FiniteEtale (Spec (CommRingCat.of (Localization.Away r))),
        Nonempty (((Over.map
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).op ⋙
            globalInternalHomFunctor (R := R) (A := A) (B := B)).RepresentableBy
              ((FiniteEtale.forget (Spec (CommRingCat.of (Localization.Away r)))).obj W)) := by
  obtain ⟨r, hr, W, ⟨hW⟩⟩ :=
    exists_finiteEtaleInternalHomRepresentable_away (R := R) (A := A) (B := B) p
  exact ⟨r, hr, W, ⟨hW.ofIso
    (globalInternalHomRestrictionBaseChangeIso
      (R := R) (S := Localization.Away r) (A := A) (B := B)).symm⟩⟩

end SchemeTheory.Affine
