/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.HenselianFullness
public import Nyll.SchemeTheory.FiniteEtale.Algebra.HenselianQuotientLift
public import Nyll.SchemeTheory.FiniteEtale.Algebra.JacobsonBaseChange
public import Mathlib.CategoryTheory.Equivalence

/-!
# Finite étale base change over a Henselian pair

Reduction is faithful by unramified rigidity, full by lifting the idempotent
of a graph, and essentially surjective by extracting a finite factor of an
étale lift. These constructions prove the equivalence for the canonical
tensor-product base-change functor.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CommAlgCat.FiniteEtale

/-- Finite étale algebras over a Henselian pair are equivalent to finite
étale algebras over its quotient. -/
@[stacks 09ZL]
theorem baseChange_isEquivalence_of_henselian
    {R : Type u} [CommRing R] (I : Ideal R) [HenselianRing R I] :
    (baseChange R (R ⧸ I) : CommAlgCat.FiniteEtale.{u} R ⥤
      CommAlgCat.FiniteEtale.{u} (R ⧸ I)).IsEquivalence where
  faithful := baseChange_faithful_of_le_jacobson I (HenselianRing.jac (R := R) (I := I))
  full := baseChange_full_of_henselian I
  essSurj := {
    mem_essImage A := by
      obtain ⟨B, hfinite, hetale, ⟨e⟩⟩ :=
        Algebra.FiniteEtale.exists_lift_of_quotient_of_henselian (A := A) I
      let : Module.Finite R B := hfinite
      let : Algebra.Etale R B := hetale
      exact ⟨FiniteEtale.of R B, ⟨FiniteEtale.isoMk e⟩⟩
  }

end CommAlgCat.FiniteEtale
