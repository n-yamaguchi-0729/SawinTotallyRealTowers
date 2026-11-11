/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Nyll.GaloisCohomology.Cyclic.IntegralCoefficientCohomology
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingCoinduction

/-!
# Shapiro for the native lifted-integer cohomology

The original coinduced representation is compared with coinduction after coefficient transport.
Mathlib's native Shapiro isomorphism then applies to those actual equivariant functions. The final
restriction of scalars retains their integral cohomology groups.
-/

@[expose] public section

noncomputable section

namespace IntegralGroupCohomology

open CategoryTheory

universe u

variable {G : Type u} [Group G] {S : Subgroup G}

/-- Shapiro's lemma for actual integer representations in the common group/carrier universe. -/
def coindIso (A : Rep.{u} ℤ S) (n : ℕ) :
    cohomology (Rep.coind S.subtype A) n ≅ cohomology A n :=
  integerScalars.mapIso
    ((groupCohomology.functor (ULift.{u} ℤ) G n).mapIso
      (Rep.coefficientRingCoindIso (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) S.subtype A) ≪≫
      groupCohomology.coindIso ((coefficientFunctor S).obj A) n)

/-- Vanishing passes to actual coinduced integral cohomology through native Shapiro. -/
theorem coind_subsingleton (A : Rep.{u} ℤ S) (n : ℕ)
    [Subsingleton (cohomology A n)] : Subsingleton (cohomology (Rep.coind S.subtype A) n) :=
  Function.Injective.subsingleton (coindIso A n).toLinearEquiv.injective

end IntegralGroupCohomology
