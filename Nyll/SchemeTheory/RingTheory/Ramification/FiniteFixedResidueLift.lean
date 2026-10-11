/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteInvariantResidueLift
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Invariant.Basic

/-!
# Finite quotient lifts expressed in the original residue ring

The native quotient action is first constructed on the fixed subring before
introducing a coefficient algebra. Its literal carrier is then the existing
fixed subalgebra over the original base. The finite uniform-lift theorem
produces equations directly in the original quotient B/q on N-fixed elements
of B. No fixed-ring quotient or residue algebra over such a quotient is used.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

private def fixedSubringNative (B : Type v) (G : Type w)
    [CommRing B] [Group G] [MulSemiringAction G B] (N : Subgroup G) :
    CommRingCat.{v} :=
  CommRingCat.of (FixedPoints.subring B N)

private abbrev fixedSubringQuotientAction (B : Type v) (G : Type w)
    [CommRing B] [Group G] [MulSemiringAction G B] (N : Subgroup G) [N.Normal] :
    MulSemiringAction (G ⧸ N) (fixedSubringNative B G N) :=
  inferInstanceAs (MulSemiringAction (G ⧸ N) (FixedPoints.subring B N))

variable (A : Type u) (B : Type v) (G : Type w)
    [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (N : Subgroup G)

private def fixedAlgebraNative : CommAlgCat.{v} A :=
  CommAlgCat.of A (FixedPoints.subalgebra A B N)

private def fixedAlgebraInclusion : fixedAlgebraNative A B G N →+* B :=
  subalgebraRingMap (FixedPoints.subalgebra A B N)

private theorem fixedAlgebraInclusion_injective :
    Function.Injective (fixedAlgebraInclusion A B G N).toFun :=
  subalgebraRingMap_injective (FixedPoints.subalgebra A B N)

private def fixedAlgebraBaseMap : A →+* fixedAlgebraNative A B G N :=
  subalgebraBaseMap (FixedPoints.subalgebra A B N)

private theorem fixedAlgebraBaseMap_eq_algebraMap :
    fixedAlgebraBaseMap A B G N = algebraMap A (fixedAlgebraNative A B G N) :=
  subalgebraBaseMap_eq_algebraMap (FixedPoints.subalgebra A B N)

private theorem fixedAlgebraInclusion_comp_base :
    (fixedAlgebraInclusion A B G N).comp (fixedAlgebraBaseMap A B G N) =
      algebraMap A B :=
  subalgebraRingMap_comp_base (FixedPoints.subalgebra A B N)

private def fixedAlgebraInclusionAlgHom : fixedAlgebraNative A B G N →ₐ[A] B where
  toRingHom := fixedAlgebraInclusion A B G N
  commutes' a := by
    have h : (fixedAlgebraInclusion A B G N).comp
        (algebraMap A (fixedAlgebraNative A B G N)) = algebraMap A B := by
      rw [← fixedAlgebraBaseMap_eq_algebraMap A B G N]
      exact fixedAlgebraInclusion_comp_base A B G N
    exact congrArg (fun f : A →+* B => f.toFun a) h

private theorem fixedAlgebraInclusion_smul
    (a : A) (c : fixedAlgebraNative A B G N) :
    (fixedAlgebraInclusion A B G N).toFun (a • c) =
      a • (fixedAlgebraInclusion A B G N).toFun c :=
  (fixedAlgebraInclusionAlgHom A B G N).toLinearMap.map_smul a c

private def fixedAlgebraElement (x : B) (hx : ∀ n ∈ N, n • x = x) :
    fixedAlgebraNative A B G N :=
  ⟨x, fun n => hx n.val n.property⟩

variable [N.Normal]

private abbrev fixedAlgebraQuotientAction :
    MulSemiringAction (G ⧸ N) (fixedAlgebraNative A B G N) :=
  fixedSubringQuotientAction B G N

attribute [local instance] fixedAlgebraQuotientAction

private theorem fixedAlgebraInclusion_quotient_smul
    (g : G) (c : fixedAlgebraNative A B G N) :
    (fixedAlgebraInclusion A B G N).toFun ((QuotientGroup.mk g : G ⧸ N) • c) =
      g • (fixedAlgebraInclusion A B G N).toFun c := rfl

private theorem fixedAlgebraQuotient_smulCommClass :
    SMulCommClass (G ⧸ N) A (fixedAlgebraNative A B G N) := by
  constructor
  intro h a c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
  apply fixedAlgebraInclusion_injective A B G N
  rw [fixedAlgebraInclusion_quotient_smul, fixedAlgebraInclusion_smul,
    fixedAlgebraInclusion_smul, fixedAlgebraInclusion_quotient_smul]
  exact smul_comm g a ((fixedAlgebraInclusion A B G N).toFun c)

private theorem fixedAlgebraQuotient_isInvariant [Algebra.IsInvariant A B G] :
    Algebra.IsInvariant A (fixedAlgebraNative A B G N) (G ⧸ N) := by
  constructor
  intro c hc
  have hcG : ∀ g : G, g • (fixedAlgebraInclusion A B G N).toFun c =
      (fixedAlgebraInclusion A B G N).toFun c := by
    intro g
    exact (fixedAlgebraInclusion_quotient_smul A B G N g c).symm.trans
      (congrArg (fixedAlgebraInclusion A B G N).toFun (hc (QuotientGroup.mk g)))
  obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G)
    ((fixedAlgebraInclusion A B G N).toFun c) hcG
  refine ⟨a, ?_⟩
  apply fixedAlgebraInclusion_injective A B G N
  exact ((fixedAlgebraInclusionAlgHom A B G N).commutes a).trans ha

private def fixedResidueCoefficient (q : Ideal B) :
    fixedAlgebraNative A B G N →+* B ⧸ q :=
  (Ideal.Quotient.mk q).comp (fixedAlgebraInclusion A B G N)

omit [N.Normal] in
private theorem fixedResidueCoefficient_comp_base (q : Ideal B) :
    (fixedResidueCoefficient A B G N q).comp
        (algebraMap A (fixedAlgebraNative A B G N)) =
      (Ideal.Quotient.mk q).comp (algebraMap A B) := by
  exact (RingHom.comp_assoc (algebraMap A (fixedAlgebraNative A B G N))
    (fixedAlgebraInclusion A B G N) (Ideal.Quotient.mk q)).trans
      (congrArg (fun f : A →+* B => (Ideal.Quotient.mk q).comp f)
        (fixedAlgebraInclusionAlgHom A B G N).comp_algebraMap)

private theorem fixedResidueCoefficient_quotient_smul
    (q : Ideal B) (g : G) (c : fixedAlgebraNative A B G N) :
    (fixedResidueCoefficient A B G N q).toFun ((QuotientGroup.mk g : G ⧸ N) • c) =
      (Ideal.Quotient.mk q).toFun (g • (fixedAlgebraInclusion A B G N).toFun c) :=
  congrArg (Ideal.Quotient.mk q).toFun
    (fixedAlgebraInclusion_quotient_smul A B G N g c)

omit [N.Normal] in
private theorem fixedResidueCoefficient_element
    (q : Ideal B) (x : B) (hx : ∀ n ∈ N, n • x = x) :
    (fixedResidueCoefficient A B G N q).toFun (fixedAlgebraElement A B G N x hx) =
      (Ideal.Quotient.mk q).toFun x := rfl

/-- A finite quotient of an invariant action supplies one original group
element whose residue equations hold on every N-fixed original element. -/
theorem exists_residue_lift_on_fixed_elements
    [Finite (G ⧸ N)] [Algebra.IsInvariant A B G]
    (q : Ideal B) [q.IsPrime] (φ : (B ⧸ q) ≃+* (B ⧸ q))
    (hφ : φ.toRingHom.comp ((Ideal.Quotient.mk q).comp (algebraMap A B)) =
      (Ideal.Quotient.mk q).comp (algebraMap A B)) :
    ∃ g : G, ∀ x : B, (∀ n ∈ N, n • x = x) →
      (Ideal.Quotient.mk q).toFun (g • x) =
        φ.toRingHom.toFun ((Ideal.Quotient.mk q).toFun x) := by
  have : SMulCommClass (G ⧸ N) A (fixedAlgebraNative A B G N) :=
    fixedAlgebraQuotient_smulCommClass A B G N
  have : Algebra.IsInvariant A (fixedAlgebraNative A B G N) (G ⧸ N) :=
    fixedAlgebraQuotient_isInvariant A B G N
  have hcoeff : φ.toRingHom.comp
        ((fixedResidueCoefficient A B G N q).comp
          (algebraMap A (fixedAlgebraNative A B G N))) =
      (fixedResidueCoefficient A B G N q).comp
        (algebraMap A (fixedAlgebraNative A B G N)) := by
    rw [fixedResidueCoefficient_comp_base A B G N q]
    exact hφ
  obtain ⟨h, hh⟩ := finiteInvariantRingHom_exists_lift (H := G ⧸ N)
    (fixedResidueCoefficient A B G N q) φ hcoeff
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
  refine ⟨g, ?_⟩
  intro x hx
  let c : fixedAlgebraNative A B G N := fixedAlgebraElement A B G N x hx
  exact (fixedResidueCoefficient_quotient_smul A B G N q g c).symm.trans
    ((hh c).trans (congrArg φ.toRingHom.toFun
      (fixedResidueCoefficient_element A B G N q x hx)))

end EtaleFundamentalGroups.Inertia
