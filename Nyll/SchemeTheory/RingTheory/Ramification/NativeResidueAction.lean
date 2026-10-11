/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.ProfiniteInvariantResidueLift
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# The actual native residue-action homomorphism

The source and target are the existing stabilizer and quotient-algebra
 automorphism groups. The map is exactly Ideal.Quotient.stabilizerHom.
Its surjectivity is obtained from the constructed global residue equations,
and its kernel mapped to the original group is the native inertia subgroup.
The quotient-algebra-to-ring conversion is proved before profinite data occur.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open scoped Pointwise

universe u v

/-- The actual prime stabilizer with its native group structure. -/
def nativeResidueStabilizer (B G : Type v) [CommRing B] [Group G]
    [MulSemiringAction G B] (q : Ideal B) : GrpCat.{v} :=
  GrpCat.of (MulAction.stabilizer G q)

/-- The actual algebra automorphisms of the literal residue quotient. -/
def nativeResidueAutomorphisms (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (q : Ideal B) [q.LiesOver p] : GrpCat.{v} :=
  GrpCat.of ((B ⧸ q) ≃ₐ[A ⧸ p] (B ⧸ q))

/-- The original stabilizer inclusion. -/
def nativeResidueStabilizerInclusion (B G : Type v) [CommRing B] [Group G]
    [MulSemiringAction G B] (q : Ideal B) : nativeResidueStabilizer B G q →* G :=
  (MulAction.stabilizer G q).subtype

/-- The literal canonical residue homomorphism, retained as its native group map. -/
def nativeResidueStabilizerHom (A : Type u) (B G : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (p : Ideal A) (q : Ideal B) [q.LiesOver p] :
    nativeResidueStabilizer B G q →* nativeResidueAutomorphisms A B p q :=
  Ideal.Quotient.stabilizerHom q p G

/-- The same actual map as a native group-category morphism. -/
def nativeResidueStabilizerMorphism (A : Type u) (B G : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (p : Ideal A) (q : Ideal B) [q.LiesOver p] :
    GrpCat.Hom (nativeResidueStabilizer B G q) (nativeResidueAutomorphisms A B p q) where
  hom' := Ideal.Quotient.stabilizerHom q p G

/-- Forget only the coefficient-linearity proof of the actual automorphism. -/
def nativeResidueAutomorphismRingEquiv (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (q : Ideal B) [q.LiesOver p]
    (σ : nativeResidueAutomorphisms A B p q) : (B ⧸ q) ≃+* (B ⧸ q) :=
  (show (B ⧸ q) ≃ₐ[A ⧸ p] (B ⧸ q) from σ).toRingEquiv

/-- The native quotient coefficient square, before an automorphism is introduced. -/
private theorem nativeQuotientCoefficient_square
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (q : Ideal B) [q.LiesOver p] :
    (Ideal.Quotient.mk q).comp (algebraMap A B) =
      (algebraMap (A ⧸ p) (B ⧸ q)).comp (Ideal.Quotient.mk p) := by
  apply RingHom.ext
  intro a
  simpa only [RingHom.comp_apply] using
    (Ideal.Quotient.algebraMap_mk_of_liesOver q p a).symm

/-- The original quotient-algebra automorphism fixes the actual A coefficients. -/
theorem nativeResidueAutomorphismRingEquiv_comp_coefficient
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (q : Ideal B) [q.LiesOver p]
    (σ : nativeResidueAutomorphisms A B p q) :
    (nativeResidueAutomorphismRingEquiv A B p q σ).toRingHom.comp
        ((Ideal.Quotient.mk q).comp (algebraMap A B)) =
      (Ideal.Quotient.mk q).comp (algebraMap A B) := by
  let ψ : (B ⧸ q) ≃ₐ[A ⧸ p] (B ⧸ q) := σ
  have hforget : (nativeResidueAutomorphismRingEquiv A B p q σ).toRingHom =
      ψ.toAlgHom.toRingHom := rfl
  have hcoeff := nativeQuotientCoefficient_square A B p q
  have hfix : ψ.toAlgHom.toRingHom.comp (algebraMap (A ⧸ p) (B ⧸ q)) =
      algebraMap (A ⧸ p) (B ⧸ q) := ψ.toAlgHom.comp_algebraMap
  calc
    (nativeResidueAutomorphismRingEquiv A B p q σ).toRingHom.comp
        ((Ideal.Quotient.mk q).comp (algebraMap A B)) =
      ψ.toAlgHom.toRingHom.comp
        ((algebraMap (A ⧸ p) (B ⧸ q)).comp (Ideal.Quotient.mk p)) :=
      congrArg₂ (fun (f : (B ⧸ q) →+* (B ⧸ q)) (g : A →+* (B ⧸ q)) => f.comp g)
        hforget hcoeff
    _ = (ψ.toAlgHom.toRingHom.comp (algebraMap (A ⧸ p) (B ⧸ q))).comp
        (Ideal.Quotient.mk p) :=
      (RingHom.comp_assoc (Ideal.Quotient.mk p)
        (algebraMap (A ⧸ p) (B ⧸ q)) ψ.toAlgHom.toRingHom).symm
    _ = (algebraMap (A ⧸ p) (B ⧸ q)).comp (Ideal.Quotient.mk p) :=
      congrArg (fun f : (A ⧸ p) →+* (B ⧸ q) => f.comp (Ideal.Quotient.mk p)) hfix
    _ = (Ideal.Quotient.mk q).comp (algebraMap A B) := hcoeff.symm

/-- Forgetting coefficient-linearity does not identify distinct automorphisms. -/
theorem nativeResidueAutomorphismRingEquiv_injective
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (q : Ideal B) [q.LiesOver p] :
    Function.Injective (nativeResidueAutomorphismRingEquiv A B p q) := by
  intro σ τ h
  change (show (B ⧸ q) ≃ₐ[A ⧸ p] (B ⧸ q) from σ) =
    (show (B ⧸ q) ≃ₐ[A ⧸ p] (B ⧸ q) from τ)
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun e : (B ⧸ q) ≃+* (B ⧸ q) => e.toRingHom.toFun x) h

private theorem residueEquation_mem_stabilizer
    {B G : Type v} [CommRing B] [Group G] [MulSemiringAction G B]
    (q : Ideal B) (φ : (B ⧸ q) ≃+* (B ⧸ q)) (g : G)
    (hg : ∀ b : B, (Ideal.Quotient.mk q).toFun (g • b) =
      φ.toRingHom.toFun ((Ideal.Quotient.mk q).toFun b)) :
    g ∈ MulAction.stabilizer G q := by
  have hmem (b : B) : g • b ∈ q ↔ b ∈ q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
    have hb : Ideal.Quotient.mk q (g • b) = φ (Ideal.Quotient.mk q b) := by
      simpa only [RingHom.toFun_eq_coe, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom] using hg b
    rw [hb]
    constructor
    · intro hz
      apply φ.injective
      exact hz.trans (map_zero φ).symm
    · intro hz
      rw [hz]
      exact map_zero φ
  change g • q = q
  apply Ideal.ext
  intro b
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  simpa only [smul_inv_smul] using (hmem (g⁻¹ • b)).symm

/-- The proved global residue equation constructs an actual stabilizer element. -/
def nativeResidueStabilizerOfEquation
    {B G : Type v} [CommRing B] [Group G] [MulSemiringAction G B]
    (q : Ideal B) (φ : (B ⧸ q) ≃+* (B ⧸ q)) (g : G)
    (hg : ∀ b : B, (Ideal.Quotient.mk q).toFun (g • b) =
      φ.toRingHom.toFun ((Ideal.Quotient.mk q).toFun b)) :
    nativeResidueStabilizer B G q :=
  ⟨g, residueEquation_mem_stabilizer q φ g hg⟩

/-- The constructed stabilizer element retains its original group element. -/
theorem nativeResidueStabilizerOfEquation_value
    {B G : Type v} [CommRing B] [Group G] [MulSemiringAction G B]
    (q : Ideal B) (φ : (B ⧸ q) ≃+* (B ⧸ q)) (g : G)
    (hg : ∀ b : B, (Ideal.Quotient.mk q).toFun (g • b) =
      φ.toRingHom.toFun ((Ideal.Quotient.mk q).toFun b)) :
    (nativeResidueStabilizerInclusion B G q).toFun
      (nativeResidueStabilizerOfEquation q φ g hg) = g := rfl

/-- The native residue action has its literal value on original coefficients. -/
theorem nativeResidueStabilizerHom_apply_coefficient
    (A : Type u) (B G : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (p : Ideal A) (q : Ideal B) [q.LiesOver p]
    (d : nativeResidueStabilizer B G q) (b : B) :
    (nativeResidueAutomorphismRingEquiv A B p q
      ((nativeResidueStabilizerHom A B G p q).toFun d)).toRingHom.toFun
        ((Ideal.Quotient.mk q).toFun b) =
      (Ideal.Quotient.mk q).toFun ((nativeResidueStabilizerInclusion B G q).toFun d • b) := rfl

/-- The actual native residue action is surjective for the original profinite
invariant action. Its lift is constructed by compact residue equations. -/
theorem nativeResidueStabilizerHom_surjective
    (A : Type u) (B G : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
    (p : Ideal A) (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    Function.Surjective (nativeResidueStabilizerHom A B G p q).toFun := by
  intro σ
  let φ := nativeResidueAutomorphismRingEquiv A B p q σ
  have hφ := nativeResidueAutomorphismRingEquiv_comp_coefficient A B p q σ
  obtain ⟨g, hg⟩ := profiniteInvariant_exists_residue_lift A (B := B) (G := G) q φ hφ
  let d : nativeResidueStabilizer B G q := nativeResidueStabilizerOfEquation q φ g hg
  refine ⟨d, ?_⟩
  apply nativeResidueAutomorphismRingEquiv_injective A B p q
  apply RingEquiv.ext
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h := (nativeResidueStabilizerHom_apply_coefficient A B G p q d b).trans (hg b)
  simpa only [RingHom.toFun_eq_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using h

/-- The kernel of the actual residue action, included in the original group,
is exactly the original inertia subgroup. This is the native kernel theorem. -/
theorem nativeResidueStabilizerHom_map_ker
    (A : Type u) (B G : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (p : Ideal A) (q : Ideal B) [q.LiesOver p] :
    (nativeResidueStabilizerHom A B G p q).ker.map
        (nativeResidueStabilizerInclusion B G q) = q.inertia G :=
  Ideal.Quotient.map_ker_stabilizer_subtype q p G

end EtaleFundamentalGroups.Inertia
