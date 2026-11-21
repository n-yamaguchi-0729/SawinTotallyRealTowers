/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormComparison
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusTransport
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainFiniteReciprocity

/-!
# Comparing finite reciprocity through fixed coefficients

The two prime-norm formulas compute reciprocity using the same positive
Frobenius lift and corresponding prime elements in its fixed fields.
-/

@[expose] public section

open CyclicCohomology KummerTheory

noncomputable section

namespace ClassFormation

universe u v a b

variable {G : Type u} {G' : Type v} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
  (A : Rep.{a} ℤ G) (A' : Rep.{b} ℤ G')
  (H : FiniteAbstractField G) (H' : FiniteAbstractField G')
  (J : FiniteGaloisSubextension H.field) (J' : FiniteGaloisSubextension H'.field)
  (e : H.field.toSubgroup ≃ₜ* H'.field.toSubgroup)
  (he : ∀ s : H.field.toSubgroup, s.1 ∈ J.field.toSubgroup ↔ (e s).1 ∈ J'.field.toSubgroup)
  (f : A.V →+ A'.V)
  (hf : ∀ (s : H.field.toSubgroup) (x : A.V), f (A.ρ s.1 x) = A'.ρ (e s).1 (f x))

local instance : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field J.field J.below) :=
  J.finite

local instance : Finite (H'.field.toSubgroup ⧸ extensionSubgroup H'.field J'.field J'.below) :=
  J'.finite

/-- On the lower fixed group the coefficient map is given by equivariance. -/
def finiteReciprocityBaseCoefficientsMap :
    ambientFixedAddSubgroup A H.field →+ ambientFixedAddSubgroup A' H'.field :=
  relativeFixedCoefficientsMap (hJ'H' := le_rfl) (e := e.toMulEquiv)
    (he := fun s => iff_of_true s.2 (e s).2) A A' f hf

/-- The corresponding coefficient comparison descends to the actual finite
norm quotient because it commutes with the relative norm. -/
def finiteNormQuotientTransport :
    FiniteNormQuotient A H.field J.field J.below →+
      FiniteNormQuotient A' H'.field J'.field J'.below := by
  let fH := finiteReciprocityBaseCoefficientsMap A A' H H' e f hf
  let fJ := relativeFixedCoefficientsMap
    (hJ'H' := J'.below) (e := e.toMulEquiv) (he := he) A A' f hf
  refine finiteNormQuotientLift A H.field J.field J.below
    ((finiteNormClassHom A' H'.field J'.field J'.below).comp fH) ?_
  rintro _ ⟨x, rfl⟩
  change finiteNormClass A' H'.field J'.field J'.below
    (fH (relativeNorm A H.field J.field J.below x)) = 0
  rw [finiteNormClass_eq_zero_iff]
  exact ⟨fJ x, Subtype.ext (relativeNorm_map_of_equivariant J.below J'.below e.toMulEquiv he
    A A' f hf x (fJ x) rfl).symm⟩

/-- Quotient transport keeps the same fixed coefficient representative. -/
@[simp]
theorem finiteNormQuotientTransport_finiteNormClass (x : ambientFixedAddSubgroup A H.field) :
    finiteNormQuotientTransport A A' H H' J J' e he f hf
        (finiteNormClass A H.field J.field J.below x) =
      finiteNormClass A' H'.field J'.field J'.below
        (finiteReciprocityBaseCoefficientsMap A A' H H' e f hf x) :=
  rfl

variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [IsTopologicalGroup G'] [CompactSpace G'] [T2Space G'] [TotallyDisconnectedSpace G']
  (D : DegreeData G) (D' : DegreeData G')
  (v : ValuationData D A) (v' : ValuationData D' A')

/-- If corresponding finite fixed coefficients have the same valuation
and the lower group maps have the same positive degree, the actual finite
reciprocity maps agree after transport. -/
theorem finiteReciprocityHom_transport
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (hAxiom' : v'.SatisfiesUnramifiedUnitCohomology D')
    (hd : ∀ s : H.field.toSubgroup,
      D.normalizedDegree (H.toFiniteResidueAbstractField D) s =
        D'.normalizedDegree (H'.toFiniteResidueAbstractField D') (e s))
    (hv : ∀ (S : FiniteAbstractField G) (S' : FiniteAbstractField G')
      (_hSH : S.field.toSubgroup ≤ H.field.toSubgroup)
      (_hS'H' : S'.field.toSubgroup ≤ H'.field.toSubgroup)
      (_hS : ∀ s : H.field.toSubgroup,
        s.1 ∈ S.field.toSubgroup ↔ (e s).1 ∈ S'.field.toSubgroup)
      (x : ambientFixedAddSubgroup A S.field) (x' : ambientFixedAddSubgroup A' S'.field),
      f x.1 = x'.1 → (v.valuationAt S x : ZHat) = (v'.valuationAt S' x' : ZHat))
    (q : H.field.toSubgroup ⧸ extensionSubgroup H.field J.field J.below) :
    finiteNormQuotientTransport A A' H H' J J' e he f hf
        (D.finiteReciprocityHom A v hAxiom H J.field J.below (Additive.ofMul q)) =
      D'.finiteReciprocityHom A' v' hAxiom' H' J'.field J'.below (Additive.ofMul
        (relativeCosetEquivOfMulEquiv J.below J'.below e.toMulEquiv he q)) := by
  let R := H.toFiniteResidueAbstractField D
  let R' := H'.toFiniteResidueAbstractField D'
  let : (extensionSubgroup R.field J.field J.below).Normal := J.normal
  let : (extensionSubgroup R'.field J'.field J'.below).Normal := J'.normal
  let : Finite (R.field.toSubgroup ⧸ extensionSubgroup R.field J.field J.below) := J.finite
  let : Finite (R'.field.toSubgroup ⧸ extensionSubgroup R'.field J'.field J'.below) := J'.finite
  obtain ⟨σ, hσ⟩ := D.frobeniusRestriction_surjective R J.field J.below q
  let σ' := D.transportFrobenius D' R R' J.field J'.field J.below J'.below e he hd σ
  have hσ' : D'.frobeniusRestriction R' J'.field J'.below σ' =
      relativeCosetEquivOfMulEquiv J.below J'.below e.toMulEquiv he q := by
    rw [D.transportFrobenius_restriction, hσ]
  let S : FiniteAbstractField G := ⟨D.frobeniusFixedField R J.field J.below σ,
    D.frobeniusFixedField_absoluteFinite H J.field J.below σ⟩
  let S' : FiniteAbstractField G' := ⟨D'.frobeniusFixedField R' J'.field J'.below σ',
    D'.frobeniusFixedField_absoluteFinite H' J'.field J'.below σ'⟩
  let hSH : S.field.toSubgroup ≤ H.field.toSubgroup :=
    D.frobeniusFixedField_le R J.field J.below σ
  let hS'H' : S'.field.toSubgroup ≤ H'.field.toSubgroup :=
    D'.frobeniusFixedField_le R' J'.field J'.below σ'
  have hS := D.transportFrobenius_mem_fixedField_iff
    D' R R' J.field J'.field J.below J'.below e he hd σ
  let : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field S.field hSH) :=
    D.frobeniusFixedField_finite R J.field J.below σ
  let : Finite (H'.field.toSubgroup ⧸ extensionSubgroup H'.field S'.field hS'H') :=
    D'.frobeniusFixedField_finite R' J'.field J'.below σ'
  obtain ⟨π, hπ⟩ := v.normalizedValuation_surjective S v.oneValue
  let π' := relativeFixedCoefficientsMap
    (hJ'H' := hS'H') (e := e.toMulEquiv) (he := hS) A A' f hf π
  have hπ' : v'.IsPrimeElement S' π' := by
    apply Subtype.ext
    change (v'.valuationAt S' π' : ZHat) = (v'.oneValue : ZHat)
    exact (hv S S' hSH hS'H' hS π π' rfl).symm.trans (congrArg Subtype.val hπ)
  have hLeft := D.finiteReciprocityHom_apply_eq_primeNormClass A v hAxiom H J.field J.below
    (Additive.ofMul q) σ hσ π hπ
  have hRight := D'.finiteReciprocityHom_apply_eq_primeNormClass A' v' hAxiom' H' J'.field J'.below
    (Additive.ofMul (relativeCosetEquivOfMulEquiv J.below J'.below e.toMulEquiv he q))
    σ' hσ' π' hπ'
  change D.finiteReciprocityHom A v hAxiom H J.field J.below (Additive.ofMul q) =
    finiteNormClass A H.field J.field J.below (relativeNorm A H.field S.field hSH π) at hLeft
  change D'.finiteReciprocityHom A' v' hAxiom' H' J'.field J'.below
      (Additive.ofMul (relativeCosetEquivOfMulEquiv J.below J'.below e.toMulEquiv he q)) =
    finiteNormClass A' H'.field J'.field J'.below
      (relativeNorm A' H'.field S'.field hS'H' π') at hRight
  rw [hLeft, hRight, finiteNormQuotientTransport_finiteNormClass]
  refine congrArg (finiteNormClass A' H'.field J'.field J'.below) (Subtype.ext ?_)
  exact relativeNorm_map_of_equivariant hSH hS'H' e.toMulEquiv hS A A' f hf π π' rfl

end ClassFormation
