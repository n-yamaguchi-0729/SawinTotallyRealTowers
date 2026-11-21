/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.AbstractFixedFieldGlobalNormResidue
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitExtensionAction
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityCanonical

/-! # Independence of the rational embedding in finite global norm residue -/

@[expose] public section

noncomputable section

open scoped IsMulCommutative NumberField
open NumberField ClassFormation CyclicCohomology RamificationTheory LocalClassFieldTheory
open KummerTheory

universe u v

namespace GlobalClassFieldTheory.Reciprocity

local notation "Ω" => SeparableClosure ℚ
local notation "Γ" => Gal(Ω/ℚ)

private theorem conjugateClosedFixingSubgroup_of_embedding_apply
    {F : Type u} [Field F] [NumberField F] (i j : F →ₐ[ℚ] Ω) (s : Γ)
    (hs : ∀ x : F, s (j x) = i x) :
    conjugateClosedSubgroup (closedFixingSubgroup ℚ Ω i.fieldRange) s =
      closedFixingSubgroup ℚ Ω j.fieldRange := by
  ext τ
  change τ ∈ conjugateClosedSubgroup (closedFixingSubgroup ℚ Ω i.fieldRange) s ↔
    τ ∈ closedFixingSubgroup ℚ Ω j.fieldRange
  rw [conjugateClosedSubgroup_mem]
  change s * τ * s⁻¹ ∈ i.fieldRange.fixingSubgroup ↔ τ ∈ j.fieldRange.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  have hs' (x : F) : s.symm (i x) = j x := by rw [← hs x, s.symm_apply_apply]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := hy
    have hx := h (i x) ⟨x, rfl⟩
    change s (τ (s.symm (i x))) = i x at hx
    rw [hs' x, ← hs x] at hx
    exact s.injective hx
  · intro h y hy
    obtain ⟨x, rfl⟩ := hy
    change s (τ (s.symm (i x))) = i x
    rw [hs' x, h (j x) ⟨x, rfl⟩, hs x]

variable (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

private theorem numberFieldEmbeddedIdeleClassEquivAmbientFixed_conjugate
    (i j : L →ₐ[ℚ] Ω) (s : Γ) (hs : ∀ x : L, s (j x) = i x) (c : IdeleClassGroup K) :
    (ideleClassRepresentation ℚ).ρ s⁻¹
        (numberFieldEmbeddedIdeleClassEquivAmbientFixed K L i (Additive.ofMul c)).1 =
      (numberFieldEmbeddedIdeleClassEquivAmbientFixed K L j (Additive.ofMul c)).1 := by
  let H := numberFieldEmbeddedBaseSubgroup K L i
  let H' := numberFieldEmbeddedBaseSubgroup K L j
  let eH := numberFieldEmbeddedAbstractBaseFieldEquiv K L i
  let eH' := numberFieldEmbeddedAbstractBaseFieldEquiv K L j
  let e := eH.symm.trans eH'
  let : Finite ((baseField Γ).toSubgroup ⧸
      extensionSubgroup (baseField Γ) H (le_baseField H)) :=
    (numberFieldEmbeddedFiniteAbstractField K L i).finite
  let : Finite ((baseField Γ).toSubgroup ⧸
      extensionSubgroup (baseField Γ) H' (le_baseField H')) :=
    (numberFieldEmbeddedFiniteAbstractField K L j).finite
  let : FiniteDimensional ℚ (abstractFixedField ℚ Ω H) := eH.toLinearEquiv.finiteDimensional
  let : FiniteDimensional ℚ (abstractFixedField ℚ Ω H') := eH'.toLinearEquiv.finiteDimensional
  have he (x : abstractFixedField ℚ Ω H) : (e x : Ω) = s.symm (x : Ω) := by
    obtain ⟨a, rfl⟩ := eH.surjective x
    change (eH' (eH.symm (eH a)) : Ω) = s.symm (eH a : Ω)
    rw [eH.symm_apply_apply]
    change j (algebraMap K L a) = s.symm (i (algebraMap K L a))
    exact (s.symm_apply_apply _).symm.trans (congrArg s.symm (hs _))
  have hcomp : eH.trans e = eH' := by
    apply AlgEquiv.ext
    intro a
    change eH' (eH.symm (eH a)) = eH' a
    rw [eH.symm_apply_apply]
  have hclass : ideleClassCongr e (ideleClassCongr eH c) = ideleClassCongr eH' c := by
    rw [ideleClassCongr_trans, hcomp]
  let x := ideleClassCongr eH c
  let y := ideleClassCongr eH' c
  let rho := (ideleClassRepresentation ℚ).ρ s.symm
  have hLeft := rationalAbstractFixedFieldIdeleClassEquivFixed_coe H (Additive.ofMul x)
  have hRight := rationalAbstractFixedFieldIdeleClassEquivFixed_coe H' (Additive.ofMul y)
  have hAction := rationalIdeleClassEquivFixed_ambientAlgEquiv s.symm e he x
  let f (z : IdeleClassGroup (abstractFixedField ℚ Ω H')) :=
    (rationalIdeleClassEquivFixed (abstractFixedField ℚ Ω H') (Additive.ofMul z)).1
  exact (congrArg rho hLeft).trans (hAction.trans ((congrArg f hclass).trans hRight.symm))

variable [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Changing the common rational embedding leaves the finite global norm-residue map unchanged. -/
theorem globalNormResidueMonoidHomOfEmbedding_eq (i j : L →ₐ[ℚ] Ω) :
    globalNormResidueMonoidHomOfEmbedding K L i =
      globalNormResidueMonoidHomOfEmbedding K L j := by
  apply MonoidHom.ext
  intro c
  let s := numberFieldEmbeddingComparisonAutomorphism j i
  have hs (x : L) : s (j x) = i x := numberFieldEmbeddingComparisonAutomorphism_apply j i x
  let Hi := numberFieldEmbeddedFiniteAbstractField K L i
  let Hj := numberFieldEmbeddedFiniteAbstractField K L j
  let Pi := numberFieldEmbeddedFiniteGaloisSubextension K L i
  let Pj := numberFieldEmbeddedFiniteGaloisSubextension K L j
  let Hs := Hi.conjugate s
  let Ls := conjugateClosedSubgroup Pi.field s
  let hC := conjugateClosedSubgroup_mono Pi.below s
  have hH : Hs.field = Hj.field :=
    conjugateClosedFixingSubgroup_of_embedding_apply
      (numberFieldEmbeddedLowerEmbedding K L i)
      (numberFieldEmbeddedLowerEmbedding K L j) s (fun x => hs (algebraMap K L x))
  have hL : Ls = Pj.field := conjugateClosedFixingSubgroup_of_embedding_apply i j s hs
  let : (extensionSubgroup Hi.field Pi.field Pi.below).Normal := Pi.normal
  let : (extensionSubgroup Hj.field Pj.field Pj.below).Normal := Pj.normal
  let : Finite (Hi.field.toSubgroup ⧸ extensionSubgroup Hi.field Pi.field Pi.below) := Pi.finite
  let : Finite (Hj.field.toSubgroup ⧸ extensionSubgroup Hj.field Pj.field Pj.below) := Pj.finite
  let : (extensionSubgroup Hs.field Ls hC).Normal :=
    conjugateExtension_normal Hi.field Pi.field Pi.below s
  let : Finite (Hs.field.toSubgroup ⧸ extensionSubgroup Hs.field Ls hC) :=
    finite_conjugateExtension Hi.field Pi.field Pi.below s
  let : Finite ((baseField Γ).toSubgroup ⧸
      extensionSubgroup (baseField Γ) Hs.field (le_baseField Hs.field)) := Hs.finite
  let : Finite ((baseField Γ).toSubgroup ⧸
      extensionSubgroup (baseField Γ) Hj.field (le_baseField Hj.field)) := Hj.finite
  let A := (ideleClassRepresentation ℚ)
  let D := rationalCyclotomicDegreeData
  let v := rationalCyclotomicIdeleClassValuationData
  let hcf := (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ)
  let Xi := numberFieldEmbeddedIdeleClassEquivAmbientFixed K L i (Additive.ofMul c)
  let Xj := numberFieldEmbeddedIdeleClassEquivAmbientFixed K L j (Additive.ofMul c)
  let xi := finiteNormClass A Hi.field Pi.field Pi.below Xi
  let xj := finiteNormClass A Hj.field Pj.field Pj.below Xj
  let qC := finiteReciprocityNaturalityConjugation Hi.field Pi.field Pi.below s
  let qT := extensionQuotientCongr hC Pj.below hH hL
  let bC := finiteReciprocityNaturalityConjugationNormMap A Hi.field Pi.field Pi.below s
  let H₀ := conjugateClosedSubgroup (numberFieldEmbeddedBaseSubgroup K L i) s
  let : Finite (H₀.toSubgroup ⧸ extensionSubgroup H₀ Ls hC) :=
    finite_conjugateExtension Hi.field Pi.field Pi.below s
  let bT := finiteNormQuotientCongr A hC Pj.below hH hL
  let Ri := D.normResidueSymbol A v hcf Hi Pi
  let Rj := D.normResidueSymbol A v hcf Hj Pj
  have hCoef : AddEquiv.addSubgroupCongr (congrArg (ambientFixedAddSubgroup A) hH)
      (conjugateFixedElement A Hi.field s Xi) = Xj :=
    Subtype.ext (numberFieldEmbeddedIdeleClassEquivAmbientFixed_conjugate K L i j s hs c)
  have hClass : bT (bC xi) = xj := calc
    _ = bT (finiteNormClass A Hs.field Ls hC (conjugateFixedElement A Hi.field s Xi)) :=
      congrArg bT (finiteReciprocityNaturalityConjugationNormMap_finiteNormClass
        A Hi.field Pi.field Pi.below s Xi)
    _ = _ := (finiteNormQuotientCongr_finiteNormClass A hC Pj.below hH hL _).trans
      (congrArg (finiteNormClass A Hj.field Pj.field Pj.below) hCoef)
  have hraw := DFunLike.congr_fun
    (D.normResidueNaturality_conjugation A v hcf Hi Pi.field Pi.below s) xi
  have hTransport := DFunLike.congr_fun
    (normResidueSymbol_congr D A v hcf Hs.field Ls Hj.field Pj.field hC Pj.below hH hL)
    (bC xi)
  have hSymbol : (MulEquiv.toAdditive qT.abelianizationCongr)
      (Additive.ofMul (qC.abelianizationCongr (Ri xi).toMul)) = Rj xj :=
    (congrArg (MulEquiv.toAdditive qT.abelianizationCongr) hraw).trans
      (hTransport.trans (congrArg Rj hClass))
  let qi := numberFieldEmbeddedExtensionQuotientEquivGaloisGroup K L i
  let qj := numberFieldEmbeddedExtensionQuotientEquivGaloisGroup K L j
  have hGalois (q : Pi.extensionQuotient) : qj (qT (qC q)) = qi q := by
    obtain ⟨g, rfl⟩ := Pi.extensionQuotientMk_surjective q
    let g' := MulEquiv.subgroupCongr (congrArg (fun H : ClosedSubgroup Γ => H.toSubgroup) hH)
      (conjugateSubgroupEquiv Hi.field s g)
    have hq : qT (qC (QuotientGroup.mk g)) = QuotientGroup.mk g' :=
      (congrArg qT (finiteReciprocityNaturalityConjugation_mk
        Hi.field Pi.field Pi.below s g)).trans (extensionQuotientCongr_mk hC Pj.below hH hL _)
    refine (congrArg qj hq).trans ?_
    apply AlgEquiv.ext
    intro x
    apply j.injective
    have hi : i (qi (QuotientGroup.mk g) x) = g.1 (i x) := by
      let : Algebra K Ω := numberFieldEmbeddedSeparableClosureAlgebra K L i
      exact ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply ℚ K L i
        (numberFieldEmbeddedSeparableClosureEquiv K L i) g x
    have hj : j (qj (QuotientGroup.mk g') x) = g'.1 (j x) := by
      let : Algebra K Ω := numberFieldEmbeddedSeparableClosureAlgebra K L j
      exact ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply ℚ K L j
        (numberFieldEmbeddedSeparableClosureEquiv K L j) g' x
    calc
      j (qj (QuotientGroup.mk g') x) = g'.1 (j x) := hj
      _ = s.symm (g.1 (s (j x))) := rfl
      _ = s.symm (g.1 (i x)) := congrArg (fun z => s.symm (g.1 z)) (hs x)
      _ = s.symm (i (qi (QuotientGroup.mk g) x)) := congrArg s.symm hi.symm
      _ = j (qi (QuotientGroup.mk g) x) :=
        (congrArg s.symm (hs _)).symm.trans (s.symm_apply_apply _)
  let gi := numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup K L i
  let gj := numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup K L j
  let e : Gal(L / K) ≃* Group.Abelianization Gal(L / K) := Group.Abelianization.equivOfComm
  have hGaloisAbelian (z : Group.Abelianization Pi.extensionQuotient) :
      gj (Additive.ofMul (qT.abelianizationCongr (qC.abelianizationCongr z))) =
        gi (Additive.ofMul z) := by
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
    change Additive.ofMul (e.symm (qj.abelianizationCongr
      (qT.abelianizationCongr (qC.abelianizationCongr (Group.Abelianization.of q))))) =
        Additive.ofMul (e.symm (qi.abelianizationCongr (Group.Abelianization.of q)))
    simp only [Group.abelianizationCongr_of]
    exact congrArg
      (fun r : Gal(L / K) => Additive.ofMul (e.symm (Group.Abelianization.of r))) (hGalois q)
  rw [globalNormResidueMonoidHomOfEmbedding_apply, globalNormResidueMonoidHomOfEmbedding_apply]
  apply Additive.toMul.injective
  change gi (Ri xi) = gj (Rj xj)
  exact (hGaloisAbelian (Ri xi).toMul).symm.trans (congrArg gj hSymbol)

/-- The ordinary finite global norm-residue map can be computed with any rational embedding. -/
theorem globalNormResidueMonoidHom_eq_ofEmbedding (j : L →ₐ[ℚ] Ω) :
    globalNormResidueMonoidHom K L = globalNormResidueMonoidHomOfEmbedding K L j :=
  (globalNormResidueMonoidHom_eq_ofEmbedding_standard K L).trans
    (globalNormResidueMonoidHomOfEmbedding_eq K L _ j)

end GlobalClassFieldTheory.Reciprocity
