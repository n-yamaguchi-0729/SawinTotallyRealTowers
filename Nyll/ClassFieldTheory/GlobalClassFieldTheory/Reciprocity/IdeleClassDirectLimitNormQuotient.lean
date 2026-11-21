/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitAbstractFixedField
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitStandardNorm
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Nyll.GaloisCohomology.Kummer.Abstract.KummerDelta

/-!
# Finite norm quotients for rational fixed fields

The abstract finite norm subgroup and quotient are identified with the
ordinary idele-class norm range and quotient of the actual fixed-field extension.
-/



@[expose] public section

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

open scoped NumberField

attribute [local instance]
  rationalAbstractFixedFieldFiniteDimensional

/-- The additive idele class group of the actual upper relative fixed field. -/
noncomputable abbrev rationalRelativeFixedFieldIdeleClassAdditiveType
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] : Type :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField E :=
    NumberField.of_module_finite ℚ E
  Additive (IdeleClassGroup E)

/-- The additive quotient of the actual lower idele class group by the norm
range from the upper field. -/
noncomputable abbrev rationalOrdinaryNormQuotientAdditiveType
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] : Type :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  letI : NumberField F :=
    NumberField.of_module_finite ℚ F
  letI : NumberField E :=
    NumberField.of_module_finite ℚ E
  Additive
    (IdeleClassGroup F ⧸ (NumberField.IdeleClassGroup.norm F E).range)

/-- Quotienting an abelian group commutes with passing to additive notation. -/
noncomputable def additiveQuotientEquiv
    {G : Type*} [CommGroup G] (H : Subgroup G) :
    (Additive G ⧸ H.toAddSubgroup) ≃+
      Additive (G ⧸ H) := by
  let normAdd : Additive G →+ Additive (G ⧸ H) :=
    MonoidHom.toAdditive (QuotientGroup.mk' H)
  let T := normAdd.ker
  have hT : H.toAddSubgroup = T := by
    ext g
    change
      Additive.toMul g ∈ H ↔
        QuotientGroup.mk' H (Additive.toMul g) = 1
    exact (QuotientGroup.eq_one_iff (Additive.toMul g)).symm
  have hsurjective : Function.Surjective normAdd := by
    intro q
    obtain ⟨g, hg⟩ :=
      QuotientGroup.mk'_surjective H (Additive.toMul q)
    refine ⟨Additive.ofMul g, ?_⟩
    apply Additive.toMul.injective
    change QuotientGroup.mk' H g = Additive.toMul q
    exact hg
  exact (QuotientAddGroup.quotientAddEquivOfEq hT).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      normAdd hsurjective)

private theorem map_addRange_eq_monoidRange_toAddSubgroup_of_equiv
    {U A G H : Type*}
    [AddCommGroup U] [AddCommGroup A] [CommGroup G] [CommGroup H]
    (f : U →+ A) (g : G →* H)
    (eU : Additive G ≃+ U) (eA : Additive H ≃+ A)
    (hcompat : ∀ c : Additive G,
      eA.symm (f (eU c)) =
        Additive.ofMul (g (Additive.toMul c))) :
    f.range.map eA.symm.toAddMonoidHom = g.range.toAddSubgroup := by
  ext y
  constructor
  · intro hy
    obtain ⟨n, ⟨u, hu⟩, hny⟩ := hy
    let c : Additive G := eU.symm u
    refine ⟨Additive.toMul c, ?_⟩
    apply Additive.ofMul.injective
    exact
      (hcompat c).symm.trans
        ((congrArg (fun z => eA.symm (f z))
            (eU.apply_symm_apply u)).trans
          ((congrArg eA.symm hu).trans hny))
  · intro hy
    obtain ⟨d, hd⟩ := hy
    let c : Additive G := Additive.ofMul d
    let u : U := eU c
    exact
      ⟨f u, ⟨u, rfl⟩,
        (hcompat c).trans (congrArg Additive.ofMul hd)⟩

section Standard

universe u

variable (k : Type u) [Field k] [NumberField k]
    (H J : ClosedSubgroup (SeparableClosure k ≃ₐ[k] SeparableClosure k))
    (hJH : J.toSubgroup ≤ H.toSubgroup)
    (hnormal : (extensionSubgroup H J hJH).Normal)
    [FiniteDimensional k (abstractFixedField k (SeparableClosure k) H)]
    [FiniteDimensional k (abstractFixedField k (SeparableClosure k) J)]
    [Finite (H.toSubgroup ⧸ extensionSubgroup H J hJH)]

attribute [local instance] abstractRelativeFixedFieldNumberField

local notation "C[" F "]" => NumberField.IdeleClassGroup (𝓞 F) F

include hnormal in
/-- The fixed-part comparison sends the finite norm subgroup to the range of
the standard norm on the same two fixed fields. -/
theorem map_finiteNormSubgroup_eq_standardIdeleClassNormRange :
    let F := abstractFixedField k (SeparableClosure k) H
    let E := abstractRelativeFixedField k (SeparableClosure k) hJH
    let n := NumberField.IdeleClassGroup.norm F E
    (finiteNormSubgroup (ideleClassRepresentation k) H J hJH).map
        (abstractFixedFieldIdeleClassEquivFixed k H).symm.toAddMonoidHom =
      n.range.toAddSubgroup := by
  intro F E n
  let : CommGroup C[F] :=
    QuotientGroup.Quotient.commGroup (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)
  let : CommGroup C[E] :=
    QuotientGroup.Quotient.commGroup (NumberField.IdeleGroup.principalSubgroup (𝓞 E) E)
  let eH := abstractFixedFieldIdeleClassEquivFixed k H
  let eJ := abstractRelativeFixedFieldIdeleClassEquivFixed k H J hJH
  let N := relativeNorm (ideleClassRepresentation k) H J hJH
  have hc (c : Additive (NumberField.IdeleClassGroup (𝓞 E) E)) :
      eH.symm (N (eJ c)) = Additive.ofMul (n c.toMul) := by
    have h := abstractFixedFieldIdeleClassEquivFixed_norm k H J hJH hnormal c.toMul
    exact (congrArg eH.symm h).trans (eH.symm_apply_apply _)
  exact map_addRange_eq_monoidRange_toAddSubgroup_of_equiv
    (G := C[E]) (H := C[F]) N n eJ eH hc

include hnormal in
/-- The finite norm quotient of the number-field formation is the standard
idele-class quotient by the actual norm from the upper fixed field. -/
noncomputable def finiteNormQuotientEquivStandardIdeleClassNormQuotient :
    let F := abstractFixedField k (SeparableClosure k) H
    let E := abstractRelativeFixedField k (SeparableClosure k) hJH
    let n := NumberField.IdeleClassGroup.norm F E
    FiniteNormQuotient (ideleClassRepresentation k) H J hJH ≃+
      Additive (NumberField.IdeleClassGroup (𝓞 F) F ⧸ n.range) := by
  intro F E n
  let : CommGroup C[F] :=
    QuotientGroup.Quotient.commGroup (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)
  let eH := abstractFixedFieldIdeleClassEquivFixed k H
  let N := finiteNormSubgroup (ideleClassRepresentation k) H J hJH
  have hnorm : N.map eH.symm.toAddMonoidHom = n.range.toAddSubgroup :=
    map_finiteNormSubgroup_eq_standardIdeleClassNormRange k H J hJH hnormal
  let eN : (KummerTheory.ambientFixedAddSubgroup (ideleClassRepresentation k) H ⧸ N) ≃+
      (Additive (NumberField.IdeleClassGroup (𝓞 F) F) ⧸ n.range.toAddSubgroup) :=
    QuotientAddGroup.congr N n.range.toAddSubgroup eH.symm hnorm
  let eQ : (Additive (NumberField.IdeleClassGroup (𝓞 F) F) ⧸ n.range.toAddSubgroup) ≃+
      Additive (NumberField.IdeleClassGroup (𝓞 F) F ⧸ n.range) :=
    additiveQuotientEquiv (G := C[F]) n.range
  exact (finiteNormQuotientConcreteEquiv (ideleClassRepresentation k) H J hJH).trans (eN.trans eQ)

/-- The finite norm quotient comparison uses the actual lower-field representative. -/
theorem finiteNormQuotientEquivStandardIdeleClassNormQuotient_finiteNormClass
    (a : KummerTheory.ambientFixedAddSubgroup (ideleClassRepresentation k) H) :
    let F := abstractFixedField k (SeparableClosure k) H
    let E := abstractRelativeFixedField k (SeparableClosure k) hJH
    let n := NumberField.IdeleClassGroup.norm F E
    finiteNormQuotientEquivStandardIdeleClassNormQuotient k H J hJH hnormal
        (finiteNormClass (ideleClassRepresentation k) H J hJH a) =
      Additive.ofMul (QuotientGroup.mk' n.range
        ((abstractFixedFieldIdeleClassEquivFixed k H).symm a).toMul) := by
  intro F E n
  simp only [finiteNormQuotientEquivStandardIdeleClassNormQuotient]
  rfl

end Standard

/-- The ordinary idele class group of the upper fixed field is the
corresponding fixed part of the rational absolute idele-class representation
for any finite extension of abstract fixed fields. -/
noncomputable def
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    rationalRelativeFixedFieldIdeleClassAdditiveType
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK ≃+
      KummerTheory.ambientFixedAddSubgroup
        (ideleClassRepresentation ℚ) L := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K
  let E :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField E :=
    NumberField.of_module_finite ℚ E
  change Additive (IdeleClassGroup E) ≃+
    KummerTheory.ambientFixedAddSubgroup
      (ideleClassRepresentation ℚ) L
  exact
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK

/-- For a finite Galois pair of abstract fixed fields, the direct upper
fixed-part comparison intertwines the class-formation relative norm with
the ordinary idele-class norm. -/
theorem
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_relativeNorm
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : rationalRelativeFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    let := hnormal
    let : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K hKfinite
    let : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    let : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    let : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
    let : NumberField F :=
      NumberField.of_module_finite ℚ F
    let : NumberField E :=
      NumberField.of_module_finite ℚ E
    let : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        ℚ (SeparableClosure ℚ) K L hLK hnormal
    relativeNorm (ideleClassRepresentation ℚ) K L hLK
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed K L hLK c) =
      rationalAbstractFixedFieldIdeleClassEquivFixed K
        (Additive.ofMul
          (NumberField.IdeleClassGroup.norm F E c.toMul)) := by
  intro F E hnormalInstance hFfinite hFEfinite htower hEfinite hFnumberField hEnumberField hGalois
  let : FiniteDimensional ℚ (abstractFixedField ℚ (SeparableClosure ℚ) L) :=
    inferInstanceAs (FiniteDimensional ℚ E)
  exact abstractFixedFieldIdeleClassEquivFixed_norm ℚ K L hLK hnormal c.toMul

/-- The fixed-field comparison carries the abstract finite norm subgroup
exactly to the ordinary idele-class norm range of the actual fixed fields. -/
theorem
    map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    let := hnormal
    let : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    let : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    let : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    let : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    let : NumberField F := NumberField.of_module_finite ℚ F
    let : NumberField E := NumberField.of_module_finite ℚ E
    let : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        ℚ (SeparableClosure ℚ) K L hLK hnormal
    (finiteNormSubgroup (ideleClassRepresentation ℚ) K L hLK).map
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          K).symm.toAddMonoidHom =
      (NumberField.IdeleClassGroup.norm F E).range.toAddSubgroup := by
  intro F E sharedOwner3 sharedOwner4 sharedOwner5 sharedOwner6 sharedOwner7 sharedOwner8
    sharedOwner9 sharedOwner10
  let : FiniteDimensional ℚ (abstractFixedField ℚ (SeparableClosure ℚ) L) :=
    inferInstanceAs (FiniteDimensional ℚ E)
  exact map_finiteNormSubgroup_eq_standardIdeleClassNormRange ℚ K L hLK hnormal

/-- The finite norm quotient in the rational absolute representation is
the ordinary idele-class quotient by the actual norm subgroup of the
fixed-field extension. -/
noncomputable def
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    FiniteNormQuotient (ideleClassRepresentation ℚ) K L hLK ≃+
      rationalOrdinaryNormQuotientAdditiveType K L hLK := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K hKfinite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let : IsScalarTower ℚ F E := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  let : FiniteDimensional ℚ (abstractFixedField ℚ (SeparableClosure ℚ) L) :=
    inferInstanceAs (FiniteDimensional ℚ E)
  let : NumberField F := NumberField.of_module_finite ℚ F
  let : NumberField E := NumberField.of_module_finite ℚ E
  exact finiteNormQuotientEquivStandardIdeleClassNormQuotient ℚ K L hLK hnormal

/-- The fixed-field norm-quotient comparison sends an abstract finite
norm class to the ordinary idele class of the transported
representative. -/
@[simp]
theorem
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      (ideleClassRepresentation ℚ) K) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    let := hnormal
    let : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    let : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    let : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    let : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    let : NumberField F := NumberField.of_module_finite ℚ F
    let : NumberField E := NumberField.of_module_finite ℚ E
    let : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        ℚ (SeparableClosure ℚ) K L hLK hnormal
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
        K L hLK hnormal
        (finiteNormClass (ideleClassRepresentation ℚ)
          K L hLK a) =
      Additive.ofMul
        (QuotientGroup.mk' (NumberField.IdeleClassGroup.norm F E).range
          (Additive.toMul
            ((rationalAbstractFixedFieldIdeleClassEquivFixed K).symm a))) := by
  intro F E hnormalInstance hFfinite hFEfinite htower hEfinite
    hFnumberField hEnumberField hGalois
  let : FiniteDimensional ℚ (abstractFixedField ℚ (SeparableClosure ℚ) L) :=
    inferInstanceAs (FiniteDimensional ℚ E)
  exact finiteNormQuotientEquivStandardIdeleClassNormQuotient_finiteNormClass ℚ K L hLK hnormal a

end Reciprocity
end GlobalClassFieldTheory
