/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
import Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LubinTateTransport
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardSubgroupIntersection
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormContainment
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupSurjectivity
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.NormTopology
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.LocalAbsoluteData
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization
import Nyll.GaloisCohomology.Cyclic.TateH0.NormImage
import Nyll.GaloisCohomology.Kummer.Abstract.KummerDelta
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence

/-!
# Equal-characteristic existence for local class field theory

The explicit Lubin--Tate level over the Laurent-series model is transported
to an arbitrary equal-characteristic local field.  Together with an
unramified extension, it supplies a finite Galois extension whose norm
subgroup lies in any prescribed open finite-index subgroup of `Kˣ`.
-/



noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open LubinTate.EqualCharacteristic

variable (K : Type) [Field K]

section LocalField

variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A transported equal-characteristic Lubin--Tate level whose norm subgroup
is contained in the prescribed uniformizer/principal-unit subgroup. -/
theorem exists_equalCharacteristicLubinTateFiniteGaloisExtension_normSubgroup_map_le
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (n : ℕ) (hn : 0 < n) :
    ∃ T : FiniteGaloisSubextension (intrinsicAbstractBase K),
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup := by
  let F := equalCharacteristicTargetLocalField K
  let hKres : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F (n - 1)
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ (n - 1)
  let : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ (n - 1)
  let : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ (n - 1)
  have hLT :
      localNormSubgroup K E ≤
        LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n := by
    simpa [equalCharacteristicTransportedLubinTateNormSubgroup, F, E] using
      (equalCharacteristicTransportedLubinTateNormSubgroup_le_of_pos
        K p ϖ hϖ n hn)
  exact
    exists_finiteGaloisExtension_normSubgroup_map_le_of_normSubgroup_le
      K E (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n) hLT

/-- The transported Lubin--Tate level retained as a named finite abelian
subextension of the fixed separable closure. -/
noncomputable def
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    FiniteAbelianSubextension (intrinsicAbstractBase K) := by
  let F := equalCharacteristicTargetLocalField K
  letI : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  letI : CharP K p := hKp
  letI : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  letI : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ m
  letI : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ m
  exact
    finiteAbelianAbstractExtensionOfEmbedding K E
      (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K E)

/-- The explicit transported Lubin--Tate level is base-linearly equivalent
to the concrete fixed field represented by its named finite abelian
subextension. -/
noncomputable def equalCharacteristicTransportedLubinTateFixedFieldEquiv
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F m
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
    E ≃ₐ[K]
      abstractFixedField K (SeparableClosure K)
        (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
          K p ϖ hϖ m).field := by
  let F := equalCharacteristicTargetLocalField K
  letI : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  letI : CharP K p := hKp
  letI : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  letI : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ m
  letI : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ m
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K E
  let T :=
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
      K p ϖ hϖ m
  have hfixed :
      abstractFixedField K (SeparableClosure K) T.field =
        finiteGaloisFieldRangeOfEmbedding K E i := by
    change
      IntermediateField.fixedField
          (finiteGaloisFieldRangeOfEmbedding K E i).fixingSubgroup =
        finiteGaloisFieldRangeOfEmbedding K E i
    exact
      InfiniteGalois.fixedField_fixingSubgroup
        (finiteGaloisFieldRangeOfEmbedding K E i)
  rw [hfixed]
  exact finiteGaloisFieldRangeEquivOfEmbedding K E i

/-- The named transported Lubin--Tate subextension retains the concrete norm
containment at level `m + 1`. -/
theorem
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension_normSubgroup_map_le
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let T :=
      equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
        K p ϖ hϖ m
    (T.normSubgroup (intrinsicAbsoluteUnits K)).map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
      (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1)).toAddSubgroup := by
  let F := equalCharacteristicTargetLocalField K
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  let : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ m
  let : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ m
  have hLT :
      localNormSubgroup K E ≤
        LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1) := by
    simpa [equalCharacteristicTransportedLubinTateNormSubgroup, F, E] using
      (equalCharacteristicTransportedLubinTateNormSubgroup_le_uniformizerPrincipalSubgroup
        K p ϖ hϖ m)
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K E
  let T :=
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
      K p ϖ hϖ m
  have hmap :
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
        additiveNormSubgroup K E := by
    simpa [T,
      equalCharacteristicTransportedLubinTateFiniteAbelianSubextension,
      i, F, E] using
      map_finiteAbelianAbstractExtension_normSubgroup_eq K E i
  change
    (T.normSubgroup (intrinsicAbsoluteUnits K)).map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
      (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1)).toAddSubgroup
  rw [hmap]
  intro x hx
  change Additive.toMul x ∈ LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1)
  apply hLT
  exact hx

/-- The transported equal-characteristic Lubin--Tate level, packaged as a
finite abelian subextension of the fixed separable closure. -/
theorem exists_equalCharacteristicLubinTateFiniteAbelianExtension_normSubgroup_map_le
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (n : ℕ) (hn : 0 < n) :
    ∃ T : FiniteAbelianSubextension (intrinsicAbstractBase K),
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup := by
  refine
    ⟨equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
        K p ϖ hϖ (n - 1), ?_⟩
  simpa [Nat.sub_add_cancel hn] using
    (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension_normSubgroup_map_le
      K p ϖ hϖ (n - 1))

/-- The named finite abelian standard compositum: its first factor is the
canonical degree-`d` unramified extension and its second factor is the
transported Lubin--Tate level indexed by `n - 1`, whose norm subgroup uses
the principal-unit level `n`. -/
noncomputable def equalCharacteristicStandardFiniteAbelianCompositum
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (d n : ℕ) (hd : 0 < d) :
    FiniteAbelianSubextension (intrinsicAbstractBase K) :=
  (localFiniteUnramifiedAbelianSubextension K d hd).compositum
    (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
      K p ϖ hϖ (n - 1))

/-- The concrete fixed field of the named standard compositum is the
compositum of its unramified and transported Lubin--Tate fixed fields. -/
theorem equalCharacteristicStandardFiniteAbelianCompositum_fixedField_eq_sup
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (d n : ℕ) (hd : 0 < d) :
    abstractFixedField K (SeparableClosure K)
        (equalCharacteristicStandardFiniteAbelianCompositum
          K p ϖ hϖ d n hd).field =
      abstractFixedField K (SeparableClosure K)
          (localFiniteUnramifiedAbelianSubextension K d hd).field ⊔
        abstractFixedField K (SeparableClosure K)
          (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
            K p ϖ hϖ (n - 1)).field := by
  simpa [equalCharacteristicStandardFiniteAbelianCompositum] using
    (finiteAbelianSubextension_compositum_fixedField K
      (localFiniteUnramifiedAbelianSubextension K d hd)
      (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
        K p ϖ hϖ (n - 1)))

/-- The ordinary norm subgroup of the named standard compositum is contained
in every overgroup of `⟨ϖ^d⟩ U^n`. -/
theorem
    equalCharacteristicStandardFiniteAbelianCompositum_nativeNormSubgroup_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (hd : 0 < d) (hn : 0 < n)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H) :
    finiteAbelianNormSubgroup K
        (equalCharacteristicStandardFiniteAbelianCompositum
          K p ϖ hϖ d n hd) ≤
      H := by
  let U := localFiniteUnramifiedAbelianSubextension K d hd
  let T :=
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
      K p ϖ hϖ (n - 1)
  have hUle :
      (U.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (unramifiedNormSubgroup K d).toAddSubgroup := by
    simpa [U] using
      localFiniteUnramifiedAbelianSubextension_normSubgroup_map_le
        K d hd
  have hTle :
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup := by
    simpa [T, Nat.sub_add_cancel hn] using
      (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension_normSubgroup_map_le
        K p ϖ hϖ (n - 1))
  have hP :
      (U.compositum T).normSubgroup (intrinsicAbsoluteUnits K) ≤
        H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom :=
    finiteAbelianCompositum_normSubgroup_le_of_standard
      K H ϖ d n hϖ hstandard U T hUle hTle
  simpa [equalCharacteristicStandardFiniteAbelianCompositum, U, T] using
    (finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map
      K (U.compositum T) H hP)

/-- The two finite abelian factors of the positive-characteristic standard
construction can be retained explicitly, together with their norm controls
and the native norm containment for their compositum. -/
theorem
    exists_equalCharacteristicStandardFiniteAbelianCompositum_nativeNormSubgroup_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (hd : 0 < d) (hn : 0 < n)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H) :
    ∃ U T : FiniteAbelianSubextension (intrinsicAbstractBase K),
      (U.normSubgroup (intrinsicAbsoluteUnits K)).map
            (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
          (unramifiedNormSubgroup K d).toAddSubgroup ∧
        (T.normSubgroup (intrinsicAbsoluteUnits K)).map
            (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
          (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup ∧
        finiteAbelianNormSubgroup K (U.compositum T) ≤ H := by
  obtain ⟨U, hUle⟩ :=
    exists_unramifiedFiniteAbelianExtension_normSubgroup_map_le K d hd
  obtain ⟨T, hTle⟩ :=
    exists_equalCharacteristicLubinTateFiniteAbelianExtension_normSubgroup_map_le
      K p ϖ hϖ n hn
  have hP :
      (U.compositum T).normSubgroup (intrinsicAbsoluteUnits K) ≤
        H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom :=
    finiteAbelianCompositum_normSubgroup_le_of_standard
      K H ϖ d n hϖ hstandard U T hUle hTle
  refine ⟨U, T, hUle, hTle, ?_⟩
  exact
    finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map
      K (U.compositum T) H hP

/-- A standard subgroup in positive characteristic is dominated by the norm
subgroup of an explicitly assembled finite abelian compositum: an unramified
factor controls the uniformizer exponent and a transported Lubin--Tate factor
controls the principal units. -/
theorem exists_equalCharacteristicStandardFiniteAbelianExtension_normSubgroup_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (hd : 0 < d) (hn : 0 < n)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H) :
    ∃ P : FiniteAbelianSubextension (intrinsicAbstractBase K),
      P.normSubgroup (intrinsicAbsoluteUnits K) ≤
        H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom := by
  obtain ⟨U, hUle⟩ :=
    exists_unramifiedFiniteAbelianExtension_normSubgroup_map_le K d hd
  obtain ⟨T, hTle⟩ :=
    exists_equalCharacteristicLubinTateFiniteAbelianExtension_normSubgroup_map_le
      K p ϖ hϖ n hn
  refine ⟨U.compositum T, ?_⟩
  exact
    finiteAbelianCompositum_normSubgroup_le_of_standard
      K H ϖ d n hϖ hstandard U T hUle hTle

/-- Native field-facing form of the preceding construction: the represented
finite abelian fixed field has ordinary norm subgroup contained in the
prescribed standard overgroup. -/
theorem exists_equalCharacteristicStandardFiniteAbelianNativeNormSubgroup_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (hd : 0 < d) (hn : 0 < n)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H) :
    ∃ P : FiniteAbelianSubextension (intrinsicAbstractBase K),
      finiteAbelianNormSubgroup K P ≤ H := by
  obtain ⟨P, hP⟩ :=
    exists_equalCharacteristicStandardFiniteAbelianExtension_normSubgroup_le
      K p H ϖ d n hϖ hd hn hstandard
  exact
    ⟨P,
      finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map
        K P H hP⟩

/-- In positive characteristic, every ordinary open finite-index subgroup of
`Kˣ` is open for the norm topology. -/
theorem openFiniteIndexSubgroup_isNormOpen_of_charP
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (H : Subgroup Kˣ) [H.FiniteIndex]
    (hH : IsOpen (H : Set Kˣ)) :
    let A := intrinsicAbsoluteUnits K
    let B := intrinsicAbstractBase K
    let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
    ClassFormation.IsNormOpen A B
      ((H.toAddSubgroup.map e.toAddMonoidHom :
        AddSubgroup (ambientFixedAddSubgroup A B)) :
        Set (ambientFixedAddSubgroup A B)) := by
  let A := intrinsicAbsoluteUnits K
  let B := intrinsicAbstractBase K
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  obtain ⟨ϖ, d, n, hϖ, hd, hn, hstandard⟩ :=
    LocalFieldTheory.exists_uniformizerPrincipalSubgroup_le_of_isOpen_finiteIndex
      K H hH
  obtain ⟨U, hUle⟩ :=
    exists_unramifiedFiniteGaloisExtension_normSubgroup_map_le K d hd
  obtain ⟨T, hTle⟩ :=
    exists_equalCharacteristicLubinTateFiniteGaloisExtension_normSubgroup_map_le
      K p ϖ hϖ n hn
  let P := U.compositum T
  have hP :
      P.normSubgroup A ≤ H.toAddSubgroup.map e.toAddMonoidHom := by
    simpa [A, B, e, P] using
      (finiteGaloisCompositum_normSubgroup_le_of_standard
        K H ϖ d n hϖ hstandard U T hUle hTle)
  exact (ClassFormation.normTopology_addSubgroup_isOpen_iff A B
    (H.toAddSubgroup.map e.toAddMonoidHom)).2 ⟨P, hP⟩

/-- In positive characteristic, every ordinary open finite-index subgroup is
the ordinary norm subgroup of a finite abelian subextension. -/
theorem finiteAbelianNormSubgroupMap_surjective_of_charP
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Function.Surjective (finiteAbelianNormSubgroupMap K) := by
  intro H
  let : H.subgroup.FiniteIndex := H.finiteIndex
  apply exists_finiteAbelianNormSubgroup_eq_of_normOpen K H
  exact openFiniteIndexSubgroup_isNormOpen_of_charP
    K p H.subgroup H.isOpen

/-- Positive-characteristic local existence as an order isomorphism: finite
abelian subextensions correspond to ordinary open finite-index subgroups of
Kˣ with the opposite inclusion order. -/
noncomputable def finiteAbelianNormSubgroupOrderIso_of_charP
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    FiniteAbelianSubextension (intrinsicAbstractBase K) ≃o
      (OpenFiniteIndexSubgroup K)ᵒᵈ where
  toEquiv := Equiv.ofBijective (finiteAbelianNormSubgroupMap K)
    ⟨finiteAbelianNormSubgroupMap_injective K,
      finiteAbelianNormSubgroupMap_surjective_of_charP K p⟩
  map_rel_iff' := by
    intro L₁ L₂
    change finiteAbelianNormSubgroup K L₂ ≤
        finiteAbelianNormSubgroup K L₁ ↔ L₁ ≤ L₂
    exact (finiteAbelianSubextension_le_iff_normSubgroup_le K L₁ L₂).symm

/-- Underlying equivalence of positive-characteristic local existence. -/
noncomputable def finiteAbelianNormSubgroupEquiv_of_charP
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    FiniteAbelianSubextension (intrinsicAbstractBase K) ≃
      OpenFiniteIndexSubgroup K :=
  (finiteAbelianNormSubgroupOrderIso_of_charP K p).toEquiv

/-- States the theorem `finiteAbelianNormSubgroupOrderIso_of_charP_apply`. -/
@[simp]
theorem finiteAbelianNormSubgroupOrderIso_of_charP_apply
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianNormSubgroupOrderIso_of_charP K p L =
      finiteAbelianNormSubgroupMap K L := by
  rfl

end LocalField

end LocalClassFieldTheory
