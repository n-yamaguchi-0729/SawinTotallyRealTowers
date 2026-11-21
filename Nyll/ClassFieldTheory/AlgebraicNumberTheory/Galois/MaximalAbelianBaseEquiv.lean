/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Mathlib.FieldTheory.Galois.Infinite
public import Nyll.ClassFieldTheory.Algebra.IntermediateFieldRingEquivOrderIso
public import Nyll.ClassFieldTheory.Algebra.AbelianGaloisEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteAbelianization
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteGaloisBaseEquiv

/-!
# Base equivalences on the actual maximal abelian extension

Restricting the specified ambient equivalence gives the separable and maximal
abelian field maps. Their conjugation actions commute with restriction and
with the canonical comparison of absolute Galois abelianizations.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v

variable {K : Type u} {M : Type v} [Field K] [Field M]

theorem separableClosure_mem_semilinear
    (e : K ≃+* M) (c : AlgebraicClosure K ≃+* AlgebraicClosure M)
    (hc : ∀ a : K, c (algebraMap K (AlgebraicClosure K) a) =
      algebraMap M (AlgebraicClosure M) (e a))
    (x : SeparableClosure K) :
    c (x : AlgebraicClosure K) ∈ separableClosure M (AlgebraicClosure M) := by
  apply mem_separableClosure_iff.2
  apply IsSeparable.of_equiv_equiv e c
  · apply RingHom.ext
    intro a
    exact (hc a).symm
  · exact mem_separableClosure_iff.1 x.property

/-- The specified algebraic-closure equivalence restricted to the actual
separable closures. -/
def separableClosureEquivOfSemilinear
    (e : K ≃+* M) (c : AlgebraicClosure K ≃+* AlgebraicClosure M)
    (hc : ∀ a : K, c (algebraMap K (AlgebraicClosure K) a) =
      algebraMap M (AlgebraicClosure M) (e a)) :
    SeparableClosure K ≃+* SeparableClosure M where
  toFun x := ⟨c x, separableClosure_mem_semilinear e c hc x⟩
  invFun y := ⟨c.symm y, separableClosure_mem_semilinear e.symm c.symm
    (semilinear_symm_algebraMap e c hc) y⟩
  left_inv x := Subtype.ext (c.symm_apply_apply x)
  right_inv y := Subtype.ext (c.apply_symm_apply y)
  map_mul' x y := Subtype.ext (c.map_mul x y)
  map_add' x y := Subtype.ext (c.map_add x y)

/-- Restriction to the separable closure retains the base embedding. -/
theorem separableClosureEquivOfSemilinear_commutes
    (e : K ≃+* M) (c : AlgebraicClosure K ≃+* AlgebraicClosure M)
    (hc : ∀ a : K, c (algebraMap K (AlgebraicClosure K) a) =
      algebraMap M (AlgebraicClosure M) (e a))
    (a : K) :
    separableClosureEquivOfSemilinear e c hc (algebraMap K (SeparableClosure K) a) =
      algebraMap M (SeparableClosure M) (e a) :=
  Subtype.ext (hc a)

private theorem abelianIntermediateField_le_maximalAbelianExtension
    (E : IntermediateField K (SeparableClosure K)) [IsAbelianGalois K E] :
    E ≤ maximalAbelianExtension K := by
  rw [maximalAbelianExtension, IntermediateField.le_fixedField_iff_le_fixingSubgroup]
  change (commutator Gal(SeparableClosure K/K)).topologicalClosure ≤ E.fixingSubgroup
  apply Subgroup.topologicalClosure_minimal
  · rw [← E.restrictNormalHom_ker]
    exact Group.Abelianization.commutator_le_ker
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := SeparableClosure K) E)
  · exact InfiniteGalois.fixingSubgroup_isClosed E

theorem maximalAbelianExtension_map_le
    (e : K ≃+* M) (c : SeparableClosure K ≃+* SeparableClosure M)
    (hc : ∀ a : K, c (algebraMap K (SeparableClosure K) a) =
      algebraMap M (SeparableClosure M) (e a)) :
    intermediateFieldMapRingEquiv e c hc (maximalAbelianExtension K) ≤
      maximalAbelianExtension M := by
  let E := intermediateFieldMapRingEquiv e c hc (maximalAbelianExtension K)
  let : IsAbelianGalois M E := isAbelianGalois_of_equiv_equiv e
    (intermediateFieldMapRingEquivEquiv e c hc (maximalAbelianExtension K))
    (intermediateFieldMapRingEquivEquiv_commutes e c hc (maximalAbelianExtension K))
  exact abelianIntermediateField_le_maximalAbelianExtension E

/-- Restrict the specified separable-closure map to the actual maximal
abelian intermediate fields. Both directions retain their ambient values. -/
def maximalAbelianExtensionEquivOfSemilinear
    (e : K ≃+* M) (c : SeparableClosure K ≃+* SeparableClosure M)
    (hc : ∀ a : K, c (algebraMap K (SeparableClosure K) a) =
      algebraMap M (SeparableClosure M) (e a)) :
    maximalAbelianExtension K ≃+* maximalAbelianExtension M where
  toFun x := ⟨c x, maximalAbelianExtension_map_le e c hc ⟨x, x.property, rfl⟩⟩
  invFun y := ⟨c.symm y, maximalAbelianExtension_map_le e.symm c.symm
    (semilinear_symm_algebraMap e c hc) ⟨y, y.property, rfl⟩⟩
  left_inv x := Subtype.ext (c.symm_apply_apply x)
  right_inv y := Subtype.ext (c.apply_symm_apply y)
  map_mul' x y := Subtype.ext (c.map_mul x y)
  map_add' x y := Subtype.ext (c.map_add x y)

/-- Restriction to the maximal abelian field retains the base embedding. -/
theorem maximalAbelianExtensionEquivOfSemilinear_commutes
    (e : K ≃+* M) (c : SeparableClosure K ≃+* SeparableClosure M)
    (hc : ∀ a : K, c (algebraMap K (SeparableClosure K) a) =
      algebraMap M (SeparableClosure M) (e a))
    (a : K) :
    maximalAbelianExtensionEquivOfSemilinear e c hc
        (algebraMap K (maximalAbelianExtension K) a) =
      algebraMap M (maximalAbelianExtension M) (e a) :=
  Subtype.ext (hc a)

/-- Mathlib's absolute abelianization identified with the actual maximal
abelian extension of the chosen separable closure. -/
noncomputable def mathlibAbelianizationToMaximal
    (K : Type u) [Field K] :
    Field.absoluteGaloisGroupAbelianization K ≃ₜ* Gal(maximalAbelianExtension K/K) :=
  (absoluteGaloisGroupAbelianizationEquivSeparable K).trans
    (absoluteTopologicalAbelianizationEquivMaximalAbelianGalois K)

/-- On an actual absolute automorphism, the comparison is restriction through
the same separable closure to the same maximal abelian field. -/
theorem mathlibAbelianizationToMaximal_mk
    (σ : Field.absoluteGaloisGroup K) :
    mathlibAbelianizationToMaximal K (QuotientGroup.mk σ) =
      AlgEquiv.restrictNormalHom (maximalAbelianExtension K) (AlgEquiv.separableClosure σ) := by
  change absoluteAbelianizationMulEquivMaximalAbelianGalois K
      (absoluteGaloisGroupAbelianizationEquivSeparable K (QuotientGroup.mk σ)) = _
  rw [absoluteGaloisGroupAbelianizationEquivSeparable_mk,
    absoluteAbelianizationMulEquivMaximalAbelianGalois_mk]

/-- The absolute comparison commutes with the actual base and ambient maps.
The proof checks representatives and their values in the original closure. -/
theorem mathlibAbelianizationToMaximal_semilinear
    (e : K ≃+* M) (c : AlgebraicClosure K ≃+* AlgebraicClosure M)
    (hc : ∀ a : K, c (algebraMap K (AlgebraicClosure K) a) =
      algebraMap M (AlgebraicClosure M) (e a))
    (q : Field.absoluteGaloisGroupAbelianization K) :
    let s := separableClosureEquivOfSemilinear e c hc
    let hs := separableClosureEquivOfSemilinear_commutes e c hc
    let m := maximalAbelianExtensionEquivOfSemilinear e s hs
    let hm := maximalAbelianExtensionEquivOfSemilinear_commutes e s hs
    mathlibAbelianizationToMaximal M
        (ProCGroups.Abelian.TopologicalAbelianization.congr
          (semilinearGaloisContinuousEquiv e c hc) q) =
      semilinearGaloisEquiv e m hm (mathlibAbelianizationToMaximal K q) := by
  intro s hs m hm
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure q
  change mathlibAbelianizationToMaximal M
      (QuotientGroup.mk (semilinearGaloisContinuousEquiv e c hc σ)) =
    semilinearGaloisEquiv e m hm
      (mathlibAbelianizationToMaximal K (QuotientGroup.mk σ))
  rw [mathlibAbelianizationToMaximal_mk (K := M)
    (semilinearGaloisContinuousEquiv e c hc σ), mathlibAbelianizationToMaximal_mk σ]
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  change
    (AlgEquiv.restrictNormalHom (maximalAbelianExtension M)
      (AlgEquiv.separableClosure (semilinearGaloisContinuousEquiv e c hc σ)) y :
      SeparableClosure M) =
    s (AlgEquiv.restrictNormalHom (maximalAbelianExtension K)
      (AlgEquiv.separableClosure σ) (m.symm y) : SeparableClosure K)
  rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
  apply Subtype.ext
  rfl

/-- The maximal-field equivalence induced by the specified algebraic-closure
extension used in the public absolute Galois base equivalence. -/
noncomputable def maximalAbelianExtensionBaseEquiv (e : K ≃+* M) :
    maximalAbelianExtension K ≃+* maximalAbelianExtension M :=
  let c := IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure M) e
  let hc := IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure M) e
  let s := separableClosureEquivOfSemilinear e c hc
  maximalAbelianExtensionEquivOfSemilinear e s
    (separableClosureEquivOfSemilinear_commutes e c hc)

/-- The specified maximal-field base equivalence extends the given base map. -/
theorem maximalAbelianExtensionBaseEquiv_commutes (e : K ≃+* M) (a : K) :
    maximalAbelianExtensionBaseEquiv e (algebraMap K (maximalAbelianExtension K) a) =
      algebraMap M (maximalAbelianExtension M) (e a) := by
  let c := IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure M) e
  let hc := IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure M) e
  exact maximalAbelianExtensionEquivOfSemilinear_commutes e
    (separableClosureEquivOfSemilinear e c hc)
    (separableClosureEquivOfSemilinear_commutes e c hc) a

/-- The public absolute base equivalence and the same maximal-field base
equivalence commute with the canonical absolute comparison. -/
theorem mathlibAbelianizationToMaximal_baseEquiv (e : K ≃+* M)
    (q : Field.absoluteGaloisGroupAbelianization K) :
    mathlibAbelianizationToMaximal M
        (absoluteGaloisGroupAbelianizationEquivOfRingEquiv e q) =
      semilinearGaloisEquiv (K := K) (M := M)
        (Ω := maximalAbelianExtension K) (Ψ := maximalAbelianExtension M)
        e (maximalAbelianExtensionBaseEquiv e)
        (maximalAbelianExtensionBaseEquiv_commutes e)
        (mathlibAbelianizationToMaximal K q) :=
  mathlibAbelianizationToMaximal_semilinear e
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure M) e)
    (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure M) e) q

end ClassFieldTheory
