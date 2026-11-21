/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius

/-!
# normalized degree and Frobenius theory: lifting finite Galois automorphisms

This file defines the Frobenius semigroup in `G(\widetilde L|K)` and proves
the lifting statement of the finite degree-quotient decomposition.  Positivity is explicit, so the
convention `0 ∉ ℕ` is not lost in Lean's natural numbers.
-/

@[expose] public section

namespace ClassFormation




noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- In a finite cyclic quotient of `ℤ̂`, every class is represented by a
strictly positive natural multiple of `1`. -/
theorem exists_positive_nsmul_one_sub_mem_of_index_ne_zero
    (H : AddSubgroup ZHat) (hH : H.index ≠ 0) (z : ZHat) :
    ∃ n : ℕ, 0 < n ∧ z - n • (1 : ZHat) ∈ H := by
  let m := H.index
  have hm : 0 < m := Nat.pos_of_ne_zero hH
  let r : ZMod m := zHatReduction m hm z
  let n : ℕ := r.val + m
  refine ⟨n, Nat.add_pos_right r.val hm, ?_⟩
  rw [zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero H hH,
    zHatMulNat_range_eq_ker_reduction m hm]
  change zHatReduction m hm (z - n • (1 : ZHat)) = 0
  rw [map_sub, map_nsmul]
  have hredOne : zHatReduction m hm (1 : ZHat) = 1 :=
    rfl
  rw [hredOne]
  change zHatReduction m hm z - n • (1 : ZMod m) = 0
  rw [nsmul_eq_mul, mul_one]
  change r - (n : ZMod m) = 0
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hn : (n : ZMod m) = r := by
    change ((r.val + m : ℕ) : ZMod m) = r
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
  rw [hn, sub_self]

namespace DegreeData

/-- `I_L`, viewed inside `G_K`; this is `G_{\widetilde L}`. -/
def extensionInertiaWithin (D : DegreeData G) (K L : ClosedSubgroup G)
    (_hLK : L.toSubgroup ≤ K.toSubgroup) : Subgroup K.toSubgroup :=
  (L.toSubgroup.subgroupOf K.toSubgroup) ⊓ D.fieldInertiaWithin K

/--
The relative inertia subgroup is normal whenever the full extension subgroup is normal.
-/
instance extensionInertiaWithin_normal (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    (D.extensionInertiaWithin K L hLK).Normal := by
  rw [extensionInertiaWithin]
  infer_instance

/-- Relative inertia is killed by the normalized degree map of the base field. -/
theorem extensionInertiaWithin_le_normalizedDegree_ker
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) :
    D.extensionInertiaWithin K.field L hLK ≤
      (D.normalizedDegree K).toMonoidHom.ker := by
  intro x hx
  rw [D.normalizedDegree_ker K]
  exact hx.2

/-- The factorized map `d_K : G(\widetilde L|K) → ℤ̂`. -/
def extensionNormalizedDegree (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) →* ZHatMul :=
  QuotientGroup.lift (D.extensionInertiaWithin K.field L hLK)
    (D.normalizedDegree K).toMonoidHom
    (D.extensionInertiaWithin_le_normalizedDegree_ker K L hLK)

/--
Establishes the identity `D.extensionNormalizedDegree K L hLK (QuotientGroup.mk k) =
D.normalizedDegree K k`.
-/
@[simp]
theorem extensionNormalizedDegree_mk (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (k : K.field.toSubgroup) :
    D.extensionNormalizedDegree K L hLK (QuotientGroup.mk k) =
      D.normalizedDegree K k :=
  rfl

/-- Restriction from `G(\widetilde L|K)` to `G(L|K)`. -/
def extensionRestriction (D : DegreeData G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) →*
      (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)) :=
  QuotientGroup.map (D.extensionInertiaWithin K L hLK)
    (L.toSubgroup.subgroupOf K.toSubgroup) (MonoidHom.id K.toSubgroup) inf_le_left

/--
Establishes the identity `D.extensionRestriction K L hLK (QuotientGroup.mk k) = QuotientGroup.mk
k`.
-/
@[simp]
theorem extensionRestriction_mk (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup) :
    D.extensionRestriction K L hLK (QuotientGroup.mk k) =
      QuotientGroup.mk k :=
  rfl

/-- The semigroup `Frob(\widetilde L|K)`: elements whose normalized
degree is a strictly positive natural. -/
def FrobeniusElements (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] : Type u :=
  {σ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK //
    ∃ n : ℕ, 0 < n ∧
      D.extensionNormalizedDegree K L hLK σ =
        (Multiplicative.ofAdd (1 : ZHat)) ^ n}

/-- The restriction map occurring in the finite degree-quotient decomposition. -/
def frobeniusRestriction (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    D.FrobeniusElements K L hLK →
      (K.field.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.field.toSubgroup)) :=
  fun σ => D.extensionRestriction K.field L hLK σ.1

private def normalizedExtensionImageAdd (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (_hLK : L.toSubgroup ≤ K.field.toSubgroup) : AddSubgroup ZHat :=
  Subgroup.toAddSubgroup'
    ((L.toSubgroup.subgroupOf K.field.toSubgroup).map
      (D.normalizedDegree K).toMonoidHom)

private theorem normalizedExtensionImageAdd_index_ne_zero
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.field.toSubgroup))] :
    (D.normalizedExtensionImageAdd K L hLK).index ≠ 0 := by
  let E := (L.toSubgroup.subgroupOf K.field.toSubgroup)
  let dK := (D.normalizedDegree K).toMonoidHom
  let H := E.map dK
  have hE : E ≤ H.comap dK := Subgroup.le_comap_map dK E
  have hdvd : (H.comap dK).index ∣ E.index :=
    Subgroup.index_dvd_of_le hE
  have hcomap : (H.comap dK).index = H.index :=
    Subgroup.index_comap_of_surjective H (D.normalizedDegree_surjective K)
  have hHdvd : H.index ∣ E.index := hcomap ▸ hdvd
  have hE0 : E.index ≠ 0 := E.index_ne_zero_of_finite
  have hH0 : H.index ≠ 0 := by
    intro hzero
    rw [hzero] at hHdvd
    exact hE0 (zero_dvd_iff.mp hHdvd)
  exact hH0

/-- **the finite degree-quotient decomposition.** For a finite Galois extension `L | K`, restriction
maps the Frobenius semigroup onto `G(L|K)`. -/
theorem frobeniusRestriction_surjective (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.field.toSubgroup))] :
    Function.Surjective (D.frobeniusRestriction K L hLK) := by
  intro σ
  refine Quotient.inductionOn' σ ?_
  intro s
  let H := D.normalizedExtensionImageAdd K L hLK
  have hH0 : H.index ≠ 0 :=
    D.normalizedExtensionImageAdd_index_ne_zero K L hLK
  obtain ⟨n, hn, hmem⟩ :=
    exists_positive_nsmul_one_sub_mem_of_index_ne_zero H hH0
      (D.normalizedDegree K s).toAdd
  have hneg : n • (1 : ZHat) - (D.normalizedDegree K s).toAdd ∈ H := by
    simpa [sub_eq_add_neg, add_comm] using H.neg_mem hmem
  change Multiplicative.ofAdd
      (n • (1 : ZHat) - (D.normalizedDegree K s).toAdd) ∈
    (L.toSubgroup.subgroupOf K.field.toSubgroup).map
      (D.normalizedDegree K).toMonoidHom at hneg
  obtain ⟨l, hlE, hdl⟩ := hneg
  let t : K.field.toSubgroup := s * l
  let q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK :=
    QuotientGroup.mk t
  have hdq : D.extensionNormalizedDegree K L hLK q =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
    apply Multiplicative.ext
    change (D.normalizedDegree K (s * l)).toAdd =
      n • (1 : ZHat)
    rw [map_mul]
    change (D.normalizedDegree K s).toAdd +
        (D.normalizedDegree K l).toAdd = n • (1 : ZHat)
    have hdl' := congrArg Multiplicative.toAdd hdl
    change (D.normalizedDegree K l).toAdd =
      n • (1 : ZHat) - (D.normalizedDegree K s).toAdd at hdl'
    rw [hdl']
    abel
  let qF : D.FrobeniusElements K L hLK := ⟨q, n, hn, hdq⟩
  refine ⟨qF, ?_⟩
  change QuotientGroup.mk (s * l) = QuotientGroup.mk s
  apply QuotientGroup.eq.mpr
  change (s * l)⁻¹ * s ∈ (L.toSubgroup.subgroupOf K.field.toSubgroup)
  simpa [mul_inv_rev, mul_assoc] using
    (L.toSubgroup.subgroupOf K.field.toSubgroup).inv_mem hlE

end DegreeData

/-- The left vertical map in the first diagram of norm--conjugation naturality:
restriction from `G(L'/K')` to `G(L/K)`. -/
def finiteReciprocityNaturalityRestriction
    (K K' L L' : ClosedSubgroup G)
    (_hLK : L.toSubgroup ≤ K.toSubgroup)
    (_hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (K'.toSubgroup ⧸ (L'.toSubgroup.subgroupOf K'.toSubgroup)) →*
      (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)) := by
  apply QuotientGroup.map
    (L'.toSubgroup.subgroupOf K'.toSubgroup)
    (L.toSubgroup.subgroupOf K.toSubgroup)
    (Subgroup.inclusion hK'K)
  intro k' hk'L'
  change k'.1 ∈ L'.toSubgroup at hk'L'
  change (Subgroup.inclusion hK'K k').1 ∈ L.toSubgroup
  exact hL'L hk'L'

/-- Restriction sends a represented finite reciprocity class to the corresponding
lower-level class. -/
@[simp]
theorem finiteReciprocityNaturalityRestriction_mk
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    (k' : K'.toSubgroup) :
    finiteReciprocityNaturalityRestriction K K' L L' hLK hL'K' hK'K hL'L
        (QuotientGroup.mk k') =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') :=
  rfl

namespace DegreeData

/-- Restriction on the infinite Frobenius quotients underlying the first
diagram of norm--conjugation naturality. -/
def finiteReciprocityNaturalityFrobeniusTowerMap
    (D : DegreeData G) [IsTopologicalGroup G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (K'.toSubgroup ⧸ D.extensionInertiaWithin K' L' hL'K') →*
      (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) := by
  apply QuotientGroup.map
    (D.extensionInertiaWithin K' L' hL'K')
    (D.extensionInertiaWithin K L hLK)
    (Subgroup.inclusion hK'K)
  rintro k' ⟨hk'L', hk'I⟩
  constructor
  · change k'.1 ∈ L'.toSubgroup at hk'L'
    change (Subgroup.inclusion hK'K k').1 ∈ L.toSubgroup
    exact hL'L hk'L'
  · exact hk'I

/-- The Frobenius tower map has the expected value on a quotient representative. -/
@[simp]
theorem finiteReciprocityNaturalityFrobeniusTowerMap_mk
    (D : DegreeData G) [IsTopologicalGroup G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    (k' : K'.toSubgroup) :
    D.finiteReciprocityNaturalityFrobeniusTowerMap K K' L L'
        hLK hL'K' hK'K hL'L (QuotientGroup.mk k') =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') := rfl

/-- Continuous form of `finiteReciprocityNaturalityFrobeniusTowerMap`, used to transport
the closed cyclic subgroup generated by a Frobenius lift. -/
def finiteReciprocityNaturalityFrobeniusTowerMapContinuous
    (D : DegreeData G) [IsTopologicalGroup G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (K'.toSubgroup ⧸ D.extensionInertiaWithin K' L' hL'K') →ₜ*
      (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) where
  toMonoidHom := D.finiteReciprocityNaturalityFrobeniusTowerMap
    K K' L L' hLK hL'K' hK'K hL'L
  continuous_toFun := by
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    change Continuous (fun k' : K'.toSubgroup =>
      QuotientGroup.mk (Subgroup.inclusion hK'K k'))
    apply QuotientGroup.continuous_mk.comp
    exact continuous_subtype_val.subtype_mk _

/-- Frobenius residue-degree compatibility's normalized-degree square on the two infinite
Frobenius quotients. -/
theorem finiteReciprocityNaturalityFrobeniusTowerMap_degree
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (q : E.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L' hL'K') :
    (D.extensionNormalizedDegree E.base L hLK
      (D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L'
        hLK hL'K' E.below hL'L q)).toAdd =
      (E.residueDegree : ℕ) •
        (D.extensionNormalizedDegree E.field L' hL'K' q).toAdd := by
  refine Quotient.inductionOn' q ?_
  intro k'
  change (D.normalizedDegree E.base (Subgroup.inclusion E.below k')).toAdd =
    (E.residueDegree : ℕ) • (D.normalizedDegree E.field k').toAdd
  exact D.frobeniusRestrictionNaturality_normalizedDegree E k'

end DegreeData

end
end ClassFormation
