import ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
import ProCGroups.Completion.FiniteQuotientLifts
import ProCGroups.FreeProC.Basic

set_option autoImplicit false
/-!
# The profinite integers as a rank-one free profinite group

The dense copy of the infinite cyclic group in `ZHat` has the expected universal property.
A map to a finite discrete group factors through the cyclic quotient determined by the order of
the image of `1`; the finite-quotient criterion then gives the full pro-all-finite completion and
free-profinite properties.

This production leaf is independent of every `Progress` module.
-/

open Set
open scoped Topology

noncomputable section

namespace ClassFieldTower.Cohomology.ProfiniteInteger

open ProCGroups
open ProCGroups.FreeProC

/-- The canonical topological generator `1` of the multiplicative profinite integers. -/
abbrev generator : ClassFormation.ZHatMul :=
  Multiplicative.ofAdd (1 : ClassFormation.ZHat)

/-- The dense homomorphism from the infinite cyclic group to the profinite integers. -/
def integersMap : Multiplicative ℤ →ₜ* ClassFormation.ZHatMul where
  toMonoidHom := AddMonoidHom.toMultiplicative
    (Int.castRingHom ClassFormation.ZHat).toAddMonoidHom
  continuous_toFun := continuous_of_discreteTopology

/-- The integer map sends `n` to the `n`-th power of the canonical generator. -/
@[simp]
theorem integersMap_apply (n : ℤ) :
    integersMap (Multiplicative.ofAdd n) = generator ^ n := by
  change Multiplicative.ofAdd ((n : ℤ) : ClassFormation.ZHat) =
    (Multiplicative.ofAdd (1 : ClassFormation.ZHat)) ^ n
  apply Multiplicative.ext
  simp

/-- The image of the integers is dense in the profinite integers. -/
theorem denseRange_integersMap : DenseRange integersMap := by
  have hOfAdd :
      DenseRange (Multiplicative.ofAdd :
        ClassFormation.ZHat → ClassFormation.ZHatMul) :=
    (show Function.Surjective
        (Multiplicative.ofAdd : ClassFormation.ZHat → ClassFormation.ZHatMul) from
      fun x => ⟨Multiplicative.toAdd x, rfl⟩).denseRange
  have hCast :
      DenseRange
        (Multiplicative.ofAdd ∘ fun a : ℤ => (a : ClassFormation.ZHat)) :=
    hOfAdd.comp ClassFormation.denseRange_intCast_zHat continuous_id
  have hToAdd :
      DenseRange (Multiplicative.toAdd : Multiplicative ℤ → ℤ) :=
    (show Function.Surjective
        (Multiplicative.toAdd : Multiplicative ℤ → ℤ) from
      fun a => ⟨Multiplicative.ofAdd a, rfl⟩).denseRange
  change DenseRange (fun z : Multiplicative ℤ =>
    Multiplicative.ofAdd ((z.toAdd : ℤ) : ClassFormation.ZHat))
  simpa [Function.comp_def] using
    hCast.comp hToAdd continuous_of_discreteTopology

private def reductionMul (n : ℕ) (hn : 0 < n) :
    ClassFormation.ZHatMul →ₜ* Multiplicative (ZMod n) where
  toFun z := Multiplicative.ofAdd (ClassFormation.zHatReduction n hn z.toAdd)
  map_one' := by
    apply Multiplicative.ext
    exact map_zero (ClassFormation.zHatReduction n hn)
  map_mul' x y := by
    apply Multiplicative.ext
    exact map_add (ClassFormation.zHatReduction n hn) x.toAdd y.toAdd
  continuous_toFun := map_continuous (ClassFormation.zHatReduction n hn)

private def cyclicIntHom {K : Type} [Group K] (k : K) :
    ℤ →+ Additive (Subgroup.zpowers k) where
  toFun z := Additive.ofMul ⟨k ^ z, z, rfl⟩
  map_zero' := by
    apply Additive.ext
    ext
    simp only [zpow_zero, toMul_ofMul, toMul_zero, OneMemClass.coe_one]
  map_add' := by
    intro a b
    apply Additive.ext
    ext
    simp only [zpow_add, toMul_ofMul, toMul_add, Subgroup.coe_mul]

private theorem cyclicIntHom_order {K : Type} [Group K] (k : K) :
    cyclicIntHom k (orderOf k) = 0 := by
  apply Additive.ext
  ext
  change k ^ ((orderOf k : ℕ) : ℤ) = 1
  simp only [zpow_natCast, pow_orderOf_eq_one]

private noncomputable def cyclicZModHom {K : Type} [Group K] (k : K) :
    ZMod (orderOf k) →+ Additive (Subgroup.zpowers k) :=
  (ZMod.lift (orderOf k)) ⟨cyclicIntHom k, cyclicIntHom_order k⟩

private noncomputable def cyclicStageHom {K : Type} [Group K] (k : K) :
    Multiplicative (ZMod (orderOf k)) →* K :=
  (Subgroup.zpowers k).subtype.comp
    (AddMonoidHom.toMultiplicativeLeft (cyclicZModHom k))

@[simp]
private theorem cyclicStageHom_generator {K : Type} [Group K] (k : K) :
    cyclicStageHom k (Multiplicative.ofAdd (1 : ZMod (orderOf k))) = k := by
  change ((cyclicZModHom k (1 : ZMod (orderOf k))).toMul : K) = k
  rw [show (1 : ZMod (orderOf k)) = ((1 : ℤ) : ZMod (orderOf k)) by norm_num]
  rw [cyclicZModHom, ZMod.lift_coe]
  change k ^ (1 : ℤ) = k
  simp only [zpow_one]

@[simp]
private theorem reductionMul_generator (n : ℕ) (hn : 0 < n) :
    reductionMul n hn generator = Multiplicative.ofAdd (1 : ZMod n) := by
  apply Multiplicative.ext
  rfl

private noncomputable def finiteLift
    {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [Finite Q] [DiscreteTopology Q]
    (φ : Multiplicative ℤ →ₜ* Q) : ClassFormation.ZHatMul →ₜ* Q := by
  let k : Q := φ (Multiplicative.ofAdd (1 : ℤ))
  let hn : 0 < orderOf k := orderOf_pos k
  exact
    { toMonoidHom := (cyclicStageHom k).comp
        (reductionMul (orderOf k) hn).toMonoidHom
      continuous_toFun := by
        have hk : Continuous (cyclicStageHom k) := continuous_of_discreteTopology
        exact hk.comp (reductionMul (orderOf k) hn).continuous_toFun }

@[simp]
private theorem finiteLift_generator
    {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [Finite Q] [DiscreteTopology Q]
    (φ : Multiplicative ℤ →ₜ* Q) :
    finiteLift φ generator = φ (Multiplicative.ofAdd (1 : ℤ)) := by
  let k : Q := φ (Multiplicative.ofAdd (1 : ℤ))
  let hn : 0 < orderOf k := orderOf_pos k
  change cyclicStageHom k (reductionMul (orderOf k) hn generator) = k
  rw [reductionMul_generator]
  exact cyclicStageHom_generator k

private theorem hom_from_multiplicativeInt_apply
    {Q : Type} [Group Q] (φ : Multiplicative ℤ →* Q) (n : ℤ) :
    φ (Multiplicative.ofAdd n) =
      (φ (Multiplicative.ofAdd (1 : ℤ))) ^ n := by
  have hn :
      Multiplicative.ofAdd n = (Multiplicative.ofAdd (1 : ℤ)) ^ n := by
    apply Multiplicative.ext
    simp
  rw [hn, map_zpow]

private theorem finiteLift_comp_integersMap
    {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [Finite Q] [DiscreteTopology Q]
    (φ : Multiplicative ℤ →ₜ* Q) :
    (finiteLift φ).comp integersMap = φ := by
  apply ContinuousMonoidHom.toMonoidHom_injective
  apply MonoidHom.ext
  intro z
  cases z
  rename_i n
  calc
    finiteLift φ (integersMap (Multiplicative.ofAdd n)) =
        finiteLift φ (generator ^ n) := by rw [integersMap_apply]
    _ = (finiteLift φ generator) ^ n := by rw [map_zpow]
    _ = (φ (Multiplicative.ofAdd (1 : ℤ))) ^ n := by rw [finiteLift_generator]
    _ = φ (Multiplicative.ofAdd n) :=
      (hom_from_multiplicativeInt_apply φ.toMonoidHom n).symm

/-- Every map from the infinite cyclic group to a finite discrete group extends uniquely over
the profinite integers. -/
theorem existsUnique_finiteLift
    {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [Finite Q] [DiscreteTopology Q]
    (φ : Multiplicative ℤ →ₜ* Q) :
    ∃! f : ClassFormation.ZHatMul →ₜ* Q, f.comp integersMap = φ := by
  let f : ClassFormation.ZHatMul →ₜ* Q := finiteLift φ
  have hf : f.comp integersMap = φ := finiteLift_comp_integersMap φ
  refine ⟨f, hf, ?_⟩
  intro g hg
  have hEqFun :
      (fun x : ClassFormation.ZHatMul => g x) =
        fun x : ClassFormation.ZHatMul => f x := by
    apply DenseRange.equalizer
      (f := integersMap) denseRange_integersMap
    · exact g.continuous_toFun
    · exact f.continuous_toFun
    · funext z
      exact congrArg (fun h : Multiplicative ℤ →ₜ* Q => h z) (hg.trans hf.symm)
  apply ContinuousMonoidHom.toMonoidHom_injective
  apply MonoidHom.ext
  intro x
  exact congrFun hEqFun x

/-- The concrete profinite integers are the pro-all-finite completion of the infinite cyclic
group. -/
theorem isProfiniteCompletion :
    ProCGroups.Completion.IsProCCompletion
      ProCGroups.FiniteGroupClass.allFinite (Multiplicative ℤ)
        ClassFormation.ZHatMul integersMap := by
  let _ : T2Space ClassFormation.ZHatMul := by
    change T2Space ClassFormation.ZHat
    infer_instance
  have hZHat : ProCGroups.ProC.HasOpenNormalBasisInClass
      ProCGroups.FiniteGroupClass.allFinite ClassFormation.ZHatMul := by
    exact ProCGroups.ProC.hasOpenNormalBasisInClass_allFinite
  apply ProCGroups.Completion.isProCCompletion_of_finiteQuotientLifts
    (C := ProCGroups.FiniteGroupClass.allFinite)
    ProCGroups.FiniteGroupClass.allFinite_formation
    hZHat
  · exact denseRange_integersMap
  · intro Q _ _ _ _ _ _hQ φ
    exact existsUnique_finiteLift φ

/-- The multiplicative profinite integers are free on their canonical generator for the
all-finite class. -/
theorem isFreeProfinite :
    IsFreeProCGroup
      (C := ProCGroups.FiniteGroupClass.allFinite)
      (Function.const PUnit generator) := by
  let hcomp := isProfiniteCompletion
  refine
    { hasOpenNormalBasisInClass := hcomp.hasOpenNormalBasisInClass
      continuous_ι := continuous_const
      generates_range := ?_
      existsUnique_lift := ?_ }
  · have hrange :
        Set.range (Function.const PUnit generator) =
          ({generator} : Set ClassFormation.ZHatMul) := by
      ext z
      simp only [mem_range, Function.const, exists_const, mem_singleton_iff, eq_comm]
    rw [hrange]
    simpa [ProCGroups.Generation.TopologicallyGenerates,
      ClassFormation.TopologicallyGenerates] using
      ClassFormation.zHatOne_topologicallyGenerates
  · intro G _ _ _ _ _ _ hG φ _hφ
    let ψ : Multiplicative ℤ →ₜ* G :=
      { toMonoidHom := zpowersHom G (φ PUnit.unit)
        continuous_toFun := continuous_of_discreteTopology }
    rcases hcomp.existsUnique_lift hG ψ with ⟨f, hf, huniq⟩
    refine ⟨f, ⟨f.continuous_toFun, ?_⟩, ?_⟩
    · intro x
      cases x
      have h1 := congrArg
        (fun k : Multiplicative ℤ →ₜ* G => k (Multiplicative.ofAdd (1 : ℤ))) hf
      have hmapOne : integersMap (Multiplicative.ofAdd (1 : ℤ)) = generator := by simp
      calc
        f generator = f (integersMap (Multiplicative.ofAdd (1 : ℤ))) := by rw [hmapOne]
        _ = ψ (Multiplicative.ofAdd (1 : ℤ)) := h1
        _ = φ PUnit.unit := by
          change (φ PUnit.unit) ^ (1 : ℤ) = φ PUnit.unit
          simp only [zpow_one]
    · intro g hg
      let gc : ClassFormation.ZHatMul →ₜ* G :=
        { toMonoidHom := g
          continuous_toFun := hg.1 }
      have hgfac : gc.comp integersMap = ψ := by
        apply ContinuousMonoidHom.toMonoidHom_injective
        apply MonoidHom.ext
        intro z
        change g (integersMap z) = (φ PUnit.unit) ^ z.toAdd
        cases z
        rename_i n
        rw [integersMap_apply, map_zpow]
        change g generator ^ n = (φ PUnit.unit) ^ n
        have hgg : g generator = φ PUnit.unit := by
          simpa only [Function.const_apply] using hg.2 PUnit.unit
        rw [hgg]
      exact congrArg ContinuousMonoidHom.toMonoidHom (huniq gc hgfac)

end ClassFieldTower.Cohomology.ProfiniteInteger

end
