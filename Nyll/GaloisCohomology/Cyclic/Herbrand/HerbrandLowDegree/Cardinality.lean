/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Equiv.Basic
public import Nyll.GaloisCohomology.Cyclic.IntegralCyclicNormComplexes
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.IntegralTateComparison

/-!
# Finiteness and cardinality of the original periodic norm complex

The coefficient modules share a working universe, independently of the finite acting group.
Every differential is the original integer norm or the original generator minus the identity.
The existing arithmetic Herbrand comparisons identify the same cycles and boundaries. This
module remains the canonical owner of the six-term cardinality argument and its pure module
helpers. It also supplies finiteness transfer from the same exact periodic sequence.
-/

@[expose] public section

noncomputable section

universe u v uG uA

open CategoryTheory IntegralGroupCohomology.Universe

namespace CyclicCohomology.ProfiniteCohomology.Herbrand

variable {G : Type u} {A B C : Type v}
    [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]

/-- The condition that the Herbrand quotient of `A` is defined. -/
def HerbrandQuotientDefined (G : Type uG) (A : Type uA)
    [Group G] [Fintype G] [CommGroup A] [MulDistribMulAction G A]
    (σ : G) : Prop :=
  Finite (HerbrandH0 G A) ∧ Finite (HerbrandHMinusOne G A σ)

private def coefficientMap (f : A →* B) :
    ModuleCat.of ℤ (Additive A) ⟶ ModuleCat.of ℤ (Additive B) :=
  ModuleCat.ofHom (MonoidHom.toAdditive f).toIntLinearMap

private def periodicChainComplex (σ : G) : ChainComplex (ModuleCat.{v} ℤ) ℕ :=
  HomologicalComplex.alternatingConst (ModuleCat.of ℤ (Additive A))
    (normHomCompSub (Rep.ofMulDistribMulAction G A) σ).zero
    (subCompNormHom (Rep.ofMulDistribMulAction G A) σ).zero
    (fun _ _ => ComplexShape.down_nat_odd_add)

private def subCompNormMap
    (σ : G) (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    subCompNormHom (Rep.ofMulDistribMulAction G A) σ ⟶
      subCompNormHom (Rep.ofMulDistribMulAction G B) σ where
  τ₁ := coefficientMap (A := A) (B := B) f
  τ₂ := coefficientMap (A := A) (B := B) f
  τ₃ := coefficientMap (A := A) (B := B) f
  comm₁₂ := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun (a : Additive A) => ?_
    change Additive.ofMul ((σ • f a.toMul) / f a.toMul) =
      Additive.ofMul (f ((σ • a.toMul) / a.toMul))
    exact congrArg Additive.ofMul (by rw [map_div, hf])
  comm₂₃ := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun (a : Additive A) => ?_
    apply Additive.toMul.injective
    exact (repNorm_toMul (G := G) (A := B) (Additive.ofMul (f a.toMul))).trans
      ((map_tateNorm f hf a.toMul).symm.trans
        (congrArg f (repNorm_toMul (G := G) (A := A) a)).symm)

private theorem alternatingConst_d_naturality
    {X Y : ModuleCat.{v} ℤ} {φX ψX : X ⟶ X} {φY ψY : Y ⟶ Y}
    (hX : φX ≫ ψX = 0) (hX' : ψX ≫ φX = 0)
    (hY : φY ≫ ψY = 0) (hY' : ψY ≫ φY = 0)
    (f : X ⟶ Y) (hφ : f ≫ φY = φX ≫ f) (hψ : f ≫ ψY = ψX ≫ f)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    f ≫ (HomologicalComplex.alternatingConst Y hY hY'
      (fun _ _ => ComplexShape.down_nat_odd_add)).d i j =
      (HomologicalComplex.alternatingConst X hX hX'
        (fun _ _ => ComplexShape.down_nat_odd_add)).d i j ≫ f := by
  change f ≫ (if (ComplexShape.down ℕ).Rel i j then
      if Even i then φY else ψY else 0) =
    (if (ComplexShape.down ℕ).Rel i j then if Even i then φX else ψX else 0) ≫ f
  rw [ite_eq_left hij, ite_eq_left hij]
  by_cases hi : Even i
  · rw [ite_eq_left hi, ite_eq_left hi]
    exact hφ
  · rw [ite_eq_right hi, ite_eq_right hi]
    exact hψ

private def periodicChainMap
    (σ : G) (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    periodicChainComplex (A := A) σ ⟶ periodicChainComplex (A := B) σ where
  f _ := coefficientMap (A := A) (B := B) f
  comm' := by
    intro i j hij
    exact alternatingConst_d_naturality
      (X := ModuleCat.of ℤ (Additive A)) (Y := ModuleCat.of ℤ (Additive B))
      (normHomCompSub (Rep.ofMulDistribMulAction G A) σ).zero
      (subCompNormHom (Rep.ofMulDistribMulAction G A) σ).zero
      (normHomCompSub (Rep.ofMulDistribMulAction G B) σ).zero
      (subCompNormHom (Rep.ofMulDistribMulAction G B) σ).zero
      (coefficientMap (A := A) (B := B) f)
      (subCompNormMap (A := A) (B := B) σ f hf).comm₂₃
      (subCompNormMap (A := A) (B := B) σ f hf).comm₁₂ i j hij

private def periodicShortComplex
    (σ : G) (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b) :
    ShortComplex (ChainComplex (ModuleCat.{v} ℤ) ℕ) :=
  ShortComplex.mk (periodicChainMap σ i hi) (periodicChainMap σ j hj) <| by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Additive.ofMul (j (i a.toMul)) = 0
    apply Additive.ofMul.injective
    exact (hker (i a.toMul)).2 ⟨a.toMul, rfl⟩

private theorem periodicShortComplex_shortExact
    (σ : G) (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j) :
    (periodicShortComplex σ i j hi hj hker).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  refine
    { exact := ?_
      mono_f := (ModuleCat.mono_iff_injective _).2 ?_
      epi_g := (ModuleCat.epi_iff_surjective _).2 ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).2
    intro b hb
    change Additive.ofMul (j b.toMul) = 0 at hb
    have hb' : j b.toMul = 1 := Additive.ofMul.injective hb
    rcases (hker b.toMul).1 hb' with ⟨a, ha⟩
    refine ⟨Additive.ofMul a, ?_⟩
    apply Additive.toMul.injective
    exact ha
  · intro a a' ha
    apply Additive.toMul.injective
    apply hinj
    exact Additive.ofMul.injective ha
  · intro c
    rcases hsurj c.toMul with ⟨b, hb⟩
    refine ⟨Additive.ofMul b, ?_⟩
    apply Additive.toMul.injective
    exact hb

private def periodicScIsoEven
    (σ : G) {n : ℕ} [h₀ : NeZero n] (hn : Even n) :
    (periodicChainComplex (A := A) σ).sc n ≅
      subCompNormHom (Rep.ofMulDistribMulAction G A) σ :=
  HomologicalComplex.alternatingConstScIsoEven (ModuleCat.of ℤ (Additive A))
    (normHomCompSub (Rep.ofMulDistribMulAction G A) σ).zero
    (subCompNormHom (Rep.ofMulDistribMulAction G A) σ).zero
    (fun _ _ => ComplexShape.down_nat_odd_add)
    (by
      change n + 1 = (ComplexShape.down ℕ).prev n
      exact (ChainComplex.prev ℕ n).symm)
    (by
      induction n generalizing h₀ with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ n _ =>
          change (ComplexShape.down ℕ).next (n + 1) + 1 = n + 1
          rw [ChainComplex.next_nat_succ]) hn

private def periodicScIsoOdd
    (σ : G) {n : ℕ} (hn : Odd n) :
    (periodicChainComplex (A := A) σ).sc n ≅
      normHomCompSub (Rep.ofMulDistribMulAction G A) σ :=
  HomologicalComplex.alternatingConstScIsoOdd (ModuleCat.of ℤ (Additive A))
    (normHomCompSub (Rep.ofMulDistribMulAction G A) σ).zero
    (subCompNormHom (Rep.ofMulDistribMulAction G A) σ).zero
    (fun _ _ => ComplexShape.down_nat_odd_add)
    (by
      change n + 1 = (ComplexShape.down ℕ).prev n
      exact (ChainComplex.prev ℕ n).symm)
    (by
      rcases hn with ⟨m, rfl⟩
      change (ComplexShape.down ℕ).next (2 * m + 1) + 1 = 2 * m + 1
      rw [ChainComplex.next_nat_succ]) hn

private def periodicHomologyIsoEven
    (σ : G) {n : ℕ} [NeZero n] (hn : Even n) :
    (periodicChainComplex (A := A) σ).homology n ≅
      (subCompNormHom (Rep.ofMulDistribMulAction G A) σ).homology :=
  ShortComplex.homologyMapIso (periodicScIsoEven σ hn)

private def periodicHomologyIsoOdd
    (σ : G) {n : ℕ} (hn : Odd n) :
    (periodicChainComplex (A := A) σ).homology n ≅
      (normHomCompSub (Rep.ofMulDistribMulAction G A) σ).homology :=
  ShortComplex.homologyMapIso (periodicScIsoOdd σ hn)

private def periodicEvenHerbrandHMinusOneIso
    (σ : G) {n : ℕ} [NeZero n] (hn : Even n) :
    (periodicChainComplex (A := A) σ).homology n ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) :=
  periodicHomologyIsoEven σ hn ≪≫
    (subNormHomologyEquivHerbrandHMinusOne σ).toIntLinearEquiv.toModuleIso

private def periodicOddHerbrandHZeroIso
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {n : ℕ} (hn : Odd n) :
    (periodicChainComplex (A := A) σ).homology n ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G A)) :=
  periodicHomologyIsoOdd σ hn ≪≫
    (normHomologyEquivHerbrandH0 σ hgen).toIntLinearEquiv.toModuleIso

private theorem periodicScIsoEven_naturality
    (σ : G) {n : ℕ} [NeZero n] (hn : Even n)
    (f : A →* B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    ShortComplex.homologyMap (periodicScIsoEven (A := A) σ hn).inv ≫
        ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor
            (ModuleCat.{v} ℤ) (ComplexShape.down ℕ) n).map
              (periodicChainMap σ f hf)) ≫
        ShortComplex.homologyMap (periodicScIsoEven (A := B) σ hn).hom =
      ShortComplex.homologyMap (subCompNormMap σ f hf) := by
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1

private theorem periodicHomologyIsoEven_naturality
    (σ : G) {n : ℕ} [NeZero n] (hn : Even n)
    (f : A →* B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    (periodicHomologyIsoEven (A := A) σ hn).inv ≫
        HomologicalComplex.homologyMap (periodicChainMap σ f hf) n ≫
        (periodicHomologyIsoEven (A := B) σ hn).hom =
      ShortComplex.homologyMap (subCompNormMap σ f hf) :=
  periodicScIsoEven_naturality σ hn f hf

/-- Conjugating a `ModuleCat ℤ` morphism by isomorphisms identifies the
ranges of the associated multiplicatively tagged homomorphisms. -/
noncomputable def moduleCatRangeEquivOfConjugate
    {X Y X' Y' : ModuleCat.{v} ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : eX.inv ≫ f ≫ eY.hom = g) :
    MonoidHom.range f.hom.toAddMonoidHom.toMultiplicative ≃
      MonoidHom.range g.hom.toAddMonoidHom.toMultiplicative := by
  have hnat : f ≫ eY.hom = eX.hom ≫ g := by
    rw [← cancel_epi eX.inv]
    simpa only [Category.assoc, eX.inv_hom_id_assoc] using h
  have hinv : eX.inv ≫ f = g ≫ eY.inv := by
    rw [← cancel_mono eY.hom]
    simpa only [Category.assoc, eY.inv_hom_id, Category.comp_id] using h
  refine
    { toFun := fun y => ⟨Multiplicative.ofAdd (eY.hom y.1.toAdd), ?_⟩
      invFun := fun y => ⟨Multiplicative.ofAdd (eY.inv y.1.toAdd), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rcases y.2 with ⟨x, hx⟩
    refine ⟨Multiplicative.ofAdd (eX.hom x.toAdd), ?_⟩
    apply Multiplicative.toAdd.injective
    change g (eX.hom x.toAdd) = eY.hom y.1.toAdd
    have hx' : f x.toAdd = y.1.toAdd :=
      congrArg Multiplicative.toAdd hx
    rw [← hx']
    exact (congrArg (fun k : X ⟶ Y' => k x.toAdd) hnat).symm
  · rcases y.2 with ⟨x, hx⟩
    refine ⟨Multiplicative.ofAdd (eX.inv x.toAdd), ?_⟩
    apply Multiplicative.toAdd.injective
    change f (eX.inv x.toAdd) = eY.inv y.1.toAdd
    have hx' : g x.toAdd = y.1.toAdd :=
      congrArg Multiplicative.toAdd hx
    rw [← hx']
    exact congrArg (fun k : X' ⟶ Y => k x.toAdd) hinv
  · intro y
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact eY.hom_inv_id_apply y.1.toAdd
  · intro y
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact eY.inv_hom_id_apply y.1.toAdd

/-- Conjugate `ModuleCat ℤ` morphisms have ranges of the same cardinality
after multiplicatively tagging their underlying additive groups. -/
theorem moduleCatRangeCard_eq_of_conjugate
    {X Y X' Y' : ModuleCat.{v} ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : eX.inv ≫ f ≫ eY.hom = g) :
    Nat.card (MonoidHom.range
        f.hom.toAddMonoidHom.toMultiplicative) =
      Nat.card (MonoidHom.range
        g.hom.toAddMonoidHom.toMultiplicative) :=
  Nat.card_congr (moduleCatRangeEquivOfConjugate f g eX eY h)

/-- Function exactness of morphisms in `ModuleCat ℤ` gives multiplicative
exactness after tagging the underlying additive groups as multiplicative. -/
theorem mulExact_of_moduleCat_exact
    {X Y Z : ModuleCat.{v} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hexact : Function.Exact f g) :
    Function.MulExact
      f.hom.toAddMonoidHom.toMultiplicative
      g.hom.toAddMonoidHom.toMultiplicative := by
  intro y
  constructor
  · intro hy
    change g y.toAdd = 0 at hy
    rcases (hexact y.toAdd).1 hy with ⟨x, hx⟩
    refine ⟨Multiplicative.ofAdd x, ?_⟩
    apply Multiplicative.toAdd.injective
    exact hx
  · rintro ⟨x, rfl⟩
    change g (f x.toAdd) = 0
    exact (hexact (f x.toAdd)).2 ⟨x.toAdd, rfl⟩

/-- Exactness of a short complex in `ModuleCat ℤ` gives multiplicative
exactness of its two underlying homomorphisms. -/
theorem mulExact_of_moduleCat_shortComplex_exact
    {X Y Z : ModuleCat.{v} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hzero : f ≫ g = 0)
    (hexact : (ShortComplex.mk f g hzero).Exact) :
    Function.MulExact
      f.hom.toAddMonoidHom.toMultiplicative
      g.hom.toAddMonoidHom.toMultiplicative :=
  mulExact_of_moduleCat_exact f g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hexact)

/-- For an exact pair of `ModuleCat ℤ` morphisms with finite middle term,
the cardinality of the middle term is the product of the two range
cardinalities. -/
theorem moduleCat_card_eq_card_range_mul_card_range_of_exact
    {X Y Z : ModuleCat.{v} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hexact : Function.Exact f g) [Finite Y] :
    Nat.card Y =
      Nat.card (MonoidHom.range
        f.hom.toAddMonoidHom.toMultiplicative) *
      Nat.card (MonoidHom.range
        g.hom.toAddMonoidHom.toMultiplicative) := by
  exact
    monoidHom_card_eq_card_range_mul_card_range_of_exact
      f.hom.toAddMonoidHom.toMultiplicative
      g.hom.toAddMonoidHom.toMultiplicative
      (mulExact_of_moduleCat_exact f g hexact).monoidHom_ker_eq.symm

/-- Finiteness transports from the target to the source of a
`ModuleCat ℤ` isomorphism. -/
theorem finite_source_of_moduleIso
    {X Y : ModuleCat.{v} ℤ} (e : X ≅ Y) [Finite Y] :
    Finite X := by
  let e' : X ≃ Y := ((forget (ModuleCat ℤ)).mapIso e).toEquiv
  exact Finite.of_injective e' e'.injective

/-- Finiteness transports from the source to the target of a
`ModuleCat ℤ` isomorphism. -/
theorem finite_target_of_moduleIso
    {X Y : ModuleCat.{v} ℤ} (e : X ≅ Y) [Finite X] :
    Finite Y := by
  let e' : Y ≃ X := ((forget (ModuleCat ℤ)).mapIso e.symm).toEquiv
  exact Finite.of_injective e' e'.injective

/-- A `ModuleCat ℤ` isomorphism with the additive form of a commutative
group identifies their cardinalities. -/
theorem moduleCat_card_eq_of_iso
    {X : ModuleCat.{v} ℤ} {T : Type v} [CommGroup T]
    (e : X ≅ ModuleCat.of ℤ (Additive T)) :
    Nat.card X = Nat.card T :=
  Nat.card_congr ((forget (ModuleCat ℤ)).mapIso e).toEquiv


/-- In an exact pair `X → Y → Z`, finiteness of `X` and `Z` forces
finiteness of `Y`. -/
theorem finite_middle_of_exact
    {X Y Z : Type*}
    [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : Y →* Z) (hexact : MonoidHom.range f = MonoidHom.ker g)
    [Finite X] [Finite Z] :
    Finite Y := by
  apply g.finite_iff_finite_ker_range.mpr
  constructor
  · let : Finite (MonoidHom.range f) :=
      Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    rw [← hexact]
    infer_instance
  · infer_instance

/-- Finiteness of the outer integer modules in an exact pair forces the middle module finite. -/
theorem finite_middle_of_moduleCat_exact
    {X Y Z : ModuleCat.{v} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hexact : Function.Exact f g)
    [Finite X] [Finite Z] :
    Finite Y := by
  let fm : Multiplicative X →* Multiplicative Y :=
    f.hom.toAddMonoidHom.toMultiplicative
  let gm : Multiplicative Y →* Multiplicative Z :=
    g.hom.toAddMonoidHom.toMultiplicative
  exact finite_middle_of_exact
    (X := Multiplicative X) (Y := Multiplicative Y)
    (Z := Multiplicative Z) fm gm
    (mulExact_of_moduleCat_exact f g hexact).monoidHom_ker_eq.symm

private theorem finite_even_of_defined (σ : G) (hA : HerbrandQuotientDefined G A σ)
    {n : ℕ} [NeZero n] (hn : Even n) :
    Finite ((periodicChainComplex (A := A) σ).homology n) := by
  let : Finite (HerbrandHMinusOne G A σ) := hA.2
  exact finite_source_of_moduleIso (periodicEvenHerbrandHMinusOneIso σ hn)

private theorem finite_odd_of_defined (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hA : HerbrandQuotientDefined G A σ) {n : ℕ} (hn : Odd n) :
    Finite ((periodicChainComplex (A := A) σ).homology n) := by
  let : Finite (HerbrandH0 G A) := hA.1
  exact finite_source_of_moduleIso (periodicOddHerbrandHZeroIso σ hgen hn)

private theorem defined_of_finite_periodic (σ : G)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite ((periodicChainComplex (A := A) σ).homology 3)]
    [Finite ((periodicChainComplex (A := A) σ).homology 4)] :
    HerbrandQuotientDefined G A σ := by
  exact ⟨finite_target_of_moduleIso (periodicOddHerbrandHZeroIso σ hgen ⟨1, rfl⟩),
    finite_target_of_moduleIso (periodicEvenHerbrandHMinusOneIso σ ⟨2, rfl⟩)⟩

/-- Any two defined arithmetic Herbrand quotients force the third to be defined,
using exactness of the original periodic norm complex. -/
theorem herbrandQuotientDefined_anyTwo_of_periodic
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    (HerbrandQuotientDefined G A σ ∧ HerbrandQuotientDefined G B σ →
        HerbrandQuotientDefined G C σ) ∧
      (HerbrandQuotientDefined G A σ ∧ HerbrandQuotientDefined G C σ →
        HerbrandQuotientDefined G B σ) ∧
      (HerbrandQuotientDefined G B σ ∧ HerbrandQuotientDefined G C σ →
        HerbrandQuotientDefined G A σ) := by
  let S := periodicShortComplex σ i j hi hj hker
  have hS : S.ShortExact := periodicShortComplex_shortExact σ i j hi hj hker hinj hsurj
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hA, hB⟩
    let : Finite (S.X₂.homology 4) := finite_even_of_defined σ hB ⟨2, rfl⟩
    let : Finite (S.X₁.homology 3) := finite_odd_of_defined σ hgen hA ⟨1, rfl⟩
    let : Finite (S.X₂.homology 3) := finite_odd_of_defined σ hgen hB ⟨1, rfl⟩
    let : Finite (S.X₁.homology 2) := finite_even_of_defined σ hA ⟨1, rfl⟩
    have hC4 : Finite (S.X₃.homology 4) := finite_middle_of_moduleCat_exact
      (HomologicalComplex.homologyMap S.g 4) (hS.δ 4 3 (by decide))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (hS.homology_exact₃ 4 3 (by decide)))
    have hC3 : Finite (S.X₃.homology 3) := finite_middle_of_moduleCat_exact
      (HomologicalComplex.homologyMap S.g 3) (hS.δ 3 2 (by decide))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (hS.homology_exact₃ 3 2 (by decide)))
    exact @defined_of_finite_periodic G C _ _ _ _ σ hgen hC3 hC4
  · rintro ⟨hA, hC⟩
    let : Finite (S.X₁.homology 3) := finite_odd_of_defined σ hgen hA ⟨1, rfl⟩
    let : Finite (S.X₃.homology 3) := finite_odd_of_defined σ hgen hC ⟨1, rfl⟩
    let : Finite (S.X₁.homology 4) := finite_even_of_defined σ hA ⟨2, rfl⟩
    let : Finite (S.X₃.homology 4) := finite_even_of_defined σ hC ⟨2, rfl⟩
    have hB3 : Finite (S.X₂.homology 3) := finite_middle_of_moduleCat_exact
      (HomologicalComplex.homologyMap S.f 3) (HomologicalComplex.homologyMap S.g 3)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (hS.homology_exact₂ 3))
    have hB4 : Finite (S.X₂.homology 4) := finite_middle_of_moduleCat_exact
      (HomologicalComplex.homologyMap S.f 4) (HomologicalComplex.homologyMap S.g 4)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (hS.homology_exact₂ 4))
    exact @defined_of_finite_periodic G B _ _ _ _ σ hgen hB3 hB4
  · rintro ⟨hB, hC⟩
    let : Finite (S.X₃.homology 4) := finite_even_of_defined σ hC ⟨2, rfl⟩
    let : Finite (S.X₂.homology 3) := finite_odd_of_defined σ hgen hB ⟨1, rfl⟩
    let : Finite (S.X₃.homology 5) := finite_odd_of_defined σ hgen hC ⟨2, rfl⟩
    let : Finite (S.X₂.homology 4) := finite_even_of_defined σ hB ⟨2, rfl⟩
    have hA3 : Finite (S.X₁.homology 3) := finite_middle_of_moduleCat_exact
      (hS.δ 4 3 (by decide)) (HomologicalComplex.homologyMap S.f 3)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (hS.homology_exact₁ 4 3 (by decide)))
    have hA4 : Finite (S.X₁.homology 4) := finite_middle_of_moduleCat_exact
      (hS.δ 5 4 (by decide)) (HomologicalComplex.homologyMap S.f 4)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (hS.homology_exact₁ 5 4 (by decide)))
    exact @defined_of_finite_periodic G A _ _ _ _ σ hgen hA3 hA4

/-- The original exact periodic norm sequence gives its six-term cardinality identity. -/
theorem herbrand_exact_cardinality_identity
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    Nat.card (HerbrandH0 G B) *
        Nat.card (HerbrandHMinusOne G A σ) *
        Nat.card (HerbrandHMinusOne G C σ) =
      Nat.card (HerbrandH0 G A) *
        Nat.card (HerbrandH0 G C) *
        Nat.card (HerbrandHMinusOne G B σ) := by
  let S := periodicShortComplex σ i j hi hj hker
  have hS : S.ShortExact :=
    periodicShortComplex_shortExact σ i j hi hj hker hinj hsurj
  let eA4 : S.X₁.homology 4 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := A) (n := 4) σ (⟨2, rfl⟩ : Even 4)
  let eB4 : S.X₂.homology 4 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G B σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := B) (n := 4) σ (⟨2, rfl⟩ : Even 4)
  let eC4 : S.X₃.homology 4 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G C σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := C) (n := 4) σ (⟨2, rfl⟩ : Even 4)
  let eA3 : S.X₁.homology 3 ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G A)) := by
    exact periodicOddHerbrandHZeroIso
      (G := G) (A := A) (n := 3) σ hgen (⟨1, rfl⟩ : Odd 3)
  let eB3 : S.X₂.homology 3 ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G B)) := by
    exact periodicOddHerbrandHZeroIso
      (G := G) (A := B) (n := 3) σ hgen (⟨1, rfl⟩ : Odd 3)
  let eC3 : S.X₃.homology 3 ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G C)) := by
    exact periodicOddHerbrandHZeroIso
      (G := G) (A := C) (n := 3) σ hgen (⟨1, rfl⟩ : Odd 3)
  let eA2 : S.X₁.homology 2 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := A) (n := 2) σ (⟨1, rfl⟩ : Even 2)
  let eB2 : S.X₂.homology 2 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G B σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := B) (n := 2) σ (⟨1, rfl⟩ : Even 2)
  let pA4 : S.X₁.homology 4 ≅
      (subCompNormHom
        (Rep.ofMulDistribMulAction G A) σ).homology := by
    exact periodicHomologyIsoEven
      (G := G) (A := A) σ (⟨2, rfl⟩ : Even 4)
  let pB4 : S.X₂.homology 4 ≅
      (subCompNormHom
        (Rep.ofMulDistribMulAction G B) σ).homology := by
    exact periodicHomologyIsoEven
      (G := G) (A := B) σ (⟨2, rfl⟩ : Even 4)
  let pA2 : S.X₁.homology 2 ≅
      (subCompNormHom
        (Rep.ofMulDistribMulAction G A) σ).homology := by
    exact periodicHomologyIsoEven
      (G := G) (A := A) σ (⟨1, rfl⟩ : Even 2)
  let pB2 : S.X₂.homology 2 ≅
      (subCompNormHom
        (Rep.ofMulDistribMulAction G B) σ).homology := by
    exact periodicHomologyIsoEven
      (G := G) (A := B) σ (⟨1, rfl⟩ : Even 2)
  let : Finite (S.X₁.homology 4) := finite_source_of_moduleIso eA4
  let : Finite (S.X₂.homology 4) := finite_source_of_moduleIso eB4
  let : Finite (S.X₃.homology 4) := finite_source_of_moduleIso eC4
  let : Finite (S.X₁.homology 3) := finite_source_of_moduleIso eA3
  let : Finite (S.X₂.homology 3) := finite_source_of_moduleIso eB3
  let : Finite (S.X₃.homology 3) := finite_source_of_moduleIso eC3
  let : Finite (S.X₁.homology 2) := finite_source_of_moduleIso eA2
  let f4 := HomologicalComplex.homologyMap S.f 4
  let g4 := HomologicalComplex.homologyMap S.g 4
  let δ43 := hS.δ 4 3 (by decide)
  let f3 := HomologicalComplex.homologyMap S.f 3
  let g3 := HomologicalComplex.homologyMap S.g 3
  let δ32 := hS.δ 3 2 (by decide)
  let f2 := HomologicalComplex.homologyMap S.f 2
  have hexactB4 : Function.Exact f4 g4 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₂ 4)
  have hexactC4 : Function.Exact g4 δ43 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₃ 4 3 (by decide))
  have hexactA3 : Function.Exact δ43 f3 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₁ 4 3 (by decide))
  have hexactB3 : Function.Exact f3 g3 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₂ 3)
  have hexactC3 : Function.Exact g3 δ32 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₃ 3 2 (by decide))
  have hexactA2 : Function.Exact δ32 f2 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₁ 3 2 (by decide))
  have hB4 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact f4 g4 hexactB4
  have hC4 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact g4 δ43 hexactC4
  have hA3 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact δ43 f3 hexactA3
  have hB3 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact f3 g3 hexactB3
  have hC3 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact g3 δ32 hexactC3
  have hA2 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact δ32 f2 hexactA2
  let q := ShortComplex.homologyMap (subCompNormMap σ i hi)
  have hf4q :
      Nat.card (MonoidHom.range
          f4.hom.toAddMonoidHom.toMultiplicative) =
        Nat.card (MonoidHom.range
          q.hom.toAddMonoidHom.toMultiplicative) := by
    apply moduleCatRangeCard_eq_of_conjugate f4 q pA4 pB4
    exact periodicHomologyIsoEven_naturality
      σ (⟨2, rfl⟩ : Even 4) i hi
  have hf2q :
      Nat.card (MonoidHom.range
          f2.hom.toAddMonoidHom.toMultiplicative) =
        Nat.card (MonoidHom.range
          q.hom.toAddMonoidHom.toMultiplicative) := by
    apply moduleCatRangeCard_eq_of_conjugate f2 q pA2 pB2
    exact periodicHomologyIsoEven_naturality σ (⟨1, rfl⟩ : Even 2) i hi
  have hrange :
      Nat.card (MonoidHom.range
          f4.hom.toAddMonoidHom.toMultiplicative) =
        Nat.card (MonoidHom.range
          f2.hom.toAddMonoidHom.toMultiplicative) :=
    hf4q.trans hf2q.symm
  have hperiodic :
      Nat.card (S.X₂.homology 3) *
          Nat.card (S.X₁.homology 2) *
          Nat.card (S.X₃.homology 4) =
        Nat.card (S.X₁.homology 3) *
          Nat.card (S.X₃.homology 3) *
          Nat.card (S.X₂.homology 4) := by
    rw [hB3, hA2, hC4, hA3, hC3, hB4, ← hrange]
    ac_rfl
  have hcB4 := moduleCat_card_eq_of_iso eB4
  have hcC4 := moduleCat_card_eq_of_iso eC4
  have hcA3 := moduleCat_card_eq_of_iso eA3
  have hcB3 := moduleCat_card_eq_of_iso eB3
  have hcC3 := moduleCat_card_eq_of_iso eC3
  have hcA2 := moduleCat_card_eq_of_iso eA2
  calc
    _ = Nat.card (S.X₂.homology 3) *
          Nat.card (S.X₁.homology 2) *
          Nat.card (S.X₃.homology 4) := by
      rw [hcB3, hcA2, hcC4]
    _ = Nat.card (S.X₁.homology 3) *
          Nat.card (S.X₃.homology 3) *
          Nat.card (S.X₂.homology 4) :=
      hperiodic
    _ = _ := by
      rw [hcA3, hcC3, hcB4]


end CyclicCohomology.ProfiniteCohomology.Herbrand
