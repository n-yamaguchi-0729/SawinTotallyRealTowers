import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.EmptySupportKummerCokernel
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace

set_option autoImplicit false
/-!
# Characters of the finite valuation vector of an idele

Any algebraic functional on the product of mod-`p` valuation defects gives a continuous
idele character. No continuity of the functional on that product is required: its composite
vanishes on the open subgroup of ideles integral at every finite place. On principal ideles
the character agrees with the dual of global finite-valuation localization.
-/

open scoped NumberField WithZero Classical

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open IsDedekindDomain KummerTheory IdeleGroup

variable (K : Type*) [Field K] [NumberField K] (p : ℕ)

/-- All mod-`p` finite valuations of an idele, with the same sign as global valuations. -/
def ideleFiniteValuationDefectHom : IdeleGroup K →* FiniteValuationDefect K p :=
  MonoidHom.pi fun v =>
    ((-Int.castAddHom (ZMod p)).toMultiplicative).comp
      ((FiniteIdeleGroup.localOrder v).comp (IdeleGroup.finiteComponent v))

/-- Integral ideles have zero finite-valuation defect. -/
theorem ideleFiniteValuationDefectHom_eq_one_of_supportedAt_empty
    (a : IdeleGroup K) (ha : a ∈ IdeleGroup.supportedAt (K := K) ∅) :
    ideleFiniteValuationDefectHom K p a = 1 := by
  funext v
  apply Multiplicative.toAdd.injective
  change -((FiniteIdeleGroup.localOrder v (a.2 v)).toAdd : ZMod p) = 0
  rw [(FiniteIdeleGroup.localOrder_eq_zero_iff v (a.2 v)).2
    ((IdeleGroup.mem_supportedAt_iff ∅ a).1 ha v (Set.notMem_empty v))]
  simp only [Int.cast_zero, neg_zero]

variable [Fact p.Prime]

/-- The valuation defect of a principal idele is the global power-class localization. -/
theorem ideleFiniteValuationDefectHom_principalIdele (a : Kˣ) :
    ideleFiniteValuationDefectHom K p (principalIdele K a) =
      absolutePowerClassFiniteValuationLocalizationMonoidHom K p
        (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a) := by
  funext v
  apply Multiplicative.toAdd.injective
  change -((FiniteIdeleGroup.localOrder v
      (IdeleGroup.finiteComponent v (principalIdele K a))).toAdd : ZMod p) =
    (v.valuationOfNeZeroMod p
      (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a)).toAdd
  rw [FiniteIdeleGroup.localOrder_apply, IdeleGroup.finiteComponent_principalIdele]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    ← HeightOneSpectrum.valuationOfNeZero_eq]
  simp only [WithZero.log, Int.cast_neg, neg_neg]
  rfl

/-- A one-place idele has only its own valuation coordinate. -/
theorem ideleFiniteValuationDefectHom_finitePlace
    (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ideleFiniteValuationDefectHom K p (finitePlaceIdele v a) =
      Pi.mulSingle v (Multiplicative.ofAdd
        (-((FiniteIdeleGroup.localOrder v a).toAdd : ZMod p))) := by
  funext w
  by_cases hw : w = v
  · subst w
    rw [Pi.mulSingle_eq_same]
    change Multiplicative.ofAdd (-((FiniteIdeleGroup.localOrder v
      (finiteComponent v (finitePlaceIdele v a))).toAdd : ZMod p)) = _
    rw [finitePlaceIdele_finiteComponent_same]
  · rw [Pi.mulSingle_eq_of_ne hw]
    change Multiplicative.ofAdd (-((FiniteIdeleGroup.localOrder w
      (finiteComponent w (finitePlaceIdele v a))).toAdd : ZMod p)) = 1
    rw [finitePlaceIdele_finiteComponent_of_ne v w a hw, map_one]
    simp only [toAdd_one, Int.cast_zero, neg_zero, ofAdd_zero]

omit [Fact p.Prime] in
/-- An integral unit at one finite place defines an integral idele. -/
theorem finitePlaceIdele_mem_supportedAt_empty_of_integral
    (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ)
    (ha : a ∈ (v.adicCompletionIntegers K).units) :
    finitePlaceIdele v a ∈ IdeleGroup.supportedAt (K := K) ∅ := by
  rw [mem_supportedAt_iff]
  intro w _
  change finiteComponent w (finitePlaceIdele v a) ∈ _
  by_cases hw : w = v
  · subst w
    rw [finitePlaceIdele_finiteComponent_same]
    exact ha
  · rw [finitePlaceIdele_finiteComponent_of_ne v w a hw]
    exact Subgroup.one_mem _

local instance ideleValuationCharacterTopology : TopologicalSpace (ZMod p) := ⊥

local instance ideleValuationCharacterDiscreteTopology : DiscreteTopology (ZMod p) :=
  discreteTopology_bot _

/-- An algebraic valuation functional, evaluated on the finite valuations of an idele. -/
def ideleValuationCharacterMonoidHom
    (φ : Module.Dual (ZMod p) (FiniteValuationDefectModP K p)) :
    IdeleGroup K →* Multiplicative (ZMod p) :=
  (show Additive (FiniteValuationDefect K p) →+ ZMod p from
    φ.toAddMonoidHom).toMultiplicativeRight.comp (ideleFiniteValuationDefectHom K p)

/-- A valuation character vanishes on ideles integral at every finite place. -/
theorem ideleValuationCharacterMonoidHom_eq_one_of_supportedAt_empty
    (φ : Module.Dual (ZMod p) (FiniteValuationDefectModP K p))
    (a : IdeleGroup K) (ha : a ∈ IdeleGroup.supportedAt (K := K) ∅) :
    ideleValuationCharacterMonoidHom K p φ a = 1 := by
  change Multiplicative.ofAdd (φ (Additive.ofMul
    (ideleFiniteValuationDefectHom K p a))) = 1
  rw [ideleFiniteValuationDefectHom_eq_one_of_supportedAt_empty K p a ha]
  change Multiplicative.ofAdd (φ 0) = 1
  rw [map_zero]
  rfl

/-- The open integral-idele subgroup proves continuity, without any topology on the dual. -/
theorem ideleValuationCharacterMonoidHom_continuous
    (φ : Module.Dual (ZMod p) (FiniteValuationDefectModP K p)) :
    Continuous (ideleValuationCharacterMonoidHom K p φ) := by
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def, map_one]
  intro V hV
  have hUopen : IsOpen ((IdeleGroup.supportedAt (K := K) ∅ :
      Subgroup (IdeleGroup K)) : Set (IdeleGroup K)) := by
    simpa only [Finset.coe_empty] using
      IdeleGroup.isOpen_supportedAt (K := K) (∅ : Finset (HeightOneSpectrum (𝓞 K)))
  apply Filter.mem_of_superset
    (hUopen.mem_nhds (IdeleGroup.supportedAt (K := K) ∅).one_mem)
  intro a ha
  change ideleValuationCharacterMonoidHom K p φ a ∈ V
  rw [ideleValuationCharacterMonoidHom_eq_one_of_supportedAt_empty K p φ a ha]
  exact mem_of_mem_nhds hV

/-- The continuous idele character furnished by a finite-valuation functional. -/
def ideleValuationCharacter
    (φ : Module.Dual (ZMod p) (FiniteValuationDefectModP K p)) :
    IdeleGroup K →ₜ* Multiplicative (ZMod p) :=
  ⟨ideleValuationCharacterMonoidHom K p φ,
    ideleValuationCharacterMonoidHom_continuous K p φ⟩

/-- On principal ideles this is exactly the dualized global valuation map. -/
theorem ideleValuationCharacter_principalIdele
    (φ : Module.Dual (ZMod p) (FiniteValuationDefectModP K p)) (a : Kˣ) :
    (ideleValuationCharacter K p φ (principalIdele K a)).toAdd =
      finiteValuationLocalizationDual K p φ
        (Additive.ofMul (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a)) := by
  change φ (Additive.ofMul (ideleFiniteValuationDefectHom K p (principalIdele K a))) = _
  rw [ideleFiniteValuationDefectHom_principalIdele K p a]
  rfl

/-- Valuation characters kill all integral local units at every finite place. -/
theorem ideleValuationCharacter_finitePlace_integral
    (φ : Module.Dual (ZMod p) (FiniteValuationDefectModP K p))
    (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ)
    (ha : a ∈ (v.adicCompletionIntegers K).units) :
    ideleValuationCharacter K p φ (finitePlaceIdele v a) = 1 :=
  ideleValuationCharacterMonoidHom_eq_one_of_supportedAt_empty K p φ _
    (finitePlaceIdele_mem_supportedAt_empty_of_integral K v a ha)

end ClassFieldTower.Martinet.Shafarevich
