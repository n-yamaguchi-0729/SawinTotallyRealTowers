import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealRadicalCyclotomicBase
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.LocalValuationKummerDual
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteKummerH1Linear
import ProCGroups.ProP.ContinuousH1

set_option autoImplicit false
/-!
# Local Kummer H¹ over the cyclotomic base

The cyclotomic base used by the ideal-radical construction contains the required primitive
`p`-th roots.  At every finite place, those roots remain primitive in the adic completion, so
absolute Kummer theory identifies local power classes with continuous degree-one characters of
the completion's absolute Galois group.

This is the intrinsic-local endpoint of the desired finite-place comparison.  Transport to the
chosen global decomposition subgroup still requires a topological local--global Galois
equivalence; the available localization comparison is only a `MulEquiv`.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP KummerTheory

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- The ideal-radical cyclotomic base with primality supplied by the ambient `Fact`. -/
abbrev FinitePlaceCyclotomicBase :=
  IdealRadicalCyclotomicBase F p (Fact.out : p.Prime)

local instance cyclotomicBaseFiniteDimensional :
    FiniteDimensional F (FinitePlaceCyclotomicBase F p) :=
  finiteDimensional_idealRadicalCyclotomicBase
    F p (Fact.out : p.Prime)

local instance cyclotomicBaseNumberField : NumberField (FinitePlaceCyclotomicBase F p) :=
  NumberField.of_module_finite F (FinitePlaceCyclotomicBase F p)

local instance finitePlaceCyclotomicKummerCharacterTopology :
    TopologicalSpace (Multiplicative (ZMod p)) := ⊥

local instance finitePlaceCyclotomicKummerCharacterDiscreteTopology :
    DiscreteTopology (Multiplicative (ZMod p)) :=
  discreteTopology_bot _

local instance finitePlaceCyclotomicKummerH1Topology (q : ℕ) :
    TopologicalSpace (ZMod q) := ⊥

local instance finitePlaceCyclotomicKummerH1DiscreteTopology (q : ℕ) :
    DiscreteTopology (ZMod q) :=
  discreteTopology_bot _

local instance finitePlaceCyclotomicKummerH1Module
    {q : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := G)) :=
  continuousH1ZModModule

/-- A primitive `p`-th root in the cyclotomic base stays primitive in every finite-place
completion. -/
theorem finitePlaceCyclotomicCompletion_primitiveRoots_nonempty
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p))) :
    (primitiveRoots p
      (v.adicCompletion (FinitePlaceCyclotomicBase F p))).Nonempty := by
  obtain ⟨zeta, hzeta⟩ :=
    idealRadicalCyclotomicBase_primitiveRoots_nonempty
      F p (Fact.out : p.Prime)
  refine ⟨algebraMap (FinitePlaceCyclotomicBase F p)
    (v.adicCompletion (FinitePlaceCyclotomicBase F p)) zeta, ?_⟩
  apply (mem_primitiveRoots (Fact.out : p.Prime).pos).2
  exact ((mem_primitiveRoots (Fact.out : p.Prime).pos).1 hzeta).map_of_injective
    (algebraMap (FinitePlaceCyclotomicBase F p)
      (v.adicCompletion (FinitePlaceCyclotomicBase F p))).injective

/-- Local `p`-power classes at a finite place of the cyclotomic base are linearly equivalent to
continuous multiplicative mod-`p` characters of the completion's absolute Galois group. -/
noncomputable def finitePlaceCyclotomicCompletionKummerLinearEquiv
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p))) :
    FinitePlaceLocalPowerClassModP (FinitePlaceCyclotomicBase F p) p v ≃ₗ[ZMod p]
      absoluteContinuousZModCharacterModP
        (v.adicCompletion (FinitePlaceCyclotomicBase F p)) p :=
  absoluteKummerContinuousZModCharacterLinearEquiv
    (v.adicCompletion (FinitePlaceCyclotomicBase F p)) p
    (finitePlaceCyclotomicCompletion_primitiveRoots_nonempty F p v)

/-- Reinterpret continuous multiplicative mod-`p` characters as additive continuous `H¹`
classes. -/
noncomputable def finitePlaceCyclotomicCompletionCharacterH1LinearEquiv
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p))) :
    absoluteContinuousZModCharacterModP
        (v.adicCompletion (FinitePlaceCyclotomicBase F p)) p ≃ₗ[ZMod p]
      ContinuousH1ZMod
        (p := p)
        (G := Field.absoluteGaloisGroup
          (v.adicCompletion (FinitePlaceCyclotomicBase F p))) := by
  let G := Field.absoluteGaloisGroup
    (v.adicCompletion (FinitePlaceCyclotomicBase F p))
  letI : Module (ZMod p)
      (Additive (G →ₜ* Multiplicative (ZMod p))) :=
    additiveZModModuleOfPowEqOne p
      (absoluteContinuousZModCharacter_pow_eq_one
        (v.adicCompletion (FinitePlaceCyclotomicBase F p)) p)
  let e : Additive (G →ₜ* Multiplicative (ZMod p)) ≃+
      ContinuousH1ZMod (p := p) (G := G) :=
    { toFun := fun chi ↦ h1OfCharacter (Additive.toMul chi)
      invFun := fun chi ↦ Additive.ofMul (characterOfH1 chi)
      left_inv := fun chi ↦ by ext sigma; rfl
      right_inv := fun chi ↦ by ext sigma; rfl
      map_add' := fun chi psi ↦ by ext sigma; rfl }
  exact
    { e with
      map_smul' := ZMod.map_smul e }

@[simp]
theorem finitePlaceCyclotomicCompletionCharacterH1LinearEquiv_apply
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p)))
    (chi : absoluteContinuousZModCharacterModP
      (v.adicCompletion (FinitePlaceCyclotomicBase F p)) p)
    (sigma : Field.absoluteGaloisGroup
      (v.adicCompletion (FinitePlaceCyclotomicBase F p))) :
    finitePlaceCyclotomicCompletionCharacterH1LinearEquiv F p v chi
        (Additive.ofMul sigma) =
      (Additive.toMul
        (show Additive
            (Field.absoluteGaloisGroup
                (v.adicCompletion (FinitePlaceCyclotomicBase F p)) →ₜ*
              Multiplicative (ZMod p))
          from chi) sigma).toAdd :=
  rfl

/-- Intrinsic local Kummer theory in the additive continuous-`H¹` convention used by the
finite-place localization layer. -/
noncomputable def finitePlaceCyclotomicCompletionKummerH1LinearEquiv
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p))) :
    FinitePlaceLocalPowerClassModP (FinitePlaceCyclotomicBase F p) p v ≃ₗ[ZMod p]
      ContinuousH1ZMod
        (p := p)
        (G := Field.absoluteGaloisGroup
          (v.adicCompletion (FinitePlaceCyclotomicBase F p))) :=
  (finitePlaceCyclotomicCompletionKummerLinearEquiv F p v).trans
    (finitePlaceCyclotomicCompletionCharacterH1LinearEquiv F p v)

@[simp]
theorem finitePlaceCyclotomicCompletionKummerH1LinearEquiv_apply
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p)))
    (x : FinitePlaceLocalPowerClassModP (FinitePlaceCyclotomicBase F p) p v)
    (sigma : Field.absoluteGaloisGroup
      (v.adicCompletion (FinitePlaceCyclotomicBase F p))) :
    finitePlaceCyclotomicCompletionKummerH1LinearEquiv F p v x
        (Additive.ofMul sigma) =
      (Additive.toMul
        (show Additive
            (Field.absoluteGaloisGroup
                (v.adicCompletion (FinitePlaceCyclotomicBase F p)) →ₜ*
              Multiplicative (ZMod p))
          from finitePlaceCyclotomicCompletionKummerLinearEquiv F p v x)
        sigma).toAdd :=
  rfl

/-- The normalized finite-place valuation, transported across intrinsic local Kummer `H¹`. -/
noncomputable def finitePlaceCyclotomicCompletionH1Valuation
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p))) :
    ContinuousH1ZMod
        (p := p)
        (G := Field.absoluteGaloisGroup
          (v.adicCompletion (FinitePlaceCyclotomicBase F p))) →ₗ[ZMod p]
      ZMod p :=
  (finitePlaceLocalPowerClassValuation (FinitePlaceCyclotomicBase F p) p v).comp
    (finitePlaceCyclotomicCompletionKummerH1LinearEquiv F p v).symm.toLinearMap

/-- Under local Kummer `H¹`, the cohomological valuation coordinate is exactly the normalized
adic valuation of the originating local power class. -/
@[simp]
theorem finitePlaceCyclotomicCompletionH1Valuation_kummer
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p)))
    (x : FinitePlaceLocalPowerClassModP (FinitePlaceCyclotomicBase F p) p v) :
    finitePlaceCyclotomicCompletionH1Valuation F p v
        (finitePlaceCyclotomicCompletionKummerH1LinearEquiv F p v x) =
      finitePlaceLocalPowerClassValuation (FinitePlaceCyclotomicBase F p) p v x := by
  simp [finitePlaceCyclotomicCompletionH1Valuation]

/-- The transported valuation on intrinsic local `H¹` is surjective. -/
theorem finitePlaceCyclotomicCompletionH1Valuation_surjective
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p))) :
    Function.Surjective
      (finitePlaceCyclotomicCompletionH1Valuation F p v) := by
  intro a
  obtain ⟨x, hx⟩ :=
    finitePlaceLocalPowerClassValuation_surjective
      (FinitePlaceCyclotomicBase F p) p v a
  refine ⟨finitePlaceCyclotomicCompletionKummerH1LinearEquiv F p v x, ?_⟩
  simpa using hx

end ClassFieldTower.Martinet.Shafarevich
