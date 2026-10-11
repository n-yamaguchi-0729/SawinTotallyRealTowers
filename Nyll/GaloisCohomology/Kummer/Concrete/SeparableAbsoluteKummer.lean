/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.SeparableKummerH1
import Nyll.GaloisCohomology.Kummer.Concrete.FiniteDualSeparation
import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Topology.Instances.ZMod

/-!
# Absolute constant-coefficient Kummer theory through the separable closure

The actual Krull restriction equivalence transfers separable Kummer characters
to the existing absolute Galois group. The exponent need only be nonzero in
the base field; no characteristic-zero or perfectness assumption is needed.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

-- Four group carriers and their four topologies; no new data instances.
private def continuousCharacterDomainCoefficientsEquiv
    {G H A B : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B]
    (e : G ≃ₜ* H) (d : A ≃ₜ* B) :
    (H →ₜ* A) ≃* (G →ₜ* B) where
  toFun f :=
    { toMonoidHom := d.toMulEquiv.toMonoidHom.comp
        (f.toMonoidHom.comp e.toMulEquiv.toMonoidHom)
      continuous_toFun := d.continuous.comp (f.continuous.comp e.continuous) }
  invFun f :=
    { toMonoidHom := d.symm.toMulEquiv.toMonoidHom.comp
        (f.toMonoidHom.comp e.symm.toMulEquiv.toMonoidHom)
      continuous_toFun := d.symm.continuous.comp (f.continuous.comp e.symm.continuous) }
  left_inv f := by
    apply ContinuousMonoidHom.ext
    intro h
    change d.symm (d (f (e (e.symm h)))) = f h
    rw [ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.symm_apply_apply]
  right_inv f := by
    apply ContinuousMonoidHom.ext
    intro g
    change d (d.symm (f (e.symm (e g)))) = f g
    rw [ContinuousMulEquiv.symm_apply_apply, ContinuousMulEquiv.apply_symm_apply]
  map_mul' f g := by
    apply ContinuousMonoidHom.ext
    intro x
    exact map_mul d (f (e x)) (g (e x))

variable (K : Type*) [Field K]

/-- The chosen primitive base root identifies separable-closure roots with
constant cyclic coefficients, using the canonical discrete topologies. -/
def separableDiscreteNthRootsContinuousMulEquivMultiplicativeZMod
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    DiscreteNthRootsSubgroup (SeparableClosure K) (n : ℕ) ≃ₜ*
      Multiplicative (ZMod (n : ℕ)) := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let ζ : K := hmu.choose
  have hζ : IsPrimitiveRoot ζ (n : ℕ) :=
    (mem_primitiveRoots n.pos).mp hmu.choose_spec
  let hζunit := hζ.isUnit_unit' n.ne_zero
  refine
    { toMulEquiv :=
        (nthRootsSubgroupEquivOfPrimitiveRoots K (SeparableClosure K) n hmu).symm.trans
          ((nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)).trans
            ((MulEquiv.subgroupCongr hζunit.zpowers_eq.symm).trans
              hζunit.zmodEquivZPowers.symm.toMultiplicativeRight))
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- Absolute Kummer theory with constant mod-n coefficients for any field
whose characteristic does not divide n. -/
def separableAbsoluteKummerContinuousZModCharacterEquiv
    (n : ℕ+) [NeZero ((n : ℕ) : K)]
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range ≃*
      (Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod (n : ℕ))) :=
  (separableKummerContinuousNthRootsCharacterEquiv K n hmu).trans
    (continuousCharacterDomainCoefficientsEquiv
      (ValuationTheory.Completion.separableClosureAutContinuousEquiv K)
      (separableDiscreteNthRootsContinuousMulEquivMultiplicativeZMod K n hmu))

/-- Evaluation is the existing separable Kummer character on the actual
restriction of the absolute automorphism, followed by the root coefficient map. -/
theorem separableAbsoluteKummerContinuousZModCharacterEquiv_apply
    (n : ℕ+) [NeZero ((n : ℕ) : K)]
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
    (σ : Field.absoluteGaloisGroup K) :
    separableAbsoluteKummerContinuousZModCharacterEquiv K n hmu a σ =
      separableDiscreteNthRootsContinuousMulEquivMultiplicativeZMod K n hmu
        (separableKummerContinuousNthRootsCharacterEquiv K n hmu a
          (ValuationTheory.Completion.separableClosureAutContinuousEquiv K σ)) := rfl

end ClassFieldTower.Martinet.Shafarevich
