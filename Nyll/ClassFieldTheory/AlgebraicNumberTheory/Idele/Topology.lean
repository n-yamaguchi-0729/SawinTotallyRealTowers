/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.RestrictedProductUnitsTopology

/-!
# The idele topology

The standard adele-unit topology is equivalent to the product of the
archimedean unit topology and the restricted-product topology on finite
coordinates. In particular each local projection is continuous.
-/

@[expose] public section

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

/-- The local integral-unit subgroup is open in the multiplicative group of a
finite completion. -/
theorem isOpen_finiteLocalUnits (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen
      ((v.adicCompletionIntegers K).units :
        Set (v.adicCompletion K)ˣ) :=
  Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)

instance finiteLocalUnitsOpen :
    Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen
        ((v.adicCompletionIntegers K).units :
          Set (v.adicCompletion K)ˣ)) :=
  ⟨isOpen_finiteLocalUnits K⟩

instance finiteIdeleGroupIsTopologicalGroup :
    IsTopologicalGroup (FiniteIdeleGroup K) :=
  inferInstance

instance finiteIdeleGroupT2Space :
    T2Space (FiniteIdeleGroup K) :=
  inferInstance

instance infiniteAdeleRingT2Space :
    T2Space (NumberField.InfiniteAdeleRing K) := by
  change T2Space ((v : InfinitePlace K) → v.Completion)
  infer_instance

instance infiniteIdeleGroupT2Space :
    T2Space (InfiniteIdeleGroup K) :=
  inferInstance

namespace IdeleGroup

/-- The finite restricted-product idèles and finite adele units are
canonically isomorphic as topological groups. -/
noncomputable def finiteEquivFiniteAdeleUnitsContinuousMulEquiv :
    FiniteIdeleGroup K ≃ₜ*
      (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ :=
  (RestrictedProduct.unitsContinuousMulEquiv
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (B := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletionIntegers K)
    (fun _ => Valued.isOpen_valuationSubring _)).symm

/-- The topological and algebraic finite-idèle comparisons agree pointwise. -/
@[simp]
theorem finiteEquivFiniteAdeleUnitsContinuousMulEquiv_apply
    (a : FiniteIdeleGroup K) :
    finiteEquivFiniteAdeleUnitsContinuousMulEquiv K a =
      finiteEquivFiniteAdeleUnits a :=
  rfl

/-- The algebraic finite-idèle comparison is continuous in the forward
direction. -/
theorem continuous_finiteEquivFiniteAdeleUnits :
    Continuous (finiteEquivFiniteAdeleUnits (K := K)) := by
  exact (finiteEquivFiniteAdeleUnitsContinuousMulEquiv K).continuous.congr
    (finiteEquivFiniteAdeleUnitsContinuousMulEquiv_apply K)

variable {K}

/-- The standard idele topology agrees with the product topology on its two parts. -/
noncomputable def componentsContinuousMulEquiv :
    IdeleGroup K ≃ₜ* (InfiniteIdeleGroup K × FiniteIdeleGroup K) := by
  let e := finiteEquivFiniteAdeleUnitsContinuousMulEquiv K
  let h : IdeleGroup K ≃ₜ InfiniteIdeleGroup K × FiniteIdeleGroup K :=
    Homeomorph.prodUnits.trans ((Homeomorph.refl _).prodCongr e.toHomeomorph.symm)
  exact
    { toMulEquiv := componentsEquiv
      continuous_toFun := h.continuous
      continuous_invFun := h.symm.continuous }

/-- The standard idele group is Hausdorff in its native topology. -/
instance : T2Space (IdeleGroup K) :=
  (componentsContinuousMulEquiv (K := K)).toHomeomorph.isEmbedding.t2Space

/-- The archimedean part is continuous in the idele topology. -/
theorem continuous_infinitePart : Continuous (infinitePart (K := K)) := by
  refine (componentsContinuousMulEquiv (K := K)).continuous.fst.congr ?_
  intro a
  exact congrArg Prod.fst (componentsEquiv_apply a)

/-- The restricted finite coordinates are continuous in the idele topology. -/
theorem continuous_finiteCoordinates : Continuous (finiteCoordinates (K := K)) := by
  refine (componentsContinuousMulEquiv (K := K)).continuous.snd.congr ?_
  intro a
  exact congrArg Prod.snd (componentsEquiv_apply a)

/-- The product of the two parts is an open chart for the idele group. -/
theorem isOpenEmbedding_ofComponents :
    Topology.IsOpenEmbedding
      (fun a : InfiniteIdeleGroup K × FiniteIdeleGroup K => ofComponents a.1 a.2) := by
  let e := (componentsContinuousMulEquiv (K := K)).symm.toHomeomorph
  have he : (fun a : InfiniteIdeleGroup K × FiniteIdeleGroup K => ofComponents a.1 a.2) = e := by
    funext a
    exact (componentsEquiv_symm_apply a).symm
  rw [he]
  exact e.isOpenEmbedding

/-- Assembling the archimedean and finite parts is continuous. -/
theorem continuous_ofComponents :
    Continuous (fun a : InfiniteIdeleGroup K × FiniteIdeleGroup K => ofComponents a.1 a.2) :=
  isOpenEmbedding_ofComponents.continuous

/-- Evaluation at an archimedean place is a continuous homomorphism. -/
def infiniteComponentContinuous (v : InfinitePlace K) :
    IdeleGroup K →ₜ* v.Completionˣ where
  __ := infiniteComponent v
  continuous_toFun :=
    (continuous_apply v).comp
      (ContinuousMulEquiv.piUnits.continuous.comp continuous_infinitePart)

/-- Evaluation at a finite place is a continuous homomorphism. -/
def finiteComponentContinuous (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup K →ₜ* (v.adicCompletion K)ˣ where
  __ := finiteComponent v
  continuous_toFun :=
    (RestrictedProduct.continuous_eval v).comp continuous_finiteCoordinates

@[simp]
theorem infiniteComponentContinuous_apply
    (a : IdeleGroup K) (v : InfinitePlace K) :
    infiniteComponentContinuous v a =
      ContinuousMulEquiv.piUnits (infinitePart a) v :=
  rfl

@[simp]
theorem finiteComponentContinuous_apply
    (a : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    finiteComponentContinuous v a = finiteCoordinates a v :=
  rfl

end IdeleGroup
