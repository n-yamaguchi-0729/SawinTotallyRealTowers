/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Local components of the standard idele group

All projections are units of the corresponding adelic ring projections.
The finite-place API also applies to an arbitrary Dedekind domain and its
fraction field; no second idele carrier is introduced.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField RestrictedProduct

noncomputable section

universe u v

variable {R : Type u} {K : Type v} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

namespace IsDedekindDomain.FiniteAdeleRing

/-- Evaluation of a finite adele unit in the local unit group. -/
def unitComponent (v : HeightOneSpectrum R) :
    (FiniteAdeleRing R K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (RestrictedProduct.evalRingHom
    (fun w : HeightOneSpectrum R => w.adicCompletion K) v).toMonoidHom

/-- The component of a finite adele unit has the underlying adele value. -/
theorem coe_unitComponent (a : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    (unitComponent v a : v.adicCompletion K) = (a : FiniteAdeleRing R K) v := rfl

/-- The standard units equivalence with restricted local units, over any Dedekind domain. -/
def unitComponentsEquiv : (FiniteAdeleRing R K)ˣ ≃*
    (Πʳ v : HeightOneSpectrum R,
      [(v.adicCompletion K)ˣ, (v.adicCompletionIntegers K).units]) :=
  RestrictedProduct.unitsEquiv
    (S := fun v : HeightOneSpectrum R => ValuationSubring (v.adicCompletion K))
    (B := fun v : HeightOneSpectrum R => v.adicCompletionIntegers K)
    (𝓕 := Filter.cofinite) (fun v : HeightOneSpectrum R => v.adicCompletion K)

/-- The units equivalence evaluates by the same local projection. -/
theorem unitComponentsEquiv_apply (a : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    unitComponentsEquiv a v = unitComponent v a := rfl

/-- Both a finite adele unit and its inverse are integral at almost every place. -/
theorem eventually_unitComponent_mem (a : (FiniteAdeleRing R K)ˣ) :
    ∀ᶠ v in Filter.cofinite,
      unitComponent v a ∈ (v.adicCompletionIntegers K).units := by
  filter_upwards [a.val.2, a.inv.2] with v hv hinv
  exact ⟨hv, hinv⟩

/-- Finite adele units are determined by their local unit components. -/
@[ext]
theorem units_ext {a b : (FiniteAdeleRing R K)ˣ}
    (h : ∀ v, unitComponent v a = unitComponent v b) : a = b := by
  apply Units.ext
  apply DFunLike.coe_injective
  funext v
  exact congrArg (fun x : (v.adicCompletion K)ˣ => (x : v.adicCompletion K)) (h v)

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.InfiniteAdeleRing

/-- Evaluation of an infinite adele unit in an archimedean completion. -/
def unitComponent (v : InfinitePlace K) : (InfiniteAdeleRing K)ˣ →* v.Completionˣ :=
  Units.map (Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) v).toMonoidHom

end NumberField.InfiniteAdeleRing

namespace NumberField.IdeleGroup

/-- The archimedean part of a standard idele. -/
def infinitePart : IdeleGroup R K →* (InfiniteAdeleRing K)ˣ :=
  Units.map (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing R K)).toMonoidHom

/-- The finite adele unit underlying a standard idele. -/
def finitePart : IdeleGroup R K →* (FiniteAdeleRing R K)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing R K)).toMonoidHom

/-- Evaluation of a standard idele at an infinite place. -/
def infiniteComponent (v : InfinitePlace K) : IdeleGroup R K →* v.Completionˣ :=
  (InfiniteAdeleRing.unitComponent v).comp infinitePart

/-- Evaluation of a standard idele at a finite place. -/
def finiteComponent (v : HeightOneSpectrum R) :
    IdeleGroup R K →* (v.adicCompletion K)ˣ :=
  (FiniteAdeleRing.unitComponent v).comp finitePart

/-- The infinite unit component evaluates the underlying adele. -/
theorem coe_infiniteComponent (a : IdeleGroup R K) (v : InfinitePlace K) :
    (infiniteComponent v a : v.Completion) = (a : AdeleRing R K).1 v := rfl

/-- The finite unit component evaluates the underlying adele. -/
theorem coe_finiteComponent (a : IdeleGroup R K) (v : HeightOneSpectrum R) :
    (finiteComponent v a : v.adicCompletion K) = (a : AdeleRing R K).2 v := rfl

/-- A standard idele is a local integral unit at almost every finite place. -/
theorem eventually_finiteComponent_mem (a : IdeleGroup R K) :
    ∀ᶠ v in Filter.cofinite,
      finiteComponent v a ∈ (v.adicCompletionIntegers K).units :=
  FiniteAdeleRing.eventually_unitComponent_mem (finitePart a)

/-- Local components jointly determine a standard idele. -/
@[ext]
theorem ext {a b : IdeleGroup R K}
    (hi : ∀ v, infiniteComponent v a = infiniteComponent v b)
    (hf : ∀ v, finiteComponent v a = finiteComponent v b) : a = b := by
  apply Units.ext
  apply Prod.ext
  · funext v
    exact congrArg (fun x : v.Completionˣ => (x : v.Completion)) (hi v)
  · apply DFunLike.coe_injective
    funext v
    exact congrArg (fun x : (v.adicCompletion K)ˣ => (x : v.adicCompletion K)) (hf v)

/-- Infinite components of a principal idele are the completion embeddings. -/
theorem infiniteComponent_unitEmbedding (x : Kˣ) (v : InfinitePlace K) :
    infiniteComponent v (unitEmbedding R K x) =
      Units.map (algebraMap K v.Completion) x := by
  apply Units.ext
  rfl

/-- Finite components of a principal idele are the completion embeddings. -/
theorem finiteComponent_unitEmbedding (x : Kˣ) (v : HeightOneSpectrum R) :
    finiteComponent v (unitEmbedding R K x) =
      Units.map (algebraMap K (v.adicCompletion K)) x := by
  apply Units.ext
  rfl

/-- The selected infinite component of the standard one-place map is its input. -/
theorem infiniteComponent_ofCompletion_same
    (v : InfinitePlace K) (x : v.Completionˣ) :
    infiniteComponent v (ofCompletion R K v x) = x := by
  classical
  apply Units.ext
  change Pi.mulSingle v (x : v.Completion) v = (x : v.Completion)
  exact Pi.mulSingle_eq_same (M := fun w : InfinitePlace K => w.Completion) v _

/-- All other infinite components of the standard one-place map are trivial. -/
theorem infiniteComponent_ofCompletion_of_ne
    (v w : InfinitePlace K) (x : v.Completionˣ) (h : w ≠ v) :
    infiniteComponent w (ofCompletion R K v x) = 1 := by
  classical
  apply Units.ext
  change Pi.mulSingle v (x : v.Completion) w = 1
  exact Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace K => w.Completion) h _

/-- An infinite one-place idele has trivial finite components. -/
theorem finiteComponent_ofCompletion
    (v : InfinitePlace K) (x : v.Completionˣ) (w : HeightOneSpectrum R) :
    finiteComponent w (ofCompletion R K v x) = 1 := by
  apply Units.ext
  rfl

/-- The standard infinite one-place map is continuous in the graph topology. -/
theorem continuous_ofCompletion (v : InfinitePlace K) :
    Continuous (ofCompletion R K v) := by
  classical
  have h : Continuous (AdeleRing.ofCompletion R K v) := by
    change Continuous (fun x : v.Completion => (Pi.mulSingle v x, (1 : FiniteAdeleRing R K)))
    exact (continuous_mulSingle (A := fun w : InfinitePlace K => w.Completion) v).prodMk
      continuous_const
  exact h.units_map _

/-- A finite one-place idele has trivial infinite components. -/
theorem infiniteComponent_ofAdicCompletion
    (v : HeightOneSpectrum R) (x : (v.adicCompletion K)ˣ) (w : InfinitePlace K) :
    infiniteComponent w (ofAdicCompletion R K v x) = 1 := by
  apply Units.ext
  rfl

/-- The selected finite component of the standard one-place map is its input. -/
theorem finiteComponent_ofAdicCompletion_same
    (v : HeightOneSpectrum R) (x : (v.adicCompletion K)ˣ) :
    finiteComponent v (ofAdicCompletion R K v x) = x := by
  classical
  apply Units.ext
  change (RestrictedProduct.mulSingle
    (fun w : HeightOneSpectrum R => w.adicCompletionIntegers K) v
      (x : v.adicCompletion K)) v = (x : v.adicCompletion K)
  rw [RestrictedProduct.mulSingle_eq_same]

/-- All other finite components of the standard one-place map are trivial. -/
theorem finiteComponent_ofAdicCompletion_of_ne
    (v w : HeightOneSpectrum R) (x : (v.adicCompletion K)ˣ) (h : w ≠ v) :
    finiteComponent w (ofAdicCompletion R K v x) = 1 := by
  classical
  apply Units.ext
  change (RestrictedProduct.mulSingle
    (fun w : HeightOneSpectrum R => w.adicCompletionIntegers K) v
      (x : v.adicCompletion K)) w = 1
  exact RestrictedProduct.mulSingle_eq_of_ne _ _ h

end NumberField.IdeleGroup
