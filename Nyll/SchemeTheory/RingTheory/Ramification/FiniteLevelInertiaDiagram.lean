/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaRepresentatives
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.AlgCat.FilteredColimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Data.Finset.Insert
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic


/-!
# The actual finite-level diagram of inertia invariants

The stage at a finite Galois intermediate field is the preimage of the upper
inertia-fixed subalgebra under the literal normalization inclusion. Transition
maps are restrictions of the existing intermediate-field inclusions. The
coefficient algebra is never replaced by an independently chosen action.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.Inertia

universe u v w

attribute [local instance] normalizationInertiaImageAction normalizationInertiaImageTower

variable (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

local instance normalizationInertiaCoefficientCommClass :
    SMulCommClass Gal(L/K) A (integralClosure A L) :=
  SMul.comp.smulCommClass (α := integralClosure A L)
    (M := (integralClosure A L) ≃ₐ[A] (integralClosure A L)) (β := A)
    (galRestrict A K L (integralClosure A L))

variable (Q : Ideal (integralClosure A L)) [Q.IsPrime]

local notation "C" => integralClosure A L
local notation "CI" => FixedPoints.subalgebra A C (Q.inertia Gal(L/K))

/-- The actual finite normalization elements whose images are fixed by the
inertia of the chosen upper prime. -/
def finiteLevelInertiaSubalgebra (E : FiniteGaloisIntermediateField K L) :
    Subalgebra A (integralClosure A E) :=
  (FixedPoints.subalgebra A (integralClosure A L) (Q.inertia Gal(L/K))).comap
    (IsScalarTower.toAlgHom A E L).mapIntegralClosure

/-- The literal inclusion of a finite invariant stage into the upper
inertia-fixed algebra. -/
def finiteLevelInertiaSubalgebraInclusion (E : FiniteGaloisIntermediateField K L) :
    finiteLevelInertiaSubalgebra A K L Q E →ₐ[A] CI :=
  (((IsScalarTower.toAlgHom A E L).mapIntegralClosure).comp
    (finiteLevelInertiaSubalgebra A K L Q E).val).codRestrict CI (fun b => b.property)

/-- The preimage stage is exactly the finite-level inertia-invariant
subalgebra. Both directions use the literal normalization inclusion, and the
reverse lifting of inertia is supplied by the actual profinite image theorem. -/
theorem finiteLevelInertiaSubalgebra_eq_fixedPoints
    (E : FiniteGaloisIntermediateField K L) :
    finiteLevelInertiaSubalgebra A K L Q E =
      FixedPoints.subalgebra A (integralClosure A E)
        ((Q.comap (IsScalarTower.toAlgHom A E L).mapIntegralClosure).inertia Gal(E/K)) := by
  let j : integralClosure A E →ₐ[A] C :=
    (IsScalarTower.toAlgHom A E L).mapIntegralClosure
  have hinj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    exact (algebraMap E L).injective (congrArg (fun z : C => (z : L)) h)
  have hcompat : ∀ (σ : Gal(L/K)) (b : integralClosure A E),
      j (AlgEquiv.restrictNormalHom E σ • b) = σ • j b := by
    intro σ b
    apply Subtype.ext
    change algebraMap E L
        (algebraMap (integralClosure A E) E
          (galRestrict A K E (integralClosure A E) (AlgEquiv.restrictNormalHom E σ) b)) =
      algebraMap C L (galRestrict A K L C σ (j b))
    rw [algebraMap_galRestrict_apply A, algebraMap_galRestrict_apply A]
    exact AlgEquiv.restrictNormal_commutes σ E (algebraMap (integralClosure A E) E b)
  have himage := integralClosure_inertia_map_eq_finiteGalois_contraction A K L E Q
  ext b
  change (∀ σ : Q.inertia Gal(L/K), σ • j b = j b) ↔
    ∀ τ : (Q.comap j).inertia Gal(E/K), τ • b = b
  constructor
  · intro hb τ
    have hτ : (τ : Gal(E/K)) ∈ (Q.inertia Gal(L/K)).map (AlgEquiv.restrictNormalHom E) := by
      rw [himage]
      exact τ.property
    obtain ⟨σ, hσ, heq⟩ := hτ
    have hfixed : (AlgEquiv.restrictNormalHom E σ) • b = b := by
      apply hinj
      rw [hcompat]
      exact hb ⟨σ, hσ⟩
    change (τ : Gal(E/K)) • b = b
    rw [← heq]
    exact hfixed
  · intro hb σ
    have hσ : AlgEquiv.restrictNormalHom E (σ : Gal(L/K)) ∈ (Q.comap j).inertia Gal(E/K) := by
      rw [← himage]
      exact ⟨(σ : Gal(L/K)), σ.property, rfl⟩
    have hfixed : AlgEquiv.restrictNormalHom E (σ : Gal(L/K)) • b = b :=
      hb ⟨AlgEquiv.restrictNormalHom E (σ : Gal(L/K)), hσ⟩
    change (σ : Gal(L/K)) • j b = j b
    rw [← hcompat, hfixed]

/-- The actual map between finite invariant stages induced by an inclusion
of finite Galois intermediate fields. -/
def finiteLevelInertiaSubalgebraMap {E F : FiniteGaloisIntermediateField K L}
    (h : E ≤ F) :
    finiteLevelInertiaSubalgebra A K L Q E →ₐ[A]
      finiteLevelInertiaSubalgebra A K L Q F :=
  ((((IntermediateField.inclusion h).restrictScalars A).mapIntegralClosure).comp
    (finiteLevelInertiaSubalgebra A K L Q E).val).codRestrict
      (finiteLevelInertiaSubalgebra A K L Q F) (fun b => by
        change (IsScalarTower.toAlgHom A F L).mapIntegralClosure
            (((IntermediateField.inclusion h).restrictScalars A).mapIntegralClosure
              (b : integralClosure A E)) ∈ CI
        have heq : (IsScalarTower.toAlgHom A F L).mapIntegralClosure
            (((IntermediateField.inclusion h).restrictScalars A).mapIntegralClosure
              (b : integralClosure A E)) =
            (IsScalarTower.toAlgHom A E L).mapIntegralClosure (b : integralClosure A E) :=
          Subtype.ext rfl
        rw [heq]
        exact b.property)

/-- The actual filtered diagram, retaining the original base algebra. -/
def finiteLevelInertiaDiagram : FiniteGaloisIntermediateField K L ⥤ AlgCat.{w} A where
  obj E := AlgCat.of A (finiteLevelInertiaSubalgebra A K L Q E)
  map f := AlgCat.ofHom (finiteLevelInertiaSubalgebraMap A K L Q f.le)
  map_id E := by
    ext b
    rfl
  map_comp f g := by
    ext b
    rfl

/-- The literal normalization inclusions form the invariant cocone. -/
def finiteLevelInertiaCocone : Cocone (finiteLevelInertiaDiagram A K L Q) where
  pt := AlgCat.of A CI
  ι.app E := AlgCat.ofHom (finiteLevelInertiaSubalgebraInclusion A K L Q E)
  ι.naturality E F f := by
    ext b
    rfl

/-- The upper inertia-fixed algebra is the filtered colimit of its actual
finite invariant stages. Finite representatives supply the cocone surjectivity;
literal field inclusions detect equality already at each stage. -/
def finiteLevelInertiaCoconeIsColimit :
    IsColimit (finiteLevelInertiaCocone A K L Q) := by
  apply isColimitOfReflects (forget₂ (AlgCat.{w} A) RingCat.{w})
  letI : ReflectsColimit
      (finiteLevelInertiaDiagram A K L Q ⋙ forget₂ (AlgCat.{w} A) RingCat.{w})
      (forget RingCat.{w}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget RingCat.{w})
  apply Types.FilteredColimit.isColimitOf'
  · change ∀ b : CI, ∃ (E : FiniteGaloisIntermediateField K L)
        (bE : finiteLevelInertiaSubalgebra A K L Q E),
        b = finiteLevelInertiaSubalgebraInclusion A K L Q E bE
    intro b
    obtain ⟨E, hE⟩ := integralClosure_inertia_fixed_finite_representatives A K L Q
      {(b : C)} (fun c hc σ hσ => by
        have hc' : c = (b : C) := Finset.mem_singleton.mp hc
        rw [hc']
        exact b.property ⟨σ, hσ⟩)
    obtain ⟨bE, hbE, _⟩ := hE (b : C) (Finset.mem_singleton_self _)
    have hbEI : bE ∈ finiteLevelInertiaSubalgebra A K L Q E := by
      change (IsScalarTower.toAlgHom A E L).mapIntegralClosure bE ∈ CI
      rw [hbE]
      exact b.property
    refine ⟨E, ⟨bE, hbEI⟩, ?_⟩
    exact Subtype.ext hbE.symm
  · intro E x y hxy
    refine ⟨E, 𝟙 E, ?_⟩
    change x = y
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun b : CI => ((b : C) : L)) hxy

end EtaleFundamentalGroups.Inertia
