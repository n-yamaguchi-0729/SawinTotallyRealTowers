/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.Data.Finset.Image
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict


/-!
# Simultaneous finite-level representatives of inertia invariants

Every finite family of elements in the actual integral closure fixed by its
prime inertia comes from one finite Galois intermediate field. The returned
elements are integral over the original base and fixed by the inertia of the
literal contracted prime. This supplies simultaneous coefficients, including
numerators and denominators, for the localized-invariant colimit construction.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v w

attribute [local instance] normalizationInertiaImageAction normalizationInertiaImageTower

/-- A finite set of inertia-fixed integral elements is represented at one
actual finite Galois level, with literal inclusion equality and the genuine
finite-level inertia action. Fixedness is descended using the proved equality
of inertia images; no colimit or fixed-ring comparison is assumed. -/
theorem integralClosure_inertia_fixed_finite_representatives
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (s : Finset (integralClosure A L))
    (hs : ∀ b ∈ s, ∀ σ ∈ Q.inertia Gal(L/K), σ • b = b) :
    ∃ E : FiniteGaloisIntermediateField K L,
      ∀ b ∈ s, ∃ bE : integralClosure A E,
        (IsScalarTower.toAlgHom A E L).mapIntegralClosure bE = b ∧
        ∀ τ ∈ (Q.comap (IsScalarTower.toAlgHom A E L).mapIntegralClosure).inertia Gal(E/K),
          τ • bE = bE := by
  classical
  let t : Finset L := s.image (fun b : integralClosure A L => (b : L))
  let E : FiniteGaloisIntermediateField K L :=
    FiniteGaloisIntermediateField.adjoin K (t : Set L)
  refine ⟨E, ?_⟩
  intro b hb
  have hbE : (b : L) ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K (t : Set L)
      (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  let e : E := ⟨(b : L), hbE⟩
  have he : IsIntegral A e :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom A E L)
      (algebraMap E L).injective).mp b.property
  let bE : integralClosure A E := ⟨e, he⟩
  refine ⟨bE, Subtype.ext rfl, ?_⟩
  intro τ hτ
  have himage := integralClosure_inertia_map_eq_finiteGalois_contraction A K L E Q
  have hτimage : τ ∈ (Q.inertia Gal(L/K)).map (AlgEquiv.restrictNormalHom E) := by
    rw [himage]
    exact hτ
  obtain ⟨σ, hσ, rfl⟩ := hτimage
  have hfixed : σ (b : L) = (b : L) :=
    (algebraMap_galRestrict_apply A σ b).symm.trans
      (congrArg Subtype.val (hs b hb σ hσ))
  apply Subtype.ext
  apply (algebraMap E L).injective
  change algebraMap E L
      (algebraMap (integralClosure A E) E
        (galRestrict A K E (integralClosure A E) (AlgEquiv.restrictNormalHom E σ) bE)) =
    algebraMap E L (algebraMap (integralClosure A E) E bE)
  rw [algebraMap_galRestrict_apply A]
  exact (AlgEquiv.restrictNormal_commutes σ E
    (algebraMap (integralClosure A E) E bE)).trans hfixed

end EtaleFundamentalGroups.Inertia
