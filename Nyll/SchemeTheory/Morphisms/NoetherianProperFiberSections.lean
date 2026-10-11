/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper
import Nyll.SchemeTheory.Affine.HomeomorphismIdempotentSections
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Lifting idempotent sections of proper closed fibres

Over a Noetherian ring, every idempotent section on a closed base change of
a proper scheme is the restriction of an actual global section. The lift
need not be idempotent. Its existence follows from the already constructed
proper formal-functions approximation: the idempotent lifts through the
homeomorphism from the closed base change to an infinitesimal thickening,
and a sufficiently thick such lift comes from a global section.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

private theorem range_specMap_quotient
    {A : Type u} [CommRing A] (I : Ideal A) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
      PrimeSpectrum.zeroLocus (I : Set A) := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
  rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

private theorem exists_appTop_eq_on_pow_one
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (I : Ideal A) :
    ∀ (e : Γ(pullback q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1)))), ⊤)),
      IsIdempotentElem e → ∃ a : Γ(P, ⊤),
        (pullback.fst q
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1))))).appTop a = e := by
  intro e he
  obtain ⟨c, hc⟩ :=
    exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper I q 1
  have hpow : I ^ (1 + c) ≤ I ^ 1 :=
    Ideal.pow_le_pow_right (Nat.le_add_right 1 c)
  let ι : Spec (CommRingCat.of (A ⧸ I ^ 1)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1)))
  let ιc : Spec (CommRingCat.of (A ⧸ I ^ (1 + c))) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (1 + c))))
  have : IsClosedImmersion ι :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1))) Ideal.Quotient.mk_surjective
  have : IsClosedImmersion ιc :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (1 + c)))) Ideal.Quotient.mk_surjective
  let τ : pullback q ι ⟶ pullback q ιc :=
    pullback.map q ι q ιc (𝟙 P)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hpow))) (𝟙 _)
      (by rw [Category.id_comp, Category.comp_id])
      (by
        rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          Ideal.Quotient.factor_comp_mk])
  have hτ : τ ≫ pullback.fst q ιc = pullback.fst q ι := by
    simp only [τ, pullback.lift_fst, Category.comp_id]
  have hclosedComp : IsClosedImmersion (τ ≫ pullback.fst q ιc) := by
    rw [hτ]
    infer_instance
  have : IsClosedImmersion τ :=
    IsClosedImmersion.of_comp_isClosedImmersion τ (pullback.fst q ιc)
  have hrange : Set.range (pullback.fst q ι) = Set.range (pullback.fst q ιc) := by
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst]
    dsimp only [ι, ιc]
    rw [range_specMap_quotient, range_specMap_quotient, pow_one,
      PrimeSpectrum.zeroLocus_pow I (by omega)]
  have hsurj : Function.Surjective τ := by
    intro z
    have hz : pullback.fst q ιc z ∈ Set.range (pullback.fst q ι) := by
      rw [hrange]
      exact ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hz
    refine ⟨w, (pullback.fst q ιc).isEmbedding.injective ?_⟩
    change (τ ≫ pullback.fst q ιc) w = pullback.fst q ιc z
    rw [hτ]
    exact hw
  have hhomeo : IsHomeomorph τ :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨τ.isEmbedding, hsurj⟩
  obtain ⟨t, ht⟩ := τ.exists_appTop_eq_of_isHomeomorph_of_isIdempotentElem hhomeo e he
  have hc' : ∀ t : Γ(pullback q ιc, ⊤),
      ∃ a : Γ(P, ⊤), τ.appTop t = (pullback.fst q ι).appTop a := by
    exact hc
  obtain ⟨a, ha⟩ := hc' t
  exact ⟨a, ha.symm.trans ht⟩

/-- An idempotent section on any closed base change of a proper scheme over
a Noetherian ring is the restriction of an actual global section. -/
theorem exists_appTop_eq_of_isProper_of_isNoetherianRing_of_isIdempotentElem
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (I : Ideal A)
    (e : Γ(pullback q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))), ⊤))
    (he : IsIdempotentElem e) :
    ∃ a : Γ(P, ⊤),
      (pullback.fst q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).appTop a = e := by
  let Lift : Ideal A → Prop := fun J =>
    ∀ (t : Γ(pullback q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))), ⊤)),
      IsIdempotentElem t → ∃ a : Γ(P, ⊤),
        (pullback.fst q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).appTop a = t
  have h : Lift (I ^ 1) := exists_appTop_eq_on_pow_one q I
  have h' : Lift I := (congrArg Lift (pow_one I)).mp h
  exact h' e he

/-- The same lift for an actual surjective base-ring map, using the
constructed quotient-by-kernel isomorphism and its pullback. In particular,
this applies directly to the residue map of a Noetherian local ring. -/
theorem exists_appTop_eq_of_isProper_of_surjective_of_isIdempotentElem
    {A K : Type u} [CommRing A] [IsNoetherianRing A] [CommRing K]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (φ : A →+* K) (hφ : Function.Surjective φ)
    (e : Γ(pullback q (Spec.map (CommRingCat.ofHom φ)), ⊤))
    (he : IsIdempotentElem e) :
    ∃ a : Γ(P, ⊤),
      (pullback.fst q (Spec.map (CommRingCat.ofHom φ))).appTop a = e := by
  let E : CommRingCat.of (A ⧸ RingHom.ker φ) ≅ CommRingCat.of K :=
    (φ.quotientKerEquivOfSurjective hφ).toCommRingCatIso
  let ι : Spec (CommRingCat.of (A ⧸ RingHom.ker φ)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ)))
  let κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom φ)
  let σ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (A ⧸ RingHom.ker φ)) :=
    Spec.map E.hom
  have : IsIso σ := by
    dsimp only [σ]
    infer_instance
  have hcomp : CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ)) ≫ E.hom =
      CommRingCat.ofHom φ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hφ a
  have hσ : σ ≫ ι = κ := by
    dsimp only [σ, ι, κ]
    rw [← Spec.map_comp, hcomp]
  let η : pullback q κ ⟶ pullback q ι :=
    pullback.map q κ q ι (𝟙 P) σ (𝟙 _)
      (by rw [Category.id_comp, Category.comp_id])
      (by rw [Category.comp_id]; exact hσ.symm)
  have : IsIso η := by
    dsimp only [η]
    infer_instance
  have hη : η ≫ pullback.fst q ι = pullback.fst q κ := by
    simp only [η, pullback.lift_fst, Category.comp_id]
  obtain ⟨a, ha⟩ :=
    exists_appTop_eq_of_isProper_of_isNoetherianRing_of_isIdempotentElem
      q (RingHom.ker φ) ((inv η).appTop e) (he.map (inv η).appTop.hom)
  refine ⟨a, ?_⟩
  calc
    (pullback.fst q κ).appTop a = η.appTop ((pullback.fst q ι).appTop a) := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hη]
    _ = η.appTop ((inv η).appTop e) := congrArg η.appTop ha
    _ = e := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        IsIso.hom_inv_id, Scheme.Hom.id_appTop, CommRingCat.id_apply]

end AlgebraicGeometry
