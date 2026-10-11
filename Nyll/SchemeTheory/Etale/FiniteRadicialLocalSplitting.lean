/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.ChosenResidueExtension
public import Nyll.SchemeTheory.Etale.PurelyInseparableFiniteFactor
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Actual local sections of affine étale schemes over a finite radicial base

First choose an étale extension of the bottom ring that removes the separable
part of the selected residue extension. The quasi-finite structure theorem
then constructs a finite open factor with singleton fiber. Its actual map to
the base change of the radicial scheme is finite and étale. The isomorphism
neighborhood gives a section, and restricting the bottom étale neighborhood
gives the asserted lift of the original cover.

No flatness or finite-presentation hypothesis is imposed on the finite
radicial map. A chosen point of the cover suffices; surjectivity of the
radicial map is not needed for this pointwise local statement.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

private theorem etale_specMap_includeRight
    (R T A : Type u) [CommRing R] [CommRing T] [CommRing A]
    [Algebra R T] [Algebra R A] [Algebra.Etale R T] :
    Etale (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom)) := by
  let : Etale (Spec.map (CommRingCat.ofHom (algebraMap R T))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have h : Etale ((pullbackSpecIso R T A).inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R T)))
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))) := inferInstance
  rw [pullbackSpecIso_inv_snd] at h
  exact h

/-- Through every point of an affine étale scheme upstairs, a finite radicial
morphism admits an actual étale neighborhood downstairs on whose base change
the cover has a section. The lift, its equation over the original base, and
a point mapping to the prescribed point of the cover are all constructed. -/
theorem Etale.exists_local_section_of_finite_radicial
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    [Module.Finite R S] [Algebra.Etale S A]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (q : PrimeSpectrum A) :
    ∃ (T : Scheme.{u}) (e : T ⟶ Spec (CommRingCat.of R)) (_ : Etale e)
      (t : T)
      (s : pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) e ⟶
        Spec (CommRingCat.of A)),
      e t = PrimeSpectrum.comap (algebraMap R S)
        (PrimeSpectrum.comap (algebraMap S A) q) ∧
      s ≫ Spec.map (CommRingCat.ofHom (algebraMap S A)) =
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S))) e ∧
      ∃ w : ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) e : Scheme.{u}),
        s w = q ∧
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S))) e w = t := by
  let qA : Spec (CommRingCat.of A) := q
  let f : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  let p : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S A))
  let a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  have hpa : p ≫ f = a := by
    dsimp only [p, f, a]
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((algebraMap S A).comp (algebraMap R S))) = _
    rw [← IsScalarTower.algebraMap_eq R S A]
  let : Etale p := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  let : IsFinite f := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  let : Algebra.FiniteType R A := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R S) (inferInstance : Algebra.FiniteType S A)
  let : Algebra.QuasiFinite R A := Algebra.QuasiFinite.trans R S A
  let p₀ : Ideal R := q.asIdeal.comap (algebraMap R A)
  let : q.asIdeal.IsPrime := q.isPrime
  let : p₀.IsPrime := Ideal.comap_isPrime _ _
  let : q.asIdeal.LiesOver p₀ := ⟨rfl⟩
  obtain ⟨R₁, hR₁, hRR₁, hEtale₁, P₁, hP₁, hP₁p, Q₁, hQ₁, hQ₁P,
      hqQ₁, _, _, hκ₁⟩ :=
    Algebra.Etale.exists_chosen_residue_extension p₀ q.asIdeal
  let : CommRing R₁ := hR₁
  let : Algebra R R₁ := hRR₁
  let : Algebra.Etale R R₁ := hEtale₁
  let : P₁.IsPrime := hP₁
  let : P₁.LiesOver p₀ := hP₁p
  let : Q₁.IsPrime := hQ₁
  let : Q₁.LiesOver P₁ := hQ₁P
  let A₁ := R₁ ⊗[R] A
  let e₁ : Spec (CommRingCat.of R₁) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R R₁))
  let u₁ : Spec (CommRingCat.of A₁) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] R₁ ⊗[R] A).toRingHom)
  let v₁ : Spec (CommRingCat.of A₁) ⟶ Spec (CommRingCat.of R₁) :=
    Spec.map (CommRingCat.ofHom (algebraMap R₁ A₁))
  let : Etale e₁ := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr hEtale₁)
  let : Etale u₁ := etale_specMap_includeRight R R₁ A
  have hsquare₁ : u₁ ≫ a = v₁ ≫ e₁ := by
    dsimp only [u₁, a, v₁, e₁, A₁]
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := R) (A := R₁) (B := A)).symm
  obtain ⟨R₂, hR₂, hR₁R₂, hEtale₂, P₂, hP₂, hP₂P, b, hb, hfinite,
      hfiniteSpec, hopen, z, hzP₂, hzQ₁, huniq, hκz⟩ :=
    exists_purelyInseparable_etale_finite_factor P₁ Q₁ hκ₁
  let : CommRing R₂ := hR₂
  let : Algebra R₁ R₂ := hR₁R₂
  let : Algebra.Etale R₁ R₂ := hEtale₂
  let : P₂.IsPrime := hP₂
  let : P₂.LiesOver P₁ := hP₂P
  let C := R₂ ⊗[R₁] A₁
  let B := Localization.Away b
  let e₂ : Spec (CommRingCat.of R₂) ⟶ Spec (CommRingCat.of R₁) :=
    Spec.map (CommRingCat.ofHom (algebraMap R₁ R₂))
  let u₂ : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of A₁) :=
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A₁ →ₐ[R₁] R₂ ⊗[R₁] A₁).toRingHom)
  let v₂ : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of R₂) :=
    Spec.map (CommRingCat.ofHom (algebraMap R₂ C))
  let i : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of C) :=
    Spec.map (CommRingCat.ofHom (algebraMap C B))
  let t₂ : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R₂) :=
    Spec.map (CommRingCat.ofHom (algebraMap R₂ B))
  let : Etale e₂ := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr hEtale₂)
  let : Etale u₂ := etale_specMap_includeRight R₁ R₂ A₁
  let : IsOpenImmersion i := hopen
  have hsquare₂ : u₂ ≫ v₁ = v₂ ≫ e₂ := by
    dsimp only [u₂, v₁, v₂, e₂, C]
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := R₁) (A := R₂) (B := A₁)).symm
  have hit : i ≫ v₂ = t₂ := by
    dsimp only [i, v₂, t₂]
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((algebraMap C B).comp (algebraMap R₂ C))) = _
    rw [← IsScalarTower.algebraMap_eq R₂ C B]
  let E : Spec (CommRingCat.of R₂) ⟶ Spec (CommRingCat.of R) := e₂ ≫ e₁
  let g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) := i ≫ u₂ ≫ u₁
  have hgq : g z = qA := by
    change u₁ ((i ≫ u₂) z) = qA
    rw [hzQ₁]
    exact PrimeSpectrum.ext hqQ₁.symm
  have hgt : (g ≫ p) ≫ f = t₂ ≫ E := by
    calc
      (g ≫ p) ≫ f = i ≫ u₂ ≫ u₁ ≫ (p ≫ f) := by
        simp only [g, Category.assoc]
      _ = i ≫ u₂ ≫ (v₁ ≫ e₁) := by rw [hpa, hsquare₁]
      _ = i ≫ (u₂ ≫ v₁) ≫ e₁ := by simp only [Category.assoc]
      _ = i ≫ (v₂ ≫ e₂) ≫ e₁ := by rw [hsquare₂]
      _ = (i ≫ v₂) ≫ (e₂ ≫ e₁) := by simp only [Category.assoc]
      _ = t₂ ≫ E := by rw [hit]
  let f' : pullback f E ⟶ Spec (CommRingCat.of R₂) := pullback.snd f E
  let : UniversallyInjective f' :=
    UniversallyInjective.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f E) (inferInstance : UniversallyInjective f)
  let l : Spec (CommRingCat.of B) ⟶ pullback f E := pullback.lift (g ≫ p) t₂ hgt
  have hlX : l ≫ pullback.fst f E = g ≫ p := pullback.lift_fst _ _ _
  have hlY : l ≫ f' = t₂ := pullback.lift_snd _ _ _
  let : IsFinite (l ≫ f') := hlY.symm ▸ hfiniteSpec
  let : IsFinite l := IsFinite.of_comp l f'
  let : Etale (l ≫ pullback.fst f E) :=
    hlX.symm ▸ inferInstanceAs (Etale (g ≫ p))
  let : Etale l := Etale.of_comp l (pullback.fst f E)
  have hlu : ∀ z' : Spec (CommRingCat.of B), l z' = l z → z' = z := by
    intro z' hz'
    apply huniq z'
    have ht : t₂ z' = t₂ z :=
      (congrArg (fun k : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R₂) ↦ k z')
        hlY).symm.trans ((congrArg f' hz').trans
          (congrArg (fun k : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R₂) ↦ k z) hlY))
    exact ht.trans hzP₂
  have hκcomp : ((l ≫ f').residueFieldMap z).hom.IsPurelyInseparable := by
    rw [hlY]
    exact hκz
  have hκl : (l.residueFieldMap z).hom.IsPurelyInseparable := by
    let : Algebra ((Spec (CommRingCat.of R₂)).residueField (f' (l z)))
        ((pullback f E).residueField (l z)) := (f'.residueFieldMap (l z)).hom.toAlgebra
    let : Algebra ((pullback f E).residueField (l z))
        ((Spec (CommRingCat.of B)).residueField z) := (l.residueFieldMap z).hom.toAlgebra
    let : Algebra ((Spec (CommRingCat.of R₂)).residueField (f' (l z)))
        ((Spec (CommRingCat.of B)).residueField z) :=
      ((l ≫ f').residueFieldMap z).hom.toAlgebra
    let : IsScalarTower ((Spec (CommRingCat.of R₂)).residueField (f' (l z)))
        ((pullback f E).residueField (l z)) ((Spec (CommRingCat.of B)).residueField z) :=
      IsScalarTower.of_algebraMap_eq'
        (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp l f' z))
    let : IsPurelyInseparable ((Spec (CommRingCat.of R₂)).residueField (f' (l z)))
        ((Spec (CommRingCat.of B)).residueField z) := hκcomp
    exact IsPurelyInseparable.tower_top
      ((Spec (CommRingCat.of R₂)).residueField (f' (l z)))
      ((pullback f E).residueField (l z)) ((Spec (CommRingCat.of B)).residueField z)
  obtain ⟨V, hV, s₀, hs₀, hs₀z⟩ :=
    Etale.exists_section_over_finite_base_neighborhood l f' z hlu hκl
  let x : (f' ⁻¹ᵁ V).toScheme := ⟨l z, hV⟩
  let e : V.toScheme ⟶ Spec (CommRingCat.of R) := V.ι ≫ E
  have hpb : IsPullback ((f' ⁻¹ᵁ V).ι ≫ pullback.fst f E) (f' ∣_ V) f e :=
    ((isPullback_morphismRestrict f' V).paste_vert
      (IsPullback.of_hasPullback f E).flip).flip
  let J : (f' ⁻¹ᵁ V).toScheme ≅ pullback f e := hpb.isoPullback
  let s : pullback f e ⟶ Spec (CommRingCat.of A) := J.inv ≫ s₀ ≫ g
  refine ⟨V.toScheme, e, inferInstance, (f' ∣_ V) x, s, ?_, ?_, J.hom x, ?_, ?_⟩
  · change ((f' ∣_ V) ≫ e) x = f (p qA)
    rw [← hpb.w]
    change f (pullback.fst f E (l z)) = f (p qA)
    have hx : pullback.fst f E (l z) = p (g z) :=
      congrArg (fun k : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of S) ↦ k z) hlX
    exact congrArg f (hx.trans (congrArg p hgq))
  · change s ≫ p = pullback.fst f e
    calc
      s ≫ p = J.inv ≫ s₀ ≫ (g ≫ p) := by simp only [s, Category.assoc]
      _ = J.inv ≫ s₀ ≫ (l ≫ pullback.fst f E) := by rw [hlX]
      _ = J.inv ≫ ((f' ⁻¹ᵁ V).ι ≫ pullback.fst f E) := by
        rw [← Category.assoc s₀ l, hs₀]
      _ = pullback.fst f e := hpb.isoPullback_inv_fst
  · change (J.hom ≫ (J.inv ≫ s₀ ≫ g)) x = qA
    rw [Iso.hom_inv_id_assoc]
    change g (s₀ x) = qA
    rw [hs₀z, hgq]
  · change (J.hom ≫ pullback.snd f e) x = (f' ∣_ V) x
    rw [hpb.isoPullback_hom_snd]

end AlgebraicGeometry
