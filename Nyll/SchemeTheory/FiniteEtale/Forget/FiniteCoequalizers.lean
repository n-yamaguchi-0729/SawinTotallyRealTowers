/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright notice; its holder requires review.

The simultaneous-splitting argument is adapted from this pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/KerTensor.lean
-/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors of Nyll-local additions: Naganori Yamaguchi (assisted by OpenAI Codex).

This file is a Nyll extension, not an upstream pi1 module.
The initial AlgHom.AreSplit definition, its scalar-tower comparison and
AlgHom.exists_areSplit adapt Christian Merten's single-map AlgHom.IsSplit,
AlgHom.IsSplit.iff_of_isScalarTower and Algebra.exists_isSplit arguments in
Pi1/RingTheory/KerTensor.lean to a simultaneous pair of maps. The upstream
credit and the unresolved upstream copyright notice above apply to those
adapted arguments. The concrete coequalizer and descent implementation is
Nyll-local; it is not supplied by the cited pi1 file.
-/

import Nyll.SchemeTheory.Descent.FpqcLocalCoequalizer
import Nyll.SchemeTheory.FiniteEtale.Forget.FiniteCoproducts
import Nyll.SchemeTheory.Pi1.FiniteEtale.Algebra.Splitting
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import Mathlib.CategoryTheory.Limits.Types.Coequalizers

/-!
# Coequalizers of finite étale schemes

This file proves the coequalizer-preservation part of Stacks Project, Tag
`0BNA`, for the canonical forgetful functors from finite étale schemes.
-/

universe u v w u' v'

noncomputable section

open CategoryTheory Limits TensorProduct

namespace Algebra

variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R S] [Algebra R B]

/-- Two maps between finite étale algebras are split when, after identifying
both algebras with finite products of the base, they are induced by maps of
the finite indexing sets. -/
private def AlgHom.AreSplit (f g : A →ₐ[R] B) : Prop :=
  ∃ (n m : ℕ) (eA : A ≃ₐ[R] (Fin n → R)) (eB : B ≃ₐ[R] (Fin m → R))
    (sigma tau : Fin m → Fin n),
    eB.toAlgHom.comp f = (AlgHom.compRight R R sigma).comp eA.toAlgHom ∧
    eB.toAlgHom.comp g = (AlgHom.compRight R R tau).comp eA.toAlgHom

/-- Reindex a finite product by the universe lift of its finite index. -/
private def finULiftPiAlgEquiv (R : Type u) [CommRing R] (n : ℕ) :
    (Fin n → R) ≃ₐ[R] (ULift.{u, 0} (Fin n) → R) :=
  AlgEquiv.piCongrLeft' R (fun _ : Fin n ↦ R) (Equiv.ulift.{u, 0}).symm

private lemma liftFinSplitEq {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (n m : ℕ)
    (eA : A ≃ₐ[R] (Fin n → R)) (eB : B ≃ₐ[R] (Fin m → R))
    (sigma : Fin m → Fin n)
    (h : eB.toAlgHom.comp f =
      (AlgHom.compRight R R sigma).comp eA.toAlgHom) :
    let eA' := eA.trans (finULiftPiAlgEquiv R n)
    let eB' := eB.trans (finULiftPiAlgEquiv R m)
    let sigma' : ULift.{u, 0} (Fin m) → ULift.{u, 0} (Fin n) :=
      fun i ↦ ULift.up (sigma i.down)
    eB'.toAlgHom.comp f =
      (AlgHom.compRight R R sigma').comp eA'.toAlgHom := by
  dsimp only
  ext x i
  have hx := DFunLike.congr_fun h x
  exact congrFun hx i.down

variable (S) in
private lemma AlgHom.AreSplit.iff_of_isScalarTower
    (T : Type u) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (f g : A →ₐ[R] B) :
    (AlgHom.AreSplit
      (Algebra.TensorProduct.map (.id T T) f)
      (Algebra.TensorProduct.map (.id T T) g)) ↔
    (AlgHom.AreSplit
      (Algebra.TensorProduct.map (.id T T)
        (Algebra.TensorProduct.map (.id S S) f))
      (Algebra.TensorProduct.map (.id T T)
        (Algebra.TensorProduct.map (.id S S) g))) := by
  constructor
  · rintro ⟨n, m, eA, eB, sigma, tau, hf, hg⟩
    refine ⟨n, m,
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans eA,
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans eB,
      sigma, tau, ?_, ?_⟩
    · ext a i
      have h := DFunLike.congr_fun hf (1 ⊗ₜ a)
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, AlgHom.coe_comp,
        Function.comp_apply] at h
      simpa [AlgHom.compRight_apply'] using congrFun h i
    · ext a i
      have h := DFunLike.congr_fun hg (1 ⊗ₜ a)
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, AlgHom.coe_comp,
        Function.comp_apply] at h
      simpa [AlgHom.compRight_apply'] using congrFun h i
  · rintro ⟨n, m, eA, eB, sigma, tau, hf, hg⟩
    refine ⟨n, m,
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm.trans eA,
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm.trans eB,
      sigma, tau, ?_, ?_⟩
    · ext a i
      have h := DFunLike.congr_fun hf (1 ⊗ₜ (1 ⊗ₜ a))
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, AlgHom.coe_comp,
        Function.comp_apply] at h
      simpa [AlgHom.compRight_apply'] using congrFun h i
    · ext a i
      have h := DFunLike.congr_fun hg (1 ⊗ₜ (1 ⊗ₜ a))
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, AlgHom.coe_comp,
        Function.comp_apply] at h
      simpa [AlgHom.compRight_apply'] using congrFun h i

/-- A pair of maps between finite étale algebras becomes split over a flat,
open neighbourhood of any prescribed prime. -/
private lemma AlgHom.exists_areSplit [Module.Finite R A] [Algebra.Etale R A]
    [Module.Finite R B] [Algebra.Etale R B] (f g : A →ₐ[R] B)
    (p : PrimeSpectrum R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.Flat R S ∧
      IsOpenMap (PrimeSpectrum.comap (algebraMap R S)) ∧
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) ∧
      AlgHom.AreSplit
        (Algebra.TensorProduct.map (AlgHom.id S S) f)
        (Algebra.TensorProduct.map (AlgHom.id S S) g) := by
  classical
  wlog hA : IsFiniteSplit R A
  · obtain ⟨S, _, _, _, ho₁, ⟨p, rfl⟩, hS⟩ :=
      exists_isFiniteSplit p (A := A)
    obtain ⟨S', _, _, _, ho₂, ⟨q, rfl⟩, hS'⟩ := this
      (R := S) (A := S ⊗[R] A) (B := S ⊗[R] B)
      (Algebra.TensorProduct.map (.id S S) f)
      (Algebra.TensorProduct.map (.id S S) g) p hS
    let _ : Algebra R S' := Algebra.compHom S' (algebraMap R S)
    have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
    refine ⟨S', inferInstance, inferInstance, Module.Flat.trans R S S', ?_,
      ⟨q, rfl⟩, ?_⟩
    · rw [IsScalarTower.algebraMap_eq R S S', PrimeSpectrum.comap_comp]
      exact ho₁.comp ho₂
    · rwa [AlgHom.AreSplit.iff_of_isScalarTower S]
  wlog hB : IsFiniteSplit R B
  · obtain ⟨S, _, _, _, ho₁, ⟨p, rfl⟩, hS⟩ :=
      exists_isFiniteSplit p (A := B)
    obtain ⟨S', _, _, _, ho₂, ⟨q, rfl⟩, hS'⟩ := this
      (R := S) (A := S ⊗[R] A) (B := S ⊗[R] B)
      (Algebra.TensorProduct.map (.id S S) f)
      (Algebra.TensorProduct.map (.id S S) g) p inferInstance hS
    let _ : Algebra R S' := Algebra.compHom S' (algebraMap R S)
    have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
    refine ⟨S', inferInstance, inferInstance, Module.Flat.trans R S S', ?_,
      ⟨q, rfl⟩, ?_⟩
    · rw [IsScalarTower.algebraMap_eq R S S', PrimeSpectrum.comap_comp]
      exact ho₁.comp ho₂
    · rwa [AlgHom.AreSplit.iff_of_isScalarTower S]
  obtain ⟨n, ⟨eA⟩⟩ := IsFiniteSplit.nonempty_algEquiv_fun R A
  obtain ⟨m, ⟨eB⟩⟩ := IsFiniteSplit.nonempty_algEquiv_fun R B
  let f' : (Fin n → R) →ₐ[R] Fin m → R :=
    eB.toAlgHom.comp (f.comp eA.symm.toAlgHom)
  let g' : (Fin n → R) →ₐ[R] Fin m → R :=
    eB.toAlgHom.comp (g.comp eA.symm.toAlgHom)
  obtain ⟨r, hr, sigma, tau, hsigma, htau⟩ :=
    AlgHom.exists_cover_eq_compRight''₂ f' g' p.asIdeal
  refine ⟨Localization.Away r, inferInstance, inferInstance, inferInstance,
    ?_, ?_, ?_⟩
  · exact (PrimeSpectrum.localization_away_isOpenEmbedding _ r).isOpenMap
  · change p ∈ Set.range
      (PrimeSpectrum.comap <| algebraMap R (Localization.Away r))
    rwa [PrimeSpectrum.localization_away_comap_range _ r]
  · refine ⟨n, m,
      (Algebra.TensorProduct.congr .refl eA).trans
        (Algebra.TensorProduct.piScalarRight ..),
      (Algebra.TensorProduct.congr .refl eB).trans
        (Algebra.TensorProduct.piScalarRight ..),
      sigma, tau, ?_, ?_⟩
    · ext a i : 3
      let e := TensorProduct.piScalarRight R (Localization.Away r)
        (Localization.Away r) (Fin m)
      simpa [TensorProduct.piScalarRight_tmul, f', e] using
        congrFun (congr(e ($(hsigma) (1 ⊗ₜ eA a)))) i
    · ext a i : 3
      let e := TensorProduct.piScalarRight R (Localization.Away r)
        (Localization.Away r) (Fin m)
      simpa [TensorProduct.piScalarRight_tmul, g', e] using
        congrFun (congr(e ($(htau) (1 ⊗ₜ eA a)))) i

end Algebra

namespace CategoryTheory.Limits

/-- The canonical cofork of the maps between copowers induced by two
functions of finite indexing types. -/
private noncomputable def sigmaMapCoforkGeneric {C : Type u}
    [Category.{v} C] {E F : Type w} (X : C) (sigma tau : F → E)
    [HasCoproductsOfShape E C] [HasCoproductsOfShape F C]
    [HasCoproductsOfShape (Function.Coequalizer sigma tau) C] :
    Cofork
      (Sigma.map' (f := fun _ : E ↦ X) (g := fun _ : F ↦ X)
        sigma (fun _ ↦ 𝟙 X))
      (Sigma.map' (f := fun _ : E ↦ X) (g := fun _ : F ↦ X)
        tau (fun _ ↦ 𝟙 X)) :=
  Cofork.ofπ
    (Sigma.map' (f := fun _ : Function.Coequalizer sigma tau ↦ X)
      (g := fun _ : E ↦ X)
      (Function.Coequalizer.mk sigma tau) (fun _ ↦ 𝟙 X))
    (by
      rw [Sigma.map'_comp_map', Sigma.map'_comp_map']
      apply Sigma.map'_eq
        (funext fun i ↦ Function.Coequalizer.condition sigma tau i)
      intro _
      simp)

/-- The copower of an object by the coequalizer of two functions is the
coequalizer of the induced maps between copowers. -/
private def isColimitCoforkSigmaMap {C : Type u} [Category.{v} C]
    {E F : Type w} (X : C) (σ τ : E → F)
    [HasCoproductsOfShape E C] [HasCoproductsOfShape F C]
    [HasCoproductsOfShape (Function.Coequalizer σ τ) C] :
    IsColimit (sigmaMapCoforkGeneric X σ τ) := by
  classical
  let Q := Function.Coequalizer σ τ
  let q : F → Q := Function.Coequalizer.mk σ τ
  let f : (∐ fun _ : E => X) ⟶ ∐ fun _ : F => X :=
    Sigma.map' (f := fun _ : F => X) (g := fun _ : E => X) σ (fun _ => 𝟙 X)
  let g : (∐ fun _ : E => X) ⟶ ∐ fun _ : F => X :=
    Sigma.map' (f := fun _ : F => X) (g := fun _ : E => X) τ (fun _ => 𝟙 X)
  let π : (∐ fun _ : F => X) ⟶ ∐ fun _ : Q => X :=
    Sigma.map' (f := fun _ : Q => X) (g := fun _ : F => X) q (fun _ => 𝟙 X)
  change IsColimit (Cofork.ofπ π _)
  refine Cofork.IsColimit.mk' _ fun s => ?_
  let h : F → (X ⟶ s.pt) := fun i => Sigma.ι (fun _ : F => X) i ≫ s.π
  have hστ (e : E) : h (σ e) = h (τ e) := by
    have := congrArg (fun k => Sigma.ι (fun _ : E => X) e ≫ k) s.condition
    simpa only [f, g, h, Sigma.ι_comp_map'_assoc, Category.id_comp] using this
  let d : Q → (X ⟶ s.pt) := Function.Coequalizer.desc σ τ h (funext hστ)
  let l : (∐ fun _ : Q => X) ⟶ s.pt := Sigma.desc d
  refine ⟨l, ?_, ?_⟩
  · change π ≫ l = s.π
    ext i
    simp only [π, q, l, d, h, Sigma.ι_comp_map'_assoc,
      Category.id_comp, Sigma.ι_comp_desc, Function.Coequalizer.desc_mk]
  · intro m hm
    change π ≫ m = s.π at hm
    apply Sigma.hom_ext
    intro i
    obtain ⟨i, rfl⟩ := Function.Coequalizer.mk_surjective σ τ i
    calc
      Sigma.ι (fun _ : Q => X) (Function.Coequalizer.mk σ τ i) ≫ m =
          Sigma.ι (fun _ : F => X) i ≫ π ≫ m := by
            simp only [π, q, Sigma.ι_comp_map'_assoc, Category.id_comp]
      _ = Sigma.ι (fun _ : F => X) i ≫ s.π := by rw [hm]
      _ = Sigma.ι (fun _ : Q => X) (Function.Coequalizer.mk σ τ i) ≫ l := by
        simp only [l, d, h, Sigma.ι_comp_desc, Function.Coequalizer.desc_mk]

/-- A functor preserving the relevant finite copowers intertwines a map of
copowers with the corresponding map after applying the functor. -/
private lemma map_sigmaMap_naturality {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D]
    [HasFiniteCoproducts C] [HasFiniteCoproducts D]
    (G : C ⥤ D) [PreservesFiniteCoproducts G]
    {E F : Type w} [Finite E] [Finite F]
    (X : C) (sigma : F → E) :
    (PreservesCoproduct.iso G (fun _ : F ↦ X)).hom ≫
        Sigma.map' sigma (fun _ ↦ 𝟙 (G.obj X)) =
      G.map (Sigma.map' sigma (fun _ ↦ 𝟙 X)) ≫
        (PreservesCoproduct.iso G (fun _ : E ↦ X)).hom := by
  apply (cancel_epi
    (PreservesCoproduct.iso G (fun _ : F ↦ X)).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_comp_map']
  simp only [Category.id_comp]
  symm
  calc
    Sigma.ι (fun _ : F ↦ G.obj X) i ≫
          (PreservesCoproduct.iso G (fun _ : F ↦ X)).inv ≫
          G.map (Sigma.map' sigma (fun _ ↦ 𝟙 X)) ≫
          (PreservesCoproduct.iso G (fun _ : E ↦ X)).hom =
        G.map (Sigma.ι (fun _ : F ↦ X) i) ≫
          G.map (Sigma.map' sigma (fun _ ↦ 𝟙 X)) ≫
          (PreservesCoproduct.iso G (fun _ : E ↦ X)).hom := by
            simp only [PreservesCoproduct.inv_hom, sigmaComparison,
              Sigma.ι_comp_desc_assoc]
    _ = G.map (Sigma.ι (fun _ : F ↦ X) i ≫
          Sigma.map' sigma (fun _ ↦ 𝟙 X)) ≫
          (PreservesCoproduct.iso G (fun _ : E ↦ X)).hom := by
            rw [G.map_comp]
            simp only [Category.assoc]
    _ = G.map (Sigma.ι (fun _ : E ↦ X) (sigma i)) ≫
          (PreservesCoproduct.iso G (fun _ : E ↦ X)).hom := by
            rw [Sigma.ι_comp_map']
            simp
    _ = Sigma.ι (fun _ : E ↦ G.obj X) (sigma i) := by
          simpa [← PreservesCoproduct.inv_hom] using
            (map_ι_comp_inv_sigmaComparison
              (G := G) (f := fun _ : E ↦ X) (sigma i))

/-- A functor preserving finite coproducts preserves the canonical
coequalizer of two maps between finite copowers. -/
private def isColimitMapSigmaMapCofork {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D]
    [HasFiniteCoproducts C] [HasFiniteCoproducts D]
    (G : C ⥤ D) [PreservesFiniteCoproducts G]
    {E F : Type w} [Finite E] [Finite F]
    (X : C) (sigma tau : F → E)
    [Finite (Function.Coequalizer sigma tau)] :
    IsColimit (G.mapCocone (sigmaMapCoforkGeneric X sigma tau)) := by
  classical
  let Q := Function.Coequalizer sigma tau
  let c := sigmaMapCoforkGeneric (G.obj X) sigma tau
  let c' : Cofork
      (G.map (Sigma.map' sigma (fun _ ↦ 𝟙 X)))
      (G.map (Sigma.map' tau (fun _ ↦ 𝟙 X))) :=
    Cofork.ofπ
      (G.map (sigmaMapCoforkGeneric X sigma tau).π)
      (by
        simpa only [← G.map_comp] using
          congrArg G.map (sigmaMapCoforkGeneric X sigma tau).condition)
  have hc : IsColimit c :=
    isColimitCoforkSigmaMap (G.obj X) sigma tau
  have hc' : IsColimit c' := (Cofork.isColimitEquivOfIsos c' c
    (PreservesCoproduct.iso G (fun _ : F ↦ X))
    (PreservesCoproduct.iso G (fun _ : E ↦ X))
    (PreservesCoproduct.iso G (fun _ : Q ↦ X))
    (map_sigmaMap_naturality G X sigma)
    (map_sigmaMap_naturality G X tau)
    (by
      change
        (PreservesCoproduct.iso G (fun _ : E ↦ X)).inv ≫
            G.map (Sigma.map' (Function.Coequalizer.mk sigma tau)
              (fun _ ↦ 𝟙 X)) ≫
            (PreservesCoproduct.iso G (fun _ : Q ↦ X)).hom =
          Sigma.map' (Function.Coequalizer.mk sigma tau)
            (fun _ ↦ 𝟙 (G.obj X))
      apply (cancel_epi
        (PreservesCoproduct.iso G (fun _ : E ↦ X)).hom).1
      simp only [Iso.hom_inv_id_assoc]
      exact (map_sigmaMap_naturality G X
        (Function.Coequalizer.mk sigma tau)).symm)).symm hc
  let h := (isColimitMapCoconeCoforkEquiv G
    (sigmaMapCoforkGeneric X sigma tau).condition).symm hc'
  exact h

/-- If a parallel pair is conjugate to maps between finite copowers, then
every finite-coproduct-preserving functor preserves its coequalizer. -/
private lemma preservesColimit_parallelPair_of_split
    {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D]
    [HasFiniteCoproducts C] [HasFiniteCoproducts D]
    (G : C ⥤ D) [PreservesFiniteCoproducts G]
    {A B : C} (f g : A ⟶ B)
    {E F : Type w} [Finite E] [Finite F]
    (X : C) (sigma tau : F → E)
    (eA : A ≅ ∐ fun _ : F ↦ X)
    (eB : B ≅ ∐ fun _ : E ↦ X)
    (hf : f ≫ eB.hom = eA.hom ≫
      Sigma.map' sigma (fun _ ↦ 𝟙 X))
    (hg : g ≫ eB.hom = eA.hom ≫
      Sigma.map' tau (fun _ ↦ 𝟙 X)) :
    PreservesColimit (parallelPair f g) G := by
  classical
  let Q := Function.Coequalizer sigma tau
  let : Finite Q := Finite.of_surjective
    (Function.Coequalizer.mk sigma tau)
    (Function.Coequalizer.mk_surjective sigma tau)
  let fModel : (∐ fun _ : F ↦ X) ⟶ ∐ fun _ : E ↦ X :=
    Sigma.map' sigma (fun _ ↦ 𝟙 X)
  let gModel : (∐ fun _ : F ↦ X) ⟶ ∐ fun _ : E ↦ X :=
    Sigma.map' tau (fun _ ↦ 𝟙 X)
  let model : Cofork fModel gModel :=
    sigmaMapCoforkGeneric X sigma tau
  have hmodel : IsColimit model :=
    isColimitCoforkSigmaMap X sigma tau
  have hmap : IsColimit (G.mapCocone model) := by
    exact isColimitMapSigmaMapCofork G X sigma tau
  have hpres : PreservesColimit (parallelPair fModel gModel) G :=
    preservesColimit_of_preserves_colimit_cocone
      (K := parallelPair fModel gModel) (t := model) hmodel hmap
  let : PreservesColimit (parallelPair fModel gModel) G := hpres
  let eDiagram : parallelPair f g ≅ parallelPair fModel gModel :=
    parallelPair.ext eA eB
      (by
        change f ≫ eB.hom = eA.hom ≫ fModel
        simpa only [fModel] using hf)
      (by
        change g ≫ eB.hom = eA.hom ≫ gModel
        simpa only [gModel] using hg)
  exact preservesColimit_of_iso_diagram G eDiagram.symm

end CategoryTheory.Limits

namespace AlgebraicGeometry

private instance finiteEtaleOverCategoryForCoequalizers (Y : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ Y) :=
  FiniteEtale.instCategory Y

private lemma sigmaMap_comp_sigmaSpec {R : Type u} [CommRing R]
    {E F : Type u} (sigma : E → F) :
    Sigma.map' (f := fun _ : F ↦ Spec (.of R))
        (g := fun _ : E ↦ Spec (.of R)) sigma (fun _ ↦ 𝟙 _) ≫
      sigmaSpec (fun _ : F ↦ CommRingCat.of R) =
    sigmaSpec (fun _ : E ↦ CommRingCat.of R) ≫
      Spec.map (CommRingCat.ofHom (RingHom.compRight R sigma)) := by
  apply Sigma.hom_ext (f := fun _ : E ↦ Spec (.of R))
  intro e
  simp only [← Category.assoc, Sigma.ι_comp_map', Category.id_comp,
    ι_sigmaSpec]
  rw [← Spec.map_comp]
  congr 1

private lemma sigmaSpec_comp_algebraMap {R : Type u} [CommRing R]
    (E : Type u) [Finite E] :
    sigmaSpec (fun _ : E ↦ CommRingCat.of R) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (E → R))) =
    Sigma.desc (fun _ : E ↦ 𝟙 (Spec (.of R))) := by
  apply Sigma.hom_ext (f := fun _ : E ↦ Spec (.of R))
  intro e
  simp only [← Category.assoc, ι_sigmaSpec, Sigma.ι_comp_desc]
  rw [← Spec.map_comp]
  convert Spec.map_id (.of R)
  ext x
  rfl

private noncomputable def specPiIsoSigma {R : Type u} [CommRing R]
    (E : Type u) [Finite E] :
    Spec (.of (E → R)) ≅ ∐ fun _ : E ↦ Spec (.of R) :=
  (asIso (sigmaSpec (fun _ : E ↦ CommRingCat.of R))).symm

private def specMapAlgEquiv {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T) :
    Spec (.of S) ≅ Spec (.of T) where
  hom := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  inv := Spec.map (CommRingCat.ofHom e.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp]
    convert Spec.map_id (.of S)
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    rw [← Spec.map_comp]
    convert Spec.map_id (.of T)
    ext x
    exact e.apply_symm_apply x

private noncomputable def specSplitIso {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    {E : Type u} [Finite E] (e : S ≃ₐ[R] (E → R)) :
    Spec (.of S) ≅ ∐ fun _ : E ↦ Spec (.of R) :=
  specMapAlgEquiv e ≪≫ specPiIsoSigma E

private lemma specSplitIso_hom_over {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    {E : Type u} [Finite E] (e : S ≃ₐ[R] (E → R)) :
    (specSplitIso e).hom ≫
      Sigma.desc (fun _ : E ↦ 𝟙 (Spec (.of R))) =
    Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [← sigmaSpec_comp_algebraMap E]
  simp only [specSplitIso, specPiIsoSigma, Iso.trans_hom, specMapAlgEquiv,
    Iso.symm_hom, asIso_inv, Category.assoc]
  slice_lhs 2 3 => rw [IsIso.inv_hom_id]
  simp only [Category.id_comp]
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact e.symm.commutes x

private lemma specMap_comp_specSplitIso {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] {E F : Type u} [Finite E] [Finite F]
    (eS : S ≃ₐ[R] (E → R)) (eT : T ≃ₐ[R] (F → R))
    (f : S →ₐ[R] T) (sigma : F → E)
    (h : eT.toAlgHom.comp f =
      (AlgHom.compRight R R sigma).comp eS.toAlgHom) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (specSplitIso eS).hom =
      (specSplitIso eT).hom ≫
        Sigma.map' sigma (fun _ ↦ 𝟙 (Spec (.of R))) := by
  apply (cancel_mono (sigmaSpec (fun _ : E ↦ CommRingCat.of R))).1
  simp only [specSplitIso, specPiIsoSigma, Iso.trans_hom,
    specMapAlgEquiv, Iso.symm_hom, asIso_inv, Category.assoc]
  rw [sigmaMap_comp_sigmaSpec sigma]
  slice_lhs 3 4 => rw [IsIso.inv_hom_id]
  slice_rhs 2 3 => rw [IsIso.inv_hom_id]
  simp only [Category.comp_id, Category.id_comp]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  change f (eS.symm x) = eT.symm ((RingHom.compRight R sigma) x)
  calc
    f (eS.symm x) = eT.symm (eT (f (eS.symm x))) :=
      (eT.symm_apply_apply _).symm
    _ = eT.symm ((AlgHom.compRight R R sigma) (eS (eS.symm x))) := by
      exact congrArg eT.symm (DFunLike.congr_fun h (eS.symm x))
    _ = eT.symm ((RingHom.compRight R sigma) x) := by
      congr 1
      ext i
      exact congrFun (eS.apply_symm_apply x) (sigma i)

private noncomputable def finiteEtaleRingEquiv (R : CommRingCat.{u}) :=
  AffineAnd.overSpecEquivUnder (@IsFiniteEtale : MorphismProperty Scheme.{u})
    RingHom.FiniteEtale.respectsIso R

@[reducible] private noncomputable def gammaAlgebraOfHom
    {R : Type u} [CommRing R] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of R)) : Algebra R Γ(Z, ⊤) :=
  (((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop).hom).toAlgebra

private lemma hom_eq_isoSpec_hom_comp_specMap_algebraMap
    {R : Type u} [CommRing R] {Z : Scheme.{u}} [IsAffine Z]
    (p : Z ⟶ Spec (.of R)) :
    letI : Algebra R Γ(Z, ⊤) := gammaAlgebraOfHom p
    p = Z.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z, ⊤))) := by
  let : Algebra R Γ(Z, ⊤) := gammaAlgebraOfHom p
  change p = Z.isoSpec.hom ≫
    Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop)
  have hnat : Z.isoSpec.hom ≫ Spec.map p.appTop =
      p ≫ (Spec (.of R)).isoSpec.hom :=
    Scheme.isoSpec_hom_naturality p
  have hcancel : (Spec (.of R)).isoSpec.hom ≫
      Spec.map (Scheme.ΓSpecIso (.of R)).inv = 𝟙 _ := by
    rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id]
  calc
    p = p ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = p ≫ ((Spec (.of R)).isoSpec.hom ≫
        Spec.map (Scheme.ΓSpecIso (.of R)).inv) :=
      congrArg (fun k ↦ p ≫ k) hcancel.symm
    _ = (p ≫ (Spec (.of R)).isoSpec.hom) ≫
        Spec.map (Scheme.ΓSpecIso (.of R)).inv :=
      (Category.assoc _ _ _).symm
    _ = (Z.isoSpec.hom ≫ Spec.map p.appTop) ≫
        Spec.map (Scheme.ΓSpecIso (.of R)).inv :=
      congrArg (fun k ↦ k ≫ Spec.map (Scheme.ΓSpecIso (.of R)).inv)
        hnat.symm
    _ = Z.isoSpec.hom ≫
        (Spec.map p.appTop ≫
          Spec.map (Scheme.ΓSpecIso (.of R)).inv) :=
      Category.assoc _ _ _
    _ = Z.isoSpec.hom ≫
        Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop) := by
      rw [Spec.map_comp]

@[reducible] private noncomputable def overSpecAlgebra
    {R : Type u} [CommRing R] (L : FiniteEtale (Spec (.of R))) :
    Algebra R Γ(L.left, ⊤) :=
  gammaAlgebraOfHom L.hom

private noncomputable def pullbackIsoSpecTensorOfHom
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {Z : Scheme.{u}} [IsAffine Z] (p : Z ⟶ Spec (.of R)) :
    letI : Algebra R Γ(Z, ⊤) := gammaAlgebraOfHom p
    pullback p (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≅
      Spec (.of (TensorProduct R S (Γ(Z, ⊤)))) := by
  letI : Algebra R Γ(Z, ⊤) := gammaAlgebraOfHom p
  let pS := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let pΓ := Spec.map
    (CommRingCat.ofHom (algebraMap R Γ(Z, ⊤)))
  let e₀ : pullback p pS ≅ pullback pΓ pS :=
    asIso (pullback.map p pS pΓ pS
      Z.isoSpec.hom (𝟙 _) (𝟙 _)
      (by
        simpa only [Category.comp_id] using
          hom_eq_isoSpec_hom_comp_specMap_algebraMap p)
      (by simp))
  exact e₀ ≪≫ pullbackSymmetry pΓ pS ≪≫
    pullbackSpecIso R S Γ(Z, ⊤)

private lemma pullbackIsoSpecTensorOfHom_hom_over
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {Z : Scheme.{u}} [IsAffine Z] (p : Z ⟶ Spec (.of R)) :
    letI : Algebra R Γ(Z, ⊤) := gammaAlgebraOfHom p
    (pullbackIsoSpecTensorOfHom p).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap S (TensorProduct R S (Γ(Z, ⊤))))) =
      pullback.snd p
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let : Algebra R Γ(Z, ⊤) := gammaAlgebraOfHom p
  simp [pullbackIsoSpecTensorOfHom, Category.assoc]

private noncomputable def pullbackSplitIsoOfHom
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {Z : Scheme.{u}} [IsAffine Z] (p : Z ⟶ Spec (.of R)) :
    letI : Algebra R Γ(Z, ⊤) := gammaAlgebraOfHom p
    ∀ {E : Type u} [Finite E]
      (_e : TensorProduct R S (Γ(Z, ⊤)) ≃ₐ[S] (E → S)),
      pullback p (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≅
        ∐ fun _ : E ↦ Spec (.of S) := by
  letI : Algebra R Γ(Z, ⊤) := gammaAlgebraOfHom p
  intro E _ e
  exact pullbackIsoSpecTensorOfHom p ≪≫ specSplitIso e

private lemma pullbackSplitIsoOfHom_hom_over
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {Z : Scheme.{u}} [IsAffine Z] (p : Z ⟶ Spec (.of R)) :
    letI : Algebra R Γ(Z, ⊤) := gammaAlgebraOfHom p
    ∀ {E : Type u} [Finite E]
      (e : TensorProduct R S (Γ(Z, ⊤)) ≃ₐ[S] (E → S)),
      (pullbackSplitIsoOfHom p e).hom ≫
          Sigma.desc (fun _ : E ↦ 𝟙 (Spec (.of S))) =
        pullback.snd p
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let : Algebra R Γ(Z, ⊤) := gammaAlgebraOfHom p
  intro E _ e
  simp only [pullbackSplitIsoOfHom, Iso.trans_hom, Category.assoc]
  rw [specSplitIso_hom_over e,
    pullbackIsoSpecTensorOfHom_hom_over p]

private noncomputable def pullbackSplitIso
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (L : FiniteEtale (Spec (.of R))) [IsAffine L.left] :
    letI : Algebra R Γ(L.left, ⊤) := overSpecAlgebra L
    ∀ {E : Type u} [Finite E]
      (_e : TensorProduct R S (Γ(L.left, ⊤)) ≃ₐ[S] (E → S)),
      ((FiniteEtale.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj L).left ≅
        ∐ fun _ : E ↦ Spec (.of S) := by
  let p : L.left ⟶ Spec (.of R) := L.hom
  change letI : Algebra R Γ(L.left, ⊤) := gammaAlgebraOfHom p
    ∀ {E : Type u} [Finite E]
      (_e : TensorProduct R S (Γ(L.left, ⊤)) ≃ₐ[S] (E → S)),
      pullback p (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≅
        ∐ fun _ : E ↦ Spec (.of S)
  exact pullbackSplitIsoOfHom p

private lemma pullbackSplitIso_hom_over
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (L : FiniteEtale (Spec (.of R))) [IsAffine L.left] :
    letI : Algebra R Γ(L.left, ⊤) := overSpecAlgebra L
    ∀ {E : Type u} [Finite E]
      (e : TensorProduct R S (Γ(L.left, ⊤)) ≃ₐ[S] (E → S)),
      (pullbackSplitIso L e).hom ≫
          Sigma.desc (fun _ : E ↦ 𝟙 (Spec (.of S))) =
        ((FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj L).hom := by
  let p : L.left ⟶ Spec (.of R) := L.hom
  change letI : Algebra R Γ(L.left, ⊤) := gammaAlgebraOfHom p
    ∀ {E : Type u} [Finite E]
      (e : TensorProduct R S (Γ(L.left, ⊤)) ≃ₐ[S] (E → S)),
      (pullbackSplitIsoOfHom p e).hom ≫
          Sigma.desc (fun _ : E ↦ 𝟙 (Spec (.of S))) =
        pullback.snd p
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  exact pullbackSplitIsoOfHom_hom_over p

private lemma pullbackMap_pullbackSpecIso {R S A B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) :
    let pS := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let pA := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let pB := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let a := Spec.map (CommRingCat.ofHom f.toRingHom)
    let q := pullback.map pS pB pS pA (𝟙 _) a (𝟙 _)
      (by simp) (by
        rw [← Spec.map_comp]
        simp only [Category.comp_id]
        dsimp only [pB]
        congr 1
        ext x
        change (algebraMap R B) x = f ((algebraMap R A) x)
        exact (f.commutes x).symm)
    q ≫ (pullbackSpecIso R S A).hom =
      (pullbackSpecIso R S B).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom) := by
  dsimp only
  apply (cancel_mono (pullbackSpecIso R S A).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, Category.comp_id,
      pullbackSpecIso_inv_fst]
    apply (cancel_epi (pullbackSpecIso R S B).inv).1
    rw [pullbackSpecIso_inv_fst]
    slice_rhs 1 2 => rw [Iso.inv_hom_id]
    simp only [Category.id_comp]
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp
  · simp only [Category.assoc, pullback.lift_snd,
      pullbackSpecIso_inv_snd]
    apply (cancel_epi (pullbackSpecIso R S B).inv).1
    slice_lhs 1 2 => rw [pullbackSpecIso_inv_snd]
    slice_rhs 1 2 => rw [Iso.inv_hom_id]
    simp only [Category.id_comp]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1

private noncomputable def baseChangeMapOfHom
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of R))
    (pY : Y ⟶ Spec (.of R)) (f : X ⟶ Y) (w : f ≫ pY = pX) :
    pullback pX (Spec.map (CommRingCat.ofHom (algebraMap R S))) ⟶
      pullback pY (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  pullback.map pX
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) pY
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    f (𝟙 _) (𝟙 _) (by simpa only [Category.comp_id] using w.symm)
    (by simp)

private lemma baseChangeMap_comp_pullbackIsoSpecTensorOfHom
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (pX : X ⟶ Spec (.of R)) (pY : Y ⟶ Spec (.of R))
    (f : X ⟶ Y) (w : f ≫ pY = pX) :
    letI : Algebra R Γ(X, ⊤) := gammaAlgebraOfHom pX
    letI : Algebra R Γ(Y, ⊤) := gammaAlgebraOfHom pY
    ∀ (fAlg : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤))
      (_hf : f.appTop.hom = fAlg.toRingHom),
      baseChangeMapOfHom pX pY f w ≫
          (pullbackIsoSpecTensorOfHom pY).hom =
        (pullbackIsoSpecTensorOfHom pX).hom ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id S S) fAlg).toRingHom) := by
  let : Algebra R Γ(X, ⊤) := gammaAlgebraOfHom pX
  let : Algebra R Γ(Y, ⊤) := gammaAlgebraOfHom pY
  intro fAlg hf
  let pS := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let pΓX := Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))
  let pΓY := Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, ⊤)))
  let a := Spec.map (CommRingCat.ofHom fAlg.toRingHom)
  let eX : pullback pX pS ≅ pullback pΓX pS :=
    asIso (pullback.map pX pS pΓX pS
      X.isoSpec.hom (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using
        hom_eq_isoSpec_hom_comp_specMap_algebraMap pX)
      (by simp))
  let eY : pullback pY pS ≅ pullback pΓY pS :=
    asIso (pullback.map pY pS pΓY pS
      Y.isoSpec.hom (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using
        hom_eq_isoSpec_hom_comp_specMap_algebraMap pY)
      (by simp))
  let q : pullback pX pS ⟶ pullback pY pS :=
    baseChangeMapOfHom pX pY f w
  let qSpec : pullback pS pΓX ⟶ pullback pS pΓY :=
    pullback.map pS pΓX pS pΓY
      (𝟙 _) a (𝟙 _) (by simp) (by
        change Spec.map (CommRingCat.ofHom
            (algebraMap R Γ(X, ⊤))) ≫ 𝟙 _ =
          Spec.map (CommRingCat.ofHom fAlg.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, ⊤)))
        rw [← Spec.map_comp]
        simp only [Category.comp_id]
        congr 1
        ext r
        change (algebraMap R Γ(X, ⊤)) r =
          fAlg ((algebraMap R Γ(Y, ⊤)) r)
        exact (fAlg.commutes r).symm)
  have happ : f.appTop = CommRingCat.ofHom fAlg.toRingHom := by
    ext r
    exact DFunLike.congr_fun hf r
  have hnat : f ≫ Y.isoSpec.hom = X.isoSpec.hom ≫ a := by
    rw [← Scheme.isoSpec_hom_naturality f]
    dsimp only [a]
    rw [happ]
  have q_fst : q ≫ pullback.fst pY pS = pullback.fst pX pS ≫ f := by
    dsimp only [q, baseChangeMapOfHom, pullback.map]
    exact pullback.lift_fst _ _ _
  have q_snd : q ≫ pullback.snd pY pS = pullback.snd pX pS := by
    dsimp only [q, baseChangeMapOfHom, pullback.map]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have eX_fst : eX.hom ≫ pullback.fst pΓX pS =
      pullback.fst pX pS ≫ X.isoSpec.hom := by
    simp [eX, pullback.map]
  have eX_snd : eX.hom ≫ pullback.snd pΓX pS =
      pullback.snd pX pS := by
    simp [eX, pullback.map]
  have eY_fst : eY.hom ≫ pullback.fst pΓY pS =
      pullback.fst pY pS ≫ Y.isoSpec.hom := by
    simp [eY, pullback.map]
  have eY_snd : eY.hom ≫ pullback.snd pΓY pS =
      pullback.snd pY pS := by
    simp [eY, pullback.map]
  have qSpec_fst : qSpec ≫ pullback.fst pS pΓY =
      pullback.fst pS pΓX := by
    simp [qSpec, pullback.map]
  have qSpec_snd : qSpec ≫ pullback.snd pS pΓY =
      pullback.snd pS pΓX ≫ a := by
    simp [qSpec, pullback.map]
  have hpre : q ≫ eY.hom ≫ (pullbackSymmetry pΓY pS).hom =
      eX.hom ≫ (pullbackSymmetry pΓX pS).hom ≫ qSpec := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [pullbackSymmetry_hom_comp_fst, eY_snd, q_snd,
        qSpec_fst, pullbackSymmetry_hom_comp_fst, eX_snd]
    · simp only [Category.assoc]
      rw [pullbackSymmetry_hom_comp_snd, eY_fst,
        reassoc_of% q_fst, qSpec_snd,
        pullbackSymmetry_hom_comp_snd_assoc, reassoc_of% eX_fst, hnat]
  change q ≫ ((eY ≪≫ pullbackSymmetry pΓY pS ≪≫
      pullbackSpecIso R S Γ(Y, ⊤)).hom) =
    ((eX ≪≫ pullbackSymmetry pΓX pS ≪≫
      pullbackSpecIso R S Γ(X, ⊤)).hom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id S S) fAlg).toRingHom)
  simp only [Iso.trans_hom, Category.assoc]
  slice_lhs 1 3 => rw [hpre]
  slice_lhs 3 4 => rw [pullbackMap_pullbackSpecIso fAlg]

private lemma pullbackMap_comp_pullbackSplitIso
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (Lsource Ltarget : FiniteEtale (Spec (.of R)))
    [IsAffine Lsource.left] [IsAffine Ltarget.left]
    (f : Lsource ⟶ Ltarget) :
    letI : Algebra R Γ(Lsource.left, ⊤) := overSpecAlgebra Lsource
    letI : Algebra R Γ(Ltarget.left, ⊤) := overSpecAlgebra Ltarget
    ∀ (fAlg : Γ(Ltarget.left, ⊤) →ₐ[R] Γ(Lsource.left, ⊤))
      (_hf : f.left.appTop.hom = fAlg.toRingHom)
      {Esource Etarget : Type u} [Finite Esource] [Finite Etarget]
      (eTarget : TensorProduct R S Γ(Ltarget.left, ⊤) ≃ₐ[S] (Etarget → S))
      (eSource : TensorProduct R S Γ(Lsource.left, ⊤) ≃ₐ[S] (Esource → S))
      (sigma : Esource → Etarget)
      (_h : eSource.toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id S S) fAlg) =
        (AlgHom.compRight S S sigma).comp eTarget.toAlgHom),
      ((FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map f).left ≫
          (pullbackSplitIso Ltarget eTarget).hom =
        (pullbackSplitIso Lsource eSource).hom ≫
          Sigma.map' sigma (fun _ ↦ 𝟙 (Spec (.of S))) := by
  let pSource : Lsource.left ⟶ Spec (.of R) := Lsource.hom
  let pTarget : Ltarget.left ⟶ Spec (.of R) := Ltarget.hom
  change letI : Algebra R Γ(Lsource.left, ⊤) := gammaAlgebraOfHom pSource
    letI : Algebra R Γ(Ltarget.left, ⊤) := gammaAlgebraOfHom pTarget
    ∀ (fAlg : Γ(Ltarget.left, ⊤) →ₐ[R] Γ(Lsource.left, ⊤))
      (_hf : f.left.appTop.hom = fAlg.toRingHom)
      {Esource Etarget : Type u} [Finite Esource] [Finite Etarget]
      (eTarget : TensorProduct R S Γ(Ltarget.left, ⊤) ≃ₐ[S] (Etarget → S))
      (eSource : TensorProduct R S Γ(Lsource.left, ⊤) ≃ₐ[S] (Esource → S))
      (sigma : Esource → Etarget)
      (_h : eSource.toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id S S) fAlg) =
        (AlgHom.compRight S S sigma).comp eTarget.toAlgHom),
      ((FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map f).left ≫
          (pullbackSplitIsoOfHom pTarget eTarget).hom =
        (pullbackSplitIsoOfHom pSource eSource).hom ≫
          Sigma.map' sigma (fun _ ↦ 𝟙 (Spec (.of S)))
  let : Algebra R Γ(Lsource.left, ⊤) := gammaAlgebraOfHom pSource
  let : Algebra R Γ(Ltarget.left, ⊤) := gammaAlgebraOfHom pTarget
  intro fAlg hf Esource Etarget _ _ eTarget eSource sigma h
  have w : f.left ≫ pTarget = pSource := MorphismProperty.Over.w f
  let q := baseChangeMapOfHom (R := R) (S := S)
    pSource pTarget f.left w
  have hmap : ((FiniteEtale.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map f).left = q := by
    rfl
  rw [hmap]
  dsimp only [q]
  simp only [pullbackSplitIsoOfHom, Iso.trans_hom]
  have hbase := baseChangeMap_comp_pullbackIsoSpecTensorOfHom
    (R := R) (S := S) pSource pTarget f.left w fAlg hf
  have hsplit := specMap_comp_specSplitIso eTarget eSource
    (Algebra.TensorProduct.map (AlgHom.id S S) fAlg) sigma h
  calc
    baseChangeMapOfHom pSource pTarget f.left w ≫
          ((pullbackIsoSpecTensorOfHom pTarget).hom ≫
            (specSplitIso eTarget).hom) =
        (baseChangeMapOfHom pSource pTarget f.left w ≫
          (pullbackIsoSpecTensorOfHom pTarget).hom) ≫
            (specSplitIso eTarget).hom := (Category.assoc _ _ _).symm
    _ = ((pullbackIsoSpecTensorOfHom pSource).hom ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.map
              (AlgHom.id S S) fAlg).toRingHom)) ≫
            (specSplitIso eTarget).hom :=
      congrArg (fun k ↦ k ≫ (specSplitIso eTarget).hom) hbase
    _ = (pullbackIsoSpecTensorOfHom pSource).hom ≫
          (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map
                (AlgHom.id S S) fAlg).toRingHom) ≫
            (specSplitIso eTarget).hom) := Category.assoc _ _ _
    _ = (pullbackIsoSpecTensorOfHom pSource).hom ≫
          ((specSplitIso eSource).hom ≫
            Sigma.map' sigma (fun _ ↦ 𝟙 (Spec (.of S)))) :=
      congrArg (fun k ↦ (pullbackIsoSpecTensorOfHom pSource).hom ≫ k)
        hsplit
    _ = ((pullbackIsoSpecTensorOfHom pSource).hom ≫
          (specSplitIso eSource).hom) ≫
            Sigma.map' sigma (fun _ ↦ 𝟙 (Spec (.of S))) :=
      (Category.assoc _ _ _).symm

private def splitBase (R : CommRingCat.{u}) : FiniteEtale (Spec R) := by
  letI : IsFiniteEtale (𝟙 (Spec R)) :=
    MorphismProperty.id_mem @IsFiniteEtale (Spec R)
  exact FiniteEtale.mk (𝟙 (Spec R))

private noncomputable def forgetToUnderlyingScheme (Y : Scheme.{u}) :
    FiniteEtale Y ⥤ Scheme.{u} :=
  FiniteEtale.forget Y ⋙ CategoryTheory.Over.forget Y

private instance (Y : Scheme.{u}) :
    PreservesFiniteCoproducts (forgetToUnderlyingScheme Y) := by
  dsimp only [forgetToUnderlyingScheme]
  infer_instance

private noncomputable def forgetToScheme (R : CommRingCat.{u}) :
    FiniteEtale (Spec R) ⥤ Scheme.{u} :=
  forgetToUnderlyingScheme (Spec R)

private instance (R : CommRingCat.{u}) :
    PreservesFiniteCoproducts (forgetToScheme R) := by
  dsimp only [forgetToScheme]
  infer_instance

private lemma splitCopowerComparison_over
    (R : CommRingCat.{u}) {E : Type u} [Finite E] :
    (PreservesCoproduct.iso (forgetToScheme R)
      (fun _ : E ↦ splitBase R)).inv ≫
        (∐ fun _ : E ↦ splitBase R).hom =
      Sigma.desc (fun _ : E ↦ 𝟙 (Spec R)) := by
  apply Sigma.hom_ext
  intro i
  rw [PreservesCoproduct.inv_hom]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k : (forgetToScheme R).obj (splitBase R) ⟶
        (forgetToScheme R).obj (∐ fun _ : E ↦ splitBase R) =>
          k ≫ (∐ fun _ : E ↦ splitBase R).hom)
      (ι_comp_sigmaComparison (forgetToScheme R) (fun _ : E ↦ splitBase R) i)).trans
      ((MorphismProperty.Over.w (Sigma.ι (fun _ : E ↦ splitBase R) i)).trans
        (Sigma.ι_comp_desc (fun _ : E ↦ 𝟙 (Spec R)) i).symm))

private lemma splitCopowerComparison_naturality
    (R : CommRingCat.{u}) {E F : Type u} [Finite E] [Finite F]
    (sigma : F → E) :
    Sigma.map'
        (f := fun _ : E ↦
          (forgetToScheme R).obj (splitBase R))
        (g := fun _ : F ↦
          (forgetToScheme R).obj (splitBase R))
        sigma (fun _ ↦
          𝟙 ((forgetToScheme R).obj (splitBase R))) ≫
        (PreservesCoproduct.iso (forgetToScheme R)
          (fun _ : E ↦ splitBase R)).inv =
      (PreservesCoproduct.iso (forgetToScheme R)
        (fun _ : F ↦ splitBase R)).inv ≫
        (forgetToScheme R).map
          (Sigma.map' (f := fun _ : E ↦ splitBase R)
            (g := fun _ : F ↦ splitBase R)
            sigma (fun _ ↦ 𝟙 (splitBase R))) := by
  let h := CategoryTheory.Limits.map_sigmaMap_naturality
    (forgetToScheme R) (splitBase R) sigma
  apply (cancel_mono
    (PreservesCoproduct.iso (forgetToScheme R)
      (fun _ : E ↦ splitBase R)).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Category.assoc, ← h]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private noncomputable def finiteEtalePullbackSplitIso
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (L : FiniteEtale (Spec (.of R))) [IsAffine L.left] :
    letI : Algebra R Γ(L.left, ⊤) := overSpecAlgebra L
    ∀ {E : Type u} [Finite E]
      (_e : TensorProduct R S Γ(L.left, ⊤) ≃ₐ[S] (E → S)),
      (FiniteEtale.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj L ≅
        ∐ fun _ : E ↦ splitBase (.of S) := by
  letI : Algebra R Γ(L.left, ⊤) := overSpecAlgebra L
  intro E _ e
  refine MorphismProperty.Over.isoMk
    ((pullbackSplitIso L e) ≪≫
      (PreservesCoproduct.iso (forgetToScheme (.of S))
        (fun _ : E ↦ splitBase (.of S))).symm) ?_
  have hc := splitCopowerComparison_over (.of S) (E := E)
  change ((pullbackSplitIso L e).hom ≫
      (PreservesCoproduct.iso (forgetToScheme (.of S))
        (fun _ : E ↦ splitBase (.of S))).inv) ≫
      (∐ fun _ : E ↦ splitBase (.of S)).hom =
    ((FiniteEtale.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj L).hom
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ (pullbackSplitIso L e).hom ≫ k) hc).trans
      (pullbackSplitIso_hom_over L e))

private lemma finiteEtalePullbackSplitIso_naturality
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (Lsource Ltarget : FiniteEtale (Spec (.of R)))
    [IsAffine Lsource.left] [IsAffine Ltarget.left]
    (f : Lsource ⟶ Ltarget) :
    letI : Algebra R Γ(Lsource.left, ⊤) := overSpecAlgebra Lsource
    letI : Algebra R Γ(Ltarget.left, ⊤) := overSpecAlgebra Ltarget
    ∀ (fAlg : Γ(Ltarget.left, ⊤) →ₐ[R] Γ(Lsource.left, ⊤))
      (_hf : f.left.appTop.hom = fAlg.toRingHom)
      {Esource Etarget : Type u} [Finite Esource] [Finite Etarget]
      (eTarget : TensorProduct R S Γ(Ltarget.left, ⊤) ≃ₐ[S] (Etarget → S))
      (eSource : TensorProduct R S Γ(Lsource.left, ⊤) ≃ₐ[S] (Esource → S))
      (sigma : Esource → Etarget)
      (_h : eSource.toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id S S) fAlg) =
        (AlgHom.compRight S S sigma).comp eTarget.toAlgHom),
      (FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map f ≫
          (finiteEtalePullbackSplitIso Ltarget eTarget).hom =
        (finiteEtalePullbackSplitIso Lsource eSource).hom ≫
          Sigma.map' sigma (fun _ ↦ 𝟙 (splitBase (.of S))) := by
  let : Algebra R Γ(Lsource.left, ⊤) := overSpecAlgebra Lsource
  let : Algebra R Γ(Ltarget.left, ⊤) := overSpecAlgebra Ltarget
  intro fAlg hf Esource Etarget _ _ eTarget eSource sigma h
  apply MorphismProperty.Over.Hom.ext
  change ((FiniteEtale.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map f).left ≫
        ((pullbackSplitIso Ltarget eTarget).hom ≫
          (PreservesCoproduct.iso (forgetToScheme (.of S))
            (fun _ : Etarget ↦ splitBase (.of S))).inv) =
      ((pullbackSplitIso Lsource eSource).hom ≫
        (PreservesCoproduct.iso (forgetToScheme (.of S))
          (fun _ : Esource ↦ splitBase (.of S))).inv) ≫
        (Sigma.map' (f := fun _ : Etarget ↦ splitBase (.of S))
          (g := fun _ : Esource ↦ splitBase (.of S))
          sigma (fun _ ↦ 𝟙 (splitBase (.of S)))).left
  let csource := (PreservesCoproduct.iso (forgetToScheme (.of S))
    (fun _ : Esource ↦ splitBase (.of S))).inv
  let ctarget := (PreservesCoproduct.iso (forgetToScheme (.of S))
    (fun _ : Etarget ↦ splitBase (.of S))).inv
  have hnat : Sigma.map' sigma (fun _ ↦ 𝟙 (Spec (.of S))) ≫ ctarget =
      csource ≫ (Sigma.map' (f := fun _ : Etarget ↦ splitBase (.of S))
        (g := fun _ : Esource ↦ splitBase (.of S))
        sigma (fun _ ↦ 𝟙 (splitBase (.of S)))).left :=
    splitCopowerComparison_naturality (.of S) sigma
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k ↦ k ≫ ctarget)
      (pullbackMap_comp_pullbackSplitIso Lsource Ltarget f
        fAlg hf eTarget eSource sigma h)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k ↦ (pullbackSplitIso Lsource eSource).hom ≫ k) hnat).trans
          (Category.assoc _ _ _).symm)))

/-- After a pair of algebra maps has split, every functor preserving finite
coproducts preserves the coequalizer of the corresponding base-changed
finite étale maps. -/
private lemma preservesColimit_pullback_parallelPair_of_areSplit
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (Lsource Ltarget : FiniteEtale (Spec (.of R)))
    [IsAffine Lsource.left] [IsAffine Ltarget.left]
    (f g : Lsource ⟶ Ltarget) :
    letI : Algebra R Γ(Lsource.left, ⊤) := overSpecAlgebra Lsource
    letI : Algebra R Γ(Ltarget.left, ⊤) := overSpecAlgebra Ltarget
    ∀ (fAlg gAlg : Γ(Ltarget.left, ⊤) →ₐ[R] Γ(Lsource.left, ⊤))
      (_hf : f.left.appTop.hom = fAlg.toRingHom)
      (_hg : g.left.appTop.hom = gAlg.toRingHom)
      (_hsplit : Algebra.AlgHom.AreSplit
        (Algebra.TensorProduct.map (AlgHom.id S S) fAlg)
        (Algebra.TensorProduct.map (AlgHom.id S S) gAlg))
      {C : Type (u + 1)} [Category.{u} C] [HasFiniteCoproducts C]
      (G : FiniteEtale (Spec (.of S)) ⥤ C)
      [PreservesFiniteCoproducts G],
      PreservesColimit
        (parallelPair
          ((FiniteEtale.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map f)
          ((FiniteEtale.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map g)) G := by
  let : Algebra R Γ(Lsource.left, ⊤) := overSpecAlgebra Lsource
  let : Algebra R Γ(Ltarget.left, ⊤) := overSpecAlgebra Ltarget
  intro fAlg gAlg hf hg hsplit C _ _ G _
  rcases hsplit with ⟨n, m, eTarget₀, eSource₀, sigma₀, tau₀,
    hsigma₀, htau₀⟩
  let Etarget := ULift.{u, 0} (Fin n)
  let Esource := ULift.{u, 0} (Fin m)
  let eTarget := eTarget₀.trans (Algebra.finULiftPiAlgEquiv S n)
  let eSource := eSource₀.trans (Algebra.finULiftPiAlgEquiv S m)
  let sigma : Esource → Etarget := fun i ↦ ULift.up (sigma₀ i.down)
  let tau : Esource → Etarget := fun i ↦ ULift.up (tau₀ i.down)
  have hsigma : eSource.toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id S S) fAlg) =
      (AlgHom.compRight S S sigma).comp eTarget.toAlgHom := by
    simpa only [eTarget, eSource, sigma] using
      Algebra.liftFinSplitEq
        (Algebra.TensorProduct.map (AlgHom.id S S) fAlg)
        n m eTarget₀ eSource₀ sigma₀ hsigma₀
  have htau : eSource.toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id S S) gAlg) =
      (AlgHom.compRight S S tau).comp eTarget.toAlgHom := by
    simpa only [eTarget, eSource, tau] using
      Algebra.liftFinSplitEq
        (Algebra.TensorProduct.map (AlgHom.id S S) gAlg)
        n m eTarget₀ eSource₀ tau₀ htau₀
  exact CategoryTheory.Limits.preservesColimit_parallelPair_of_split G
    ((FiniteEtale.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map f)
    ((FiniteEtale.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map g)
    (splitBase (.of S)) sigma tau
    (finiteEtalePullbackSplitIso Lsource eSource)
    (finiteEtalePullbackSplitIso Ltarget eTarget)
    (finiteEtalePullbackSplitIso_naturality Lsource Ltarget f
      fAlg hf eTarget eSource sigma hsigma)
    (finiteEtalePullbackSplitIso_naturality Lsource Ltarget g
      gAlg hg eTarget eSource tau htau)

end AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

variable {X : Scheme.{u}}

private instance finiteEtaleOverCategoryForLocalCoequalizers (Y : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ Y) :=
  FiniteEtale.instCategory Y

local instance finiteEtaleHasPullbacksAlongForCoequalizers
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  FiniteEtale.finiteEtaleHasPullbacksAlong f

private instance finiteEtaleBaseChangeAlongForCoequalizers
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hp ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hp⟩

/-- An object finite étale over a finite étale `X`-scheme is the same data as
an object over that scheme in `FiniteEtale X`. -/
private def overToBase (Z : FiniteEtale X) : Over Z ⥤ FiniteEtale Z.left where
  obj A := FiniteEtale.mk A.hom.left
  map {A B} f := MorphismProperty.Over.homMk f.left.left (by
    change f.left.left ≫ B.hom.left = A.hom.left
    exact congrArg (fun k => k.left) (CategoryTheory.Over.w f))
  map_id _ := rfl
  map_comp _ _ := rfl

private def overToBaseFullyFaithful (Z : FiniteEtale X) :
    (overToBase Z).FullyFaithful where
  preimage {A B} f := CategoryTheory.Over.homMk
    (MorphismProperty.Over.homMk f.left (by
      rw [← MorphismProperty.Over.w B.hom, ← MorphismProperty.Over.w A.hom]
      change (f.left ≫ B.hom.left) ≫ Z.hom = A.hom.left ≫ Z.hom
      have hf : f.left ≫ B.hom.left = A.hom.left := MorphismProperty.Over.w f
      exact congrArg (fun k => k ≫ Z.hom) hf))
    (by
      apply MorphismProperty.Over.Hom.ext
      change f.left ≫ B.hom.left = A.hom.left
      exact MorphismProperty.Over.w f)
  map_preimage _ := rfl
  preimage_map _ := rfl

private instance (Z : FiniteEtale X) : (overToBase Z).Full :=
  (overToBaseFullyFaithful Z).full

private instance (Z : FiniteEtale X) : (overToBase Z).Faithful :=
  (overToBaseFullyFaithful Z).faithful

private instance (Z : FiniteEtale X) : (overToBase Z).EssSurj where
  mem_essImage A := by
    let hcomp : IsFiniteEtale (A.hom ≫ Z.hom) :=
      MorphismProperty.comp_mem @IsFiniteEtale A.hom Z.hom A.prop Z.prop
    let AoverX : FiniteEtale X :=
      MorphismProperty.Over.mk ⊤ (A.hom ≫ Z.hom) hcomp
    let f : AoverX ⟶ Z := by
      dsimp only [AoverX, FiniteEtale.mk]
      exact MorphismProperty.Over.homMk A.hom (by rfl)
    let B : Over Z := CategoryTheory.Over.mk f
    refine ⟨B, ?_⟩
    refine ⟨?_⟩
    dsimp only [B, f, AoverX, overToBase, FiniteEtale.mk,
      MorphismProperty.Over.mk]
    exact MorphismProperty.Over.isoMk (Iso.refl A.left) (by rfl)

private instance (Z : FiniteEtale X) : (overToBase Z).IsEquivalence where

private noncomputable def localDiagram
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀) :
    WalkingParallelPair ⥤ FiniteEtale
      (Spec (.of (s.pt.left.affineOpenCover.X i : Type u))) :=
  CategoryTheory.Over.lift (parallelPair f g)
      (s.ι ≫ (Functor.const WalkingParallelPair).map (𝟙 s.pt)) ⋙
    overToBase s.pt ⋙
    FiniteEtale.pullback (s.pt.left.affineOpenCover.f i)

private noncomputable def localRingEquiv
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀) :=
  finiteEtaleRingEquiv
    (.of (s.pt.left.affineOpenCover.X i : Type u))

private noncomputable def localRingSource
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀) :=
  (localRingEquiv s i).functor.obj
    (Opposite.op ((localDiagram s i).obj WalkingParallelPair.zero))

private noncomputable def localRingTarget
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀) :=
  (localRingEquiv s i).functor.obj
    (Opposite.op ((localDiagram s i).obj WalkingParallelPair.one))

private noncomputable def localRingMapLeft
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀) :
    localRingTarget s i ⟶ localRingSource s i :=
  (localRingEquiv s i).functor.map
    ((localDiagram s i).map WalkingParallelPairHom.left).op

private noncomputable def localRingMapRight
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀) :
    localRingTarget s i ⟶ localRingSource s i :=
  (localRingEquiv s i).functor.map
    ((localDiagram s i).map WalkingParallelPairHom.right).op

private noncomputable def localUnderForget
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀) :=
  MorphismProperty.Under.forget
    (RingHom.toMorphismProperty @RingHom.FiniteEtale) ⊤
    (s.pt.left.affineOpenCover.X i)

private noncomputable def localAlgHomLeft
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀) :
    (localRingTarget s i).right →ₐ[s.pt.left.affineOpenCover.X i]
      (localRingSource s i).right :=
  CommRingCat.toAlgHom ((localUnderForget s i).map (localRingMapLeft s i))

private noncomputable def localAlgHomRight
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀) :
    (localRingTarget s i).right →ₐ[s.pt.left.affineOpenCover.X i]
      (localRingSource s i).right :=
  CommRingCat.toAlgHom ((localUnderForget s i).map (localRingMapRight s i))

private lemma localAlgHomLeft_toRingHom
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀) :
    ((localDiagram s i).map WalkingParallelPairHom.left).left.appTop.hom =
      (localAlgHomLeft s i).toRingHom := by
  rfl

private lemma localAlgHomRight_toRingHom
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀) :
    ((localDiagram s i).map WalkingParallelPairHom.right).left.appTop.hom =
      (localAlgHomRight s i).toRingHom := by
  rfl

/-- A split algebra presentation on an affine member of the target cover
makes every finite-coproduct-preserving realization preserve the
base-changed local coequalizer diagram. -/
private lemma preservesColimit_baseChanged_localDiagram_of_areSplit
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀)
    {S : Type u} [CommRing S]
    [Algebra (s.pt.left.affineOpenCover.X i) S]
    (hsplit : Algebra.AlgHom.AreSplit
      (Algebra.TensorProduct.map (AlgHom.id S S) (localAlgHomLeft s i))
      (Algebra.TensorProduct.map (AlgHom.id S S) (localAlgHomRight s i)))
    {C : Type (u + 1)} [Category.{u} C] [HasFiniteCoproducts C]
    (G : FiniteEtale (Spec (.of S)) ⥤ C)
    [PreservesFiniteCoproducts G] :
    PreservesColimit
      (parallelPair
        ((FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom
            (algebraMap (s.pt.left.affineOpenCover.X i) S)))).map
              ((localDiagram s i).map WalkingParallelPairHom.left))
        ((FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom
            (algebraMap (s.pt.left.affineOpenCover.X i) S)))).map
              ((localDiagram s i).map WalkingParallelPairHom.right))) G := by
  let Lsource := (localDiagram s i).obj WalkingParallelPair.zero
  let Ltarget := (localDiagram s i).obj WalkingParallelPair.one
  let : IsAffine Lsource.left :=
    @isAffine_of_isAffineHom Lsource.left
      (Spec (.of (s.pt.left.affineOpenCover.X i : Type u))) Lsource.hom
      (@IsFinite.toIsAffineHom _ _ Lsource.hom Lsource.prop.toIsFinite)
      (isAffine_Spec _)
  let : IsAffine Ltarget.left :=
    @isAffine_of_isAffineHom Ltarget.left
      (Spec (.of (s.pt.left.affineOpenCover.X i : Type u))) Ltarget.hom
      (@IsFinite.toIsAffineHom _ _ Ltarget.hom Ltarget.prop.toIsFinite)
      (isAffine_Spec _)
  exact preservesColimit_pullback_parallelPair_of_areSplit
    Lsource Ltarget
    ((localDiagram s i).map WalkingParallelPairHom.left)
    ((localDiagram s i).map WalkingParallelPairHom.right)
    (localAlgHomLeft s i) (localAlgHomRight s i)
    (localAlgHomLeft_toRingHom s i)
    (localAlgHomRight_toRingHom s i) hsplit G

private structure LocalSplitComponent
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀)
    (p : PrimeSpectrum (s.pt.left.affineOpenCover.X i)) where
  S : Type u
  [commRing : CommRing S]
  [algebra : Algebra (s.pt.left.affineOpenCover.X i) S]
  flat : Module.Flat (s.pt.left.affineOpenCover.X i) S
  openMap : IsOpenMap (PrimeSpectrum.comap
    (algebraMap (s.pt.left.affineOpenCover.X i) S))
  mem_range : p ∈ Set.range (PrimeSpectrum.comap
    (algebraMap (s.pt.left.affineOpenCover.X i) S))
  split : Algebra.AlgHom.AreSplit
    (Algebra.TensorProduct.map (.id S S) (localAlgHomLeft s i))
    (Algebra.TensorProduct.map (.id S S) (localAlgHomRight s i))

private theorem exists_localSplitComponent
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀)
    (p : PrimeSpectrum (s.pt.left.affineOpenCover.X i)) :
    Nonempty (LocalSplitComponent s i p) := by
  let R := s.pt.left.affineOpenCover.X i
  have hSource : RingHom.FiniteEtale (localRingSource s i).hom.hom :=
    (localRingSource s i).prop
  have hTarget : RingHom.FiniteEtale (localRingTarget s i).hom.hom :=
    (localRingTarget s i).prop
  let : Module.Finite R (localRingSource s i).right := hSource.toFinite
  let : Algebra.Etale R (localRingSource s i).right := hSource.toEtale
  let : Module.Finite R (localRingTarget s i).right := hTarget.toFinite
  let : Algebra.Etale R (localRingTarget s i).right := hTarget.toEtale
  obtain ⟨S, _, _, hflat, hopen, hmem, hsplit⟩ :=
    Algebra.AlgHom.exists_areSplit
      (localAlgHomLeft s i) (localAlgHomRight s i) p
  exact ⟨⟨S, hflat, hopen, hmem, hsplit⟩⟩

private noncomputable def localSplitComponent
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (i : s.pt.left.affineOpenCover.I₀)
    (p : PrimeSpectrum (s.pt.left.affineOpenCover.X i)) :
    LocalSplitComponent s i p :=
  Classical.choice (exists_localSplitComponent s i p)

private noncomputable def localSplitObj
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g)
    (j : Σ i : s.pt.left.affineOpenCover.I₀,
      PrimeSpectrum (s.pt.left.affineOpenCover.X i)) : Scheme := by
  letI := (localSplitComponent s j.1 j.2).commRing
  exact Spec (.of (localSplitComponent s j.1 j.2).S)

private noncomputable def localSplitMap
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g)
    (j : Σ i : s.pt.left.affineOpenCover.I₀,
      PrimeSpectrum (s.pt.left.affineOpenCover.X i)) :
    localSplitObj s j ⟶ s.pt.left := by
  letI := (localSplitComponent s j.1 j.2).commRing
  letI := (localSplitComponent s j.1 j.2).algebra
  exact Spec.map (CommRingCat.ofHom
    (algebraMap (s.pt.left.affineOpenCover.X j.1)
      (localSplitComponent s j.1 j.2).S)) ≫
    s.pt.left.affineOpenCover.f j.1

private theorem localSplitMap_flat_and_isOpenMap
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g)
    (j : Σ i : s.pt.left.affineOpenCover.I₀,
      PrimeSpectrum (s.pt.left.affineOpenCover.X i)) :
    Flat (localSplitMap s j) ∧ IsOpenMap (localSplitMap s j) := by
  let d := localSplitComponent s j.1 j.2
  let := d.commRing
  let := d.algebra
  constructor
  · dsimp only [localSplitMap, localSplitObj]
    exact MorphismProperty.comp_mem @Flat _ _
      (Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr d.flat))
      inferInstance
  · dsimp only [localSplitMap, localSplitObj]
    exact (s.pt.left.affineOpenCover.f j.1).isOpenEmbedding.isOpenMap.comp
      d.openMap

private theorem localSplitMap_jointly_surjective
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) :
    ∀ x : s.pt.left,
      ∃ (j : Σ i : s.pt.left.affineOpenCover.I₀,
          PrimeSpectrum (s.pt.left.affineOpenCover.X i))
        (y : localSplitObj s j), localSplitMap s j y = x := by
  intro x
  obtain ⟨p, hp⟩ := s.pt.left.affineOpenCover.covers x
  let i := s.pt.left.affineOpenCover.idx x
  let d := localSplitComponent s i p
  let := d.commRing
  let := d.algebra
  obtain ⟨q, hq⟩ := d.mem_range
  refine ⟨⟨i, p⟩, q, ?_⟩
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (s.pt.left.affineOpenCover.X i) d.S)) ≫
    s.pt.left.affineOpenCover.f i) q = x
  exact (congrArg (s.pt.left.affineOpenCover.f i) hq).trans hp

private theorem localSplitMap_mem_fpqcPrecoverage
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) :
    Presieve.ofArrows (localSplitObj s) (localSplitMap s) ∈
      Scheme.fpqcPrecoverage s.pt.left := by
  let I := Σ i : s.pt.left.affineOpenCover.I₀,
    PrimeSpectrum (s.pt.left.affineOpenCover.X i)
  let obj : I → Scheme.{u} := localSplitObj s
  let map : (j : I) → obj j ⟶ s.pt.left := localSplitMap s
  have hflat (j : I) : Flat (map j) :=
    (localSplitMap_flat_and_isOpenMap s j).1
  have hopen (j : I) : IsOpenMap (map j) :=
    (localSplitMap_flat_and_isOpenMap s j).2
  have hcovers : ∀ x : s.pt.left, ∃ j y, map j y = x :=
    localSplitMap_jointly_surjective s
  let P : MorphismProperty Scheme.{u} := @Flat
  let cov : s.pt.left.Cover (Scheme.precoverage P) :=
    Scheme.Cover.mkOfCovers (P := P) I obj map hcovers hflat
  change cov.presieve₀ ∈ Scheme.fpqcPrecoverage s.pt.left
  refine ⟨?_, cov.mem₀⟩
  rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact QuasiCompactCover.of_isOpenMap hopen

private def overToBaseMapCoforkIsColimit {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (hs : IsColimit s) :
    IsColimit ((overToBase s.pt).mapCocone
      (CategoryTheory.Over.liftCocone s (𝟙 s.pt))) :=
  isColimitOfPreserves (overToBase s.pt)
    (CategoryTheory.Over.isColimitLiftCocone s (𝟙 s.pt) hs)

/-- On an affine cover member, a split algebra presentation makes every
finite-coproduct-preserving realization of the base-changed local cofork a
colimit.  Taking the realization to be a further pullback followed by the
underlying-scheme functor supplies the overlap cases needed by fpqc descent. -/
private def baseChangedLocalCoforkMapIsColimit
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (hs : IsColimit s)
    (i : s.pt.left.affineOpenCover.I₀)
    {S : Type u} [CommRing S]
    [Algebra (s.pt.left.affineOpenCover.X i) S]
    (hsplit : Algebra.AlgHom.AreSplit
      (Algebra.TensorProduct.map (AlgHom.id S S) (localAlgHomLeft s i))
      (Algebra.TensorProduct.map (AlgHom.id S S) (localAlgHomRight s i)))
    {C : Type (u + 1)} [Category.{u} C] [HasFiniteCoproducts C]
    (G : FiniteEtale (Spec (.of S)) ⥤ C)
    [PreservesFiniteCoproducts G] :
    IsColimit
      (G.mapCocone
        ((FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom
            (algebraMap (s.pt.left.affineOpenCover.X i) S)))).mapCocone
          ((FiniteEtale.pullback
            (s.pt.left.affineOpenCover.f i)).mapCocone
            ((overToBase s.pt).mapCocone
              (CategoryTheory.Over.liftCocone s (𝟙 s.pt)))))) := by
  letI : PreservesColimit
      (parallelPair
        ((FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom
            (algebraMap (s.pt.left.affineOpenCover.X i) S)))).map
              ((localDiagram s i).map WalkingParallelPairHom.left))
        ((FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom
            (algebraMap (s.pt.left.affineOpenCover.X i) S)))).map
              ((localDiagram s i).map WalkingParallelPairHom.right)))
      G :=
    preservesColimit_baseChanged_localDiagram_of_areSplit s i hsplit
      G
  let K :=
    ((CategoryTheory.Over.lift (parallelPair f g)
        (s.ι ≫ (Functor.const WalkingParallelPair).map (𝟙 s.pt)) ⋙
      overToBase s.pt) ⋙
        FiniteEtale.pullback (s.pt.left.affineOpenCover.f i)) ⋙
      FiniteEtale.pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap (s.pt.left.affineOpenCover.X i) S)))
  have hKPair : PreservesColimit
      (parallelPair (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right))
      G := by
    change PreservesColimit
      (parallelPair
        ((FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom
            (algebraMap (s.pt.left.affineOpenCover.X i) S)))).map
              ((localDiagram s i).map WalkingParallelPairHom.left))
        ((FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom
            (algebraMap (s.pt.left.affineOpenCover.X i) S)))).map
              ((localDiagram s i).map WalkingParallelPairHom.right)))
      G
    infer_instance
  letI := hKPair
  letI : PreservesColimit K G :=
    preservesColimit_of_iso_diagram G
      (diagramIsoParallelPair K).symm
  let hpresK : PreservesColimit
      (((CategoryTheory.Over.lift (parallelPair f g)
          (s.ι ≫ (Functor.const WalkingParallelPair).map (𝟙 s.pt)) ⋙
        overToBase s.pt) ⋙
          FiniteEtale.pullback (s.pt.left.affineOpenCover.f i)) ⋙
        FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom
            (algebraMap (s.pt.left.affineOpenCover.X i) S)))) G := by
    change PreservesColimit K G
    infer_instance
  have hlocal : IsColimit
      ((FiniteEtale.pullback
        (s.pt.left.affineOpenCover.f i)).mapCocone
        ((overToBase s.pt).mapCocone
          (CategoryTheory.Over.liftCocone s (𝟙 s.pt)))) :=
    isColimitOfPreserves
      (FiniteEtale.pullback (s.pt.left.affineOpenCover.f i))
      (overToBaseMapCoforkIsColimit s hs)
  have hbaseChange : IsColimit
      ((FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom
          (algebraMap (s.pt.left.affineOpenCover.X i) S)))).mapCocone
        ((FiniteEtale.pullback
          (s.pt.left.affineOpenCover.f i)).mapCocone
          ((overToBase s.pt).mapCocone
            (CategoryTheory.Over.liftCocone s (𝟙 s.pt))))) :=
    isColimitOfPreserves _ hlocal
  exact (hpresK.preserves hbaseChange).some

/-- The split local model remains a Scheme-valued coequalizer after an
arbitrary further base change.  The conclusion is written using the single
pullback along the composite map, as required by fpqc-local descent. -/
private def localSplitCoforkForgetAfterPullbackIsColimit
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (hs : IsColimit s)
    (i : s.pt.left.affineOpenCover.I₀)
    {S : Type u} [CommRing S]
    [Algebra (s.pt.left.affineOpenCover.X i) S]
    (hsplit : Algebra.AlgHom.AreSplit
      (Algebra.TensorProduct.map (AlgHom.id S S) (localAlgHomLeft s i))
      (Algebra.TensorProduct.map (AlgHom.id S S) (localAlgHomRight s i)))
    {U : Scheme.{u}} (q : U ⟶ Spec (.of S)) :
    IsColimit
      ((FiniteEtale.pullback
          (q ≫ (Spec.map (CommRingCat.ofHom
              (algebraMap (s.pt.left.affineOpenCover.X i) S))) ≫
            s.pt.left.affineOpenCover.f i) ⋙
        forgetToUnderlyingScheme U).mapCocone
        ((overToBase s.pt).mapCocone
          (CategoryTheory.Over.liftCocone s (𝟙 s.pt)))) := by
  let pS : Spec (.of S) ⟶
      Spec (.of (s.pt.left.affineOpenCover.X i : Type u)) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (s.pt.left.affineOpenCover.X i) S))
  let a : Spec (.of (s.pt.left.affineOpenCover.X i : Type u)) ⟶
      s.pt.left := s.pt.left.affineOpenCover.f i
  let H : FiniteEtale U ⥤ Scheme.{u} := forgetToUnderlyingScheme U
  let G : FiniteEtale (Spec (.of S)) ⥤ Scheme.{u} :=
    FiniteEtale.pullback q ⋙ H
  letI : PreservesFiniteCoproducts G := by
    dsimp only [G, H]
    infer_instance
  have hiter := baseChangedLocalCoforkMapIsColimit
    s hs i hsplit G
  have hinnerComposite : IsColimit
      ((FiniteEtale.pullback pS ⋙ G).mapCocone
        ((FiniteEtale.pullback a).mapCocone
          ((overToBase s.pt).mapCocone
            (CategoryTheory.Over.liftCocone s (𝟙 s.pt))))) :=
    hiter.ofIsoColimit
      (Functor.mapCoconeMapCocone
        ((FiniteEtale.pullback a).mapCocone
          ((overToBase s.pt).mapCocone
            (CategoryTheory.Over.liftCocone s (𝟙 s.pt)))))
  let einner :
      FiniteEtale.pullback (q ≫ pS) ⋙ H ≅
        FiniteEtale.pullback pS ⋙ G :=
    Functor.isoWhiskerRight
        (MorphismProperty.Over.pullbackComp
          (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) q pS) H ≪≫
      Functor.associator _ _ _
  have hinnerDirect : IsColimit
      ((FiniteEtale.pullback (q ≫ pS) ⋙ H).mapCocone
        ((FiniteEtale.pullback a).mapCocone
          ((overToBase s.pt).mapCocone
            (CategoryTheory.Over.liftCocone s (𝟙 s.pt))))) :=
    IsColimit.mapCoconeEquiv einner.symm hinnerComposite
  have houterComposite : IsColimit
      ((FiniteEtale.pullback a ⋙
        (FiniteEtale.pullback (q ≫ pS) ⋙ H)).mapCocone
          ((overToBase s.pt).mapCocone
            (CategoryTheory.Over.liftCocone s (𝟙 s.pt)))) :=
    hinnerDirect.ofIsoColimit
      (Functor.mapCoconeMapCocone
        ((overToBase s.pt).mapCocone
          (CategoryTheory.Over.liftCocone s (𝟙 s.pt))))
  let eouter :
      FiniteEtale.pullback (q ≫ (pS ≫ a)) ⋙ H ≅
        FiniteEtale.pullback a ⋙
          (FiniteEtale.pullback (q ≫ pS) ⋙ H) :=
    Functor.isoWhiskerRight
        (MorphismProperty.Over.pullbackComp
          (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) (q ≫ pS) a
          (fg := q ≫ (pS ≫ a)) (by simp)) H ≪≫
      Functor.associator _ _ _
  have hdirectComposite : IsColimit
      ((FiniteEtale.pullback (q ≫ (pS ≫ a)) ⋙ H).mapCocone
        ((overToBase s.pt).mapCocone
          (CategoryTheory.Over.liftCocone s (𝟙 s.pt)))) :=
    IsColimit.mapCoconeEquiv eouter.symm houterComposite
  simpa only [pS, a, H] using hdirectComposite


end AlgebraicGeometry.FiniteEtale

namespace AlgebraicGeometry

private lemma pullback_congrHom_map_naturality
    {W Y T S : Scheme.{u}} {a a' : W ⟶ S} {b b' : Y ⟶ S}
    (p : T ⟶ S) (i : W ⟶ Y) (ha : a = a') (hb : b = b')
    (e : a ≫ 𝟙 S = i ≫ b) (e' : a' ≫ 𝟙 S = i ≫ b') :
    (pullback.congrHom ha rfl).hom ≫
        pullback.map a' p b' p i (𝟙 T) (𝟙 S) e'
          (by simp) =
      pullback.map a p b p i (𝟙 T) (𝟙 S) e
          (by simp) ≫
        (pullback.congrHom hb rfl).hom := by
  simp only [pullback.congrHom, asIso_hom]
  rw [pullback.map_comp, pullback.map_comp]
  simp

private lemma pullback_congrHom_map_naturality_inv
    {W Y T S : Scheme.{u}} {a a' : W ⟶ S} {b b' : Y ⟶ S}
    (p : T ⟶ S) (i : W ⟶ Y) (ha : a = a') (hb : b = b')
    (e : a ≫ 𝟙 S = i ≫ b) (e' : a' ≫ 𝟙 S = i ≫ b') :
    (pullback.congrHom ha rfl).inv ≫
        pullback.map a p b p i (𝟙 T) (𝟙 S) e
          (by simp) =
      pullback.map a' p b' p i (𝟙 T) (𝟙 S) e'
          (by simp) ≫
        (pullback.congrHom hb rfl).inv := by
  simp only [pullback.congrHom_inv]
  rw [pullback.map_comp, pullback.map_comp]
  simp

private lemma pullback_congrHom_map_naturality_right_rfl
    {W Y T S : Scheme.{u}} {a a' : W ⟶ S} {b : Y ⟶ S}
    (p : T ⟶ S) (i : W ⟶ Y) (ha : a = a')
    (e : a ≫ 𝟙 S = i ≫ b) (e' : a' ≫ 𝟙 S = i ≫ b) :
    (pullback.congrHom ha rfl).hom ≫
        pullback.map a' p b p i (𝟙 T) (𝟙 S) e'
          (by simp) =
      pullback.map a p b p i (𝟙 T) (𝟙 S) e
          (by simp) := by
  simpa [pullback.congrHom] using
    pullback_congrHom_map_naturality p i ha (rfl : b = b) e e'

variable {A B Z U : Scheme.{u}} {a b : A ⟶ B} {c : B ⟶ Z}
  (hc : a ≫ c = b ≫ c) (p : U ⟶ Z)

private def forwardLeft : pullback p (a ≫ c) ⟶ pullback p c :=
  pullback.lift (pullback.fst p (a ≫ c)) (pullback.snd p (a ≫ c) ≫ a)
    (by simpa only [Category.assoc] using
      (pullback.condition : pullback.fst p (a ≫ c) ≫ p =
        pullback.snd p (a ≫ c) ≫ (a ≫ c)))

private def forwardRight : pullback p (a ≫ c) ⟶ pullback p c :=
  pullback.lift (pullback.fst p (a ≫ c)) (pullback.snd p (a ≫ c) ≫ b)
    (by simpa only [Category.assoc, ← hc] using
      (pullback.condition : pullback.fst p (a ≫ c) ≫ p =
        pullback.snd p (a ≫ c) ≫ (a ≫ c)))

private def forwardPi : pullback p c ⟶ U := pullback.fst p c

private def forwardCofork : Cofork (forwardLeft p) (forwardRight hc p) :=
  Cofork.ofπ (forwardPi p) (by
    simp only [forwardLeft, forwardRight, forwardPi, pullback.lift_fst])

private def reverseLeft : pullback (a ≫ c) p ⟶ pullback c p :=
  pullback.lift (pullback.fst (a ≫ c) p ≫ a) (pullback.snd (a ≫ c) p)
    (by simpa only [Category.assoc] using
      (pullback.condition : pullback.fst (a ≫ c) p ≫ (a ≫ c) =
        pullback.snd (a ≫ c) p ≫ p))

private def reverseRight : pullback (a ≫ c) p ⟶ pullback c p :=
  pullback.lift (pullback.fst (a ≫ c) p ≫ b) (pullback.snd (a ≫ c) p)
    (by simpa only [Category.assoc, ← hc] using
      (pullback.condition : pullback.fst (a ≫ c) p ≫ (a ≫ c) =
        pullback.snd (a ≫ c) p ≫ p))

private def reversePi : pullback c p ⟶ pullback (𝟙 Z) p :=
  pullback.lift (pullback.fst c p ≫ c) (pullback.snd c p)
    (by simpa only [Category.assoc, Category.comp_id] using
      (pullback.condition : pullback.fst c p ≫ c = pullback.snd c p ≫ p))

private def reverseCofork : Cofork (reverseLeft p) (reverseRight hc p) :=
  Cofork.ofπ (reversePi p) (by
    apply pullback.hom_ext
    · dsimp only [reverseLeft, reverseRight, reversePi]
      simp_rw [Category.assoc]
      simp_rw [pullback.lift_fst]
      simp_rw [← Category.assoc]
      simp_rw [pullback.lift_fst]
      exact congrArg (fun k => pullback.fst (a ≫ c) p ≫ k) hc
    · dsimp only [reverseLeft, reverseRight, reversePi]
      simp_rw [Category.assoc]
      simp_rw [pullback.lift_snd])

private def reversePointIso : pullback (𝟙 Z) p ≅ U :=
  asIso (pullback.snd (𝟙 Z) p)

private def reverseForwardIsColimitEquiv :
    IsColimit (reverseCofork hc p) ≃ IsColimit (forwardCofork hc p) :=
  Cofork.isColimitEquivOfIsos
    (reverseCofork hc p) (forwardCofork hc p)
    (pullbackSymmetry (a ≫ c) p)
    (pullbackSymmetry c p)
    (reversePointIso p)
    (by
      apply pullback.hom_ext
      · calc
          ((pullbackSymmetry (a ≫ c) p).hom ≫ forwardLeft p) ≫
                pullback.fst p c =
              (pullbackSymmetry (a ≫ c) p).hom ≫
                pullback.fst p (a ≫ c) := by
                  rw [Category.assoc, forwardLeft, pullback.lift_fst]
          _ = pullback.snd (a ≫ c) p := pullbackSymmetry_hom_comp_fst _ _
          _ = reverseLeft p ≫ pullback.snd c p := by
                rw [reverseLeft, pullback.lift_snd]
          _ = reverseLeft p ≫
              ((pullbackSymmetry c p).hom ≫ pullback.fst p c) := by
                rw [pullbackSymmetry_hom_comp_fst]
          _ = (reverseLeft p ≫ (pullbackSymmetry c p).hom) ≫
                pullback.fst p c := by rw [Category.assoc]
      · calc
          ((pullbackSymmetry (a ≫ c) p).hom ≫ forwardLeft p) ≫
                pullback.snd p c =
              (pullbackSymmetry (a ≫ c) p).hom ≫
                (pullback.snd p (a ≫ c) ≫ a) := by
                  rw [Category.assoc, forwardLeft, pullback.lift_snd]
          _ = ((pullbackSymmetry (a ≫ c) p).hom ≫
                pullback.snd p (a ≫ c)) ≫ a := by rw [Category.assoc]
          _ = pullback.fst (a ≫ c) p ≫ a := by
                rw [pullbackSymmetry_hom_comp_snd]
          _ = reverseLeft p ≫ pullback.fst c p := by
                rw [reverseLeft, pullback.lift_fst]
          _ = reverseLeft p ≫
              ((pullbackSymmetry c p).hom ≫ pullback.snd p c) := by
                rw [pullbackSymmetry_hom_comp_snd]
          _ = (reverseLeft p ≫ (pullbackSymmetry c p).hom) ≫
                pullback.snd p c := by rw [Category.assoc])
    (by
      apply pullback.hom_ext
      · calc
          ((pullbackSymmetry (a ≫ c) p).hom ≫ forwardRight hc p) ≫
                pullback.fst p c =
              (pullbackSymmetry (a ≫ c) p).hom ≫
                pullback.fst p (a ≫ c) := by
                  rw [Category.assoc, forwardRight, pullback.lift_fst]
          _ = pullback.snd (a ≫ c) p := pullbackSymmetry_hom_comp_fst _ _
          _ = reverseRight hc p ≫ pullback.snd c p := by
                rw [reverseRight, pullback.lift_snd]
          _ = reverseRight hc p ≫
              ((pullbackSymmetry c p).hom ≫ pullback.fst p c) := by
                rw [pullbackSymmetry_hom_comp_fst]
          _ = (reverseRight hc p ≫ (pullbackSymmetry c p).hom) ≫
                pullback.fst p c := by rw [Category.assoc]
      · calc
          ((pullbackSymmetry (a ≫ c) p).hom ≫ forwardRight hc p) ≫
                pullback.snd p c =
              (pullbackSymmetry (a ≫ c) p).hom ≫
                (pullback.snd p (a ≫ c) ≫ b) := by
                  rw [Category.assoc, forwardRight, pullback.lift_snd]
          _ = ((pullbackSymmetry (a ≫ c) p).hom ≫
                pullback.snd p (a ≫ c)) ≫ b := by rw [Category.assoc]
          _ = pullback.fst (a ≫ c) p ≫ b := by
                rw [pullbackSymmetry_hom_comp_snd]
          _ = reverseRight hc p ≫ pullback.fst c p := by
                rw [reverseRight, pullback.lift_fst]
          _ = reverseRight hc p ≫
              ((pullbackSymmetry c p).hom ≫ pullback.snd p c) := by
                rw [pullbackSymmetry_hom_comp_snd]
          _ = (reverseRight hc p ≫ (pullbackSymmetry c p).hom) ≫
                pullback.snd p c := by rw [Category.assoc])
    (by
      change (pullbackSymmetry c p).inv ≫ reversePi p ≫
        pullback.snd (𝟙 Z) p = pullback.fst p c
      dsimp only [reversePi]
      rw [pullback.lift_snd, pullbackSymmetry_inv_comp_snd])

/-- The maps in the literal statement of 0BMN (written with `pullback.map`). -/
private def zeroBMNLeft : pullback p (a ≫ c) ⟶ pullback p c :=
  pullback.map p (a ≫ c) p c (𝟙 U) a (𝟙 Z) (by simp) (by simp)

private def zeroBMNRight : pullback p (a ≫ c) ⟶ pullback p c :=
  pullback.map p (a ≫ c) p c (𝟙 U) b (𝟙 Z) (by simp) (by simp [hc])

private lemma forwardLeft_eq_zeroBMNLeft :
    forwardLeft (a := a) (c := c) p = zeroBMNLeft (a := a) (c := c) p := by
  apply pullback.hom_ext <;> simp [forwardLeft, zeroBMNLeft, pullback.map]

private lemma forwardRight_eq_zeroBMNRight :
    forwardRight hc p = zeroBMNRight hc p := by
  apply pullback.hom_ext <;> simp [forwardRight, zeroBMNRight, pullback.map]

private def zeroBMNCofork : Cofork (zeroBMNLeft p) (zeroBMNRight hc p) :=
  Cofork.ofπ (pullback.fst p c) (by
    rw [← forwardLeft_eq_zeroBMNLeft (a := a) (c := c) p,
      ← forwardRight_eq_zeroBMNRight hc p]
    exact (forwardCofork hc p).condition)

/-- Transport from the convenient lift presentation to the exact 0BMN cofork. -/
private def forwardZeroBMNIsColimitEquiv :
    IsColimit (forwardCofork hc p) ≃ IsColimit (zeroBMNCofork hc p) :=
  Cofork.isColimitEquivOfIsos
    (forwardCofork hc p) (zeroBMNCofork hc p)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using (forwardLeft_eq_zeroBMNLeft (a := a) (c := c) p).symm)
    (by simpa using (forwardRight_eq_zeroBMNRight hc p).symm)
    (by
      change pullback.fst p c ≫ 𝟙 U = pullback.fst p c
      simp only [Category.comp_id])

end AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale.PullbackCoforkTransport

variable {X : Scheme.{u}} {A B : FiniteEtale X} {f g : A ⟶ B}

private def pointSource (s : Cofork f g) : FiniteEtale s.pt.left :=
  FiniteEtale.mk (f ≫ s.π).left

private def pointMiddle (s : Cofork f g) : FiniteEtale s.pt.left :=
  FiniteEtale.mk s.π.left

private def pointTarget (s : Cofork f g) : FiniteEtale s.pt.left :=
  MorphismProperty.Over.mk ⊤ (𝟙 s.pt.left)
    (MorphismProperty.id_mem _ _)

private def pointLeft (s : Cofork f g) : pointSource s ⟶ pointMiddle s :=
  MorphismProperty.Over.homMk f.left

private def pointRight (s : Cofork f g) : pointSource s ⟶ pointMiddle s :=
  MorphismProperty.Over.homMk g.left
    (congrArg (fun k ↦ k.left) s.condition.symm)

private def pointPi (s : Cofork f g) : pointMiddle s ⟶ pointTarget s :=
  MorphismProperty.Over.homMk s.π.left

private def pointCofork (s : Cofork f g) : Cofork (pointLeft s) (pointRight s) :=
  Cofork.ofπ (pointPi s) (by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun k ↦ k.left) s.condition)

variable {U : Scheme.{u}}

private noncomputable def nestedDiagram
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    WalkingParallelPair ⥤ Scheme.{u} :=
  ((CategoryTheory.Over.lift (parallelPair f g)
      (s.ι ≫ (Functor.const WalkingParallelPair).map (𝟙 s.pt)) ⋙
    overToBase s.pt) ⋙ FiniteEtale.pullback p) ⋙
      forgetToUnderlyingScheme U

/-- This is the nested production cocone
`(pullback p ⋙ forgetToUnderlyingScheme).mapCocone
  ((overToBase _).mapCocone (Over.liftCocone _ _))`. -/
private noncomputable def nestedUnderlyingCofork
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    Cocone (nestedDiagram s p) :=
  (FiniteEtale.pullback p ⋙ forgetToUnderlyingScheme U).mapCocone
    ((overToBase s.pt).mapCocone
      (CategoryTheory.Over.liftCocone s (𝟙 s.pt)))

private def pullbackCofork (s : Cofork f g) (p : U ⟶ s.pt.left) :
    Cofork ((FiniteEtale.pullback p).map (pointLeft s))
      ((FiniteEtale.pullback p).map (pointRight s)) :=
  Cofork.ofπ ((FiniteEtale.pullback p).map (pointPi s)) (by
    simp only [← Functor.map_comp]
    exact congrArg (fun k ↦ (FiniteEtale.pullback p).map k)
      (pointCofork s).condition)

/-- The literal Scheme cofork obtained by applying
`FiniteEtale.forget _ ⋙ Over.forget _` to `pullbackCofork`. -/
private def underlyingPullbackCofork (s : Cofork f g) (p : U ⟶ s.pt.left) :
    Cofork (((FiniteEtale.pullback p).map (pointLeft s)).left)
      (((FiniteEtale.pullback p).map (pointRight s)).left) :=
  Cofork.ofπ (((FiniteEtale.pullback p).map (pointPi s)).left)
    (congrArg (fun k ↦ k.left) (pullbackCofork s p).condition)

private noncomputable def normalizedNestedCofork
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    Cofork
      ((nestedDiagram s p).map WalkingParallelPairHom.left)
      ((nestedDiagram s p).map WalkingParallelPairHom.right) :=
  (Cocone.precompose (diagramIsoParallelPair (nestedDiagram s p)).inv).obj
    (nestedUnderlyingCofork s p)

private lemma nestedSourceHom_eq
    (s : Cofork f g) :
    (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left =
      (f ≫ s.π).left := by
  rw [s.app_zero_eq_comp_π_left]
  exact congrArg (fun k ↦ k.left) (Category.comp_id (f ≫ s.π))

private lemma nestedMiddleHom_eq
    (s : Cofork f g) :
    (s.ι.app WalkingParallelPair.one ≫ 𝟙 s.pt).left =
      s.π.left := by
  rw [s.app_one_eq_π]
  exact congrArg (fun k ↦ k.left) (Category.comp_id s.π)

private lemma nested_zero_eq
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    (nestedDiagram s p).obj WalkingParallelPair.zero =
      ((FiniteEtale.pullback p).obj (pointSource s)).left := by
  change Limits.pullback (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left p =
    Limits.pullback (f ≫ s.π).left p
  exact congrArg (fun k ↦ Limits.pullback k p) (nestedSourceHom_eq s)

private lemma nested_one_eq
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    (nestedDiagram s p).obj WalkingParallelPair.one =
      ((FiniteEtale.pullback p).obj (pointMiddle s)).left := by
  change Limits.pullback (s.ι.app WalkingParallelPair.one ≫ 𝟙 s.pt).left p =
    Limits.pullback s.π.left p
  exact congrArg (fun k ↦ Limits.pullback k p) (nestedMiddleHom_eq s)

private lemma nested_point_eq
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    (normalizedNestedCofork s p).pt =
      (underlyingPullbackCofork s p).pt := by
  rfl

private lemma nested_pi_eq
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    (normalizedNestedCofork s p).π =
      (underlyingPullbackCofork s p).π := by
  rfl

private noncomputable def nestedSourceIso
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    (nestedDiagram s p).obj WalkingParallelPair.zero ≅
      ((FiniteEtale.pullback p).obj (pointSource s)).left :=
  Limits.pullback.congrHom (nestedSourceHom_eq s) rfl

private noncomputable def nestedMiddleIso
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    (nestedDiagram s p).obj WalkingParallelPair.one ≅
      ((FiniteEtale.pullback p).obj (pointMiddle s)).left :=
  Limits.pullback.congrHom (nestedMiddleHom_eq s) rfl

private noncomputable def nestedPointIso
    (s : Cofork f g) (p : U ⟶ s.pt.left) :=
  Iso.refl (normalizedNestedCofork s p).pt

private lemma pullbackLeft_left (s : Cofork f g) (p : U ⟶ s.pt.left) :
    ((FiniteEtale.pullback p).map (pointLeft s)).left =
      Limits.pullback.lift
        (Limits.pullback.fst ((f ≫ s.π).left) p ≫ f.left)
        (Limits.pullback.snd ((f ≫ s.π).left) p)
        (by
          change (Limits.pullback.fst ((f ≫ s.π).left) p ≫ f.left) ≫
              s.π.left = Limits.pullback.snd ((f ≫ s.π).left) p ≫ p
          calc
            _ = Limits.pullback.fst ((f ≫ s.π).left) p ≫
                (f.left ≫ s.π.left) := Category.assoc _ _ _
            _ = Limits.pullback.fst ((f ≫ s.π).left) p ≫
                (f ≫ s.π).left := rfl
            _ = Limits.pullback.snd ((f ≫ s.π).left) p ≫ p :=
              Limits.pullback.condition) := by
  rfl

private lemma pullbackRight_left (s : Cofork f g) (p : U ⟶ s.pt.left) :
    ((FiniteEtale.pullback p).map (pointRight s)).left =
      Limits.pullback.lift
        (Limits.pullback.fst ((f ≫ s.π).left) p ≫ g.left)
        (Limits.pullback.snd ((f ≫ s.π).left) p)
        (by
          change (Limits.pullback.fst ((f ≫ s.π).left) p ≫ g.left) ≫
              s.π.left = Limits.pullback.snd ((f ≫ s.π).left) p ≫ p
          let h : f.left ≫ s.π.left = g.left ≫ s.π.left :=
            congrArg (fun k ↦ k.left) s.condition
          calc
            _ = Limits.pullback.fst ((f ≫ s.π).left) p ≫
                (g.left ≫ s.π.left) := Category.assoc _ _ _
            _ = Limits.pullback.fst ((f ≫ s.π).left) p ≫
                (f.left ≫ s.π.left) :=
              congrArg
                (fun k ↦ Limits.pullback.fst ((f ≫ s.π).left) p ≫ k)
                h.symm
            _ = Limits.pullback.fst ((f ≫ s.π).left) p ≫
                (f ≫ s.π).left := rfl
            _ = Limits.pullback.snd ((f ≫ s.π).left) p ≫ p :=
              Limits.pullback.condition) := by
  rfl

private lemma pullbackPi_left (s : Cofork f g) (p : U ⟶ s.pt.left) :
    ((FiniteEtale.pullback p).map (pointPi s)).left =
      Limits.pullback.lift
        (Limits.pullback.fst s.π.left p ≫ s.π.left)
        (Limits.pullback.snd s.π.left p)
        (by
          change (Limits.pullback.fst s.π.left p ≫ s.π.left) ≫
              𝟙 s.pt.left = Limits.pullback.snd s.π.left p ≫ p
          simpa only [Category.comp_id] using
            (Limits.pullback.condition :
              Limits.pullback.fst s.π.left p ≫ s.π.left =
                Limits.pullback.snd s.π.left p ≫ p)) := by
  rfl

private lemma nestedLeft_left (s : Cofork f g)
    (p : U ⟶ s.pt.left) :
    (nestedDiagram s p).map WalkingParallelPairHom.left =
      Limits.pullback.lift
        (Limits.pullback.fst
          (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left p ≫ f.left)
        (Limits.pullback.snd
          (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left p)
        (by
          change (Limits.pullback.fst
              (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left p ≫
                f.left) ≫
              (s.ι.app WalkingParallelPair.one ≫ 𝟙 s.pt).left =
            Limits.pullback.snd
              (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left p ≫ p
          rw [nestedSourceHom_eq, nestedMiddleHom_eq]
          calc
            _ = Limits.pullback.fst (f ≫ s.π).left p ≫
                (f.left ≫ s.π.left) := Category.assoc _ _ _
            _ = Limits.pullback.fst (f ≫ s.π).left p ≫
                (f ≫ s.π).left := rfl
            _ = Limits.pullback.snd (f ≫ s.π).left p ≫ p :=
              Limits.pullback.condition) := by
  rfl

private lemma nestedRight_left (s : Cofork f g)
    (p : U ⟶ s.pt.left) :
    (nestedDiagram s p).map WalkingParallelPairHom.right =
      Limits.pullback.lift
        (Limits.pullback.fst
          (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left p ≫ g.left)
        (Limits.pullback.snd
          (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left p)
        (by
          change (Limits.pullback.fst
              (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left p ≫
                g.left) ≫
              (s.ι.app WalkingParallelPair.one ≫ 𝟙 s.pt).left =
            Limits.pullback.snd
              (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left p ≫ p
          rw [nestedSourceHom_eq, nestedMiddleHom_eq]
          have hfg : f.left ≫ s.π.left = g.left ≫ s.π.left :=
            congrArg (fun k ↦ k.left) s.condition
          calc
            _ = Limits.pullback.fst (f ≫ s.π).left p ≫
                (g.left ≫ s.π.left) := Category.assoc _ _ _
            _ = Limits.pullback.fst (f ≫ s.π).left p ≫
                (f.left ≫ s.π.left) :=
              congrArg
                (fun k ↦ Limits.pullback.fst (f ≫ s.π).left p ≫ k)
                hfg.symm
            _ = Limits.pullback.fst (f ≫ s.π).left p ≫
                (f ≫ s.π).left := rfl
            _ = Limits.pullback.snd (f ≫ s.π).left p ≫ p :=
              Limits.pullback.condition) := by
  rfl

private def normalizedUnderlyingIsColimitEquiv
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    IsColimit (normalizedNestedCofork s p) ≃
      IsColimit (underlyingPullbackCofork s p) :=
  Cofork.isColimitEquivOfIsos
    (normalizedNestedCofork s p) (underlyingPullbackCofork s p)
    (nestedSourceIso s p) (nestedMiddleIso s p) (nestedPointIso s p)
    (by
      let eOld :
          (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left ≫
              𝟙 s.pt.left =
            f.left ≫ (s.ι.app WalkingParallelPair.one ≫ 𝟙 s.pt).left := by
        calc
          _ = (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left :=
            Category.comp_id _
          _ = (f ≫ s.π).left := nestedSourceHom_eq s
          _ = f.left ≫ s.π.left := rfl
          _ = f.left ≫ (s.ι.app WalkingParallelPair.one ≫ 𝟙 s.pt).left :=
            congrArg (fun k ↦ f.left ≫ k) (nestedMiddleHom_eq s).symm
      let eNew : (f ≫ s.π).left ≫ 𝟙 s.pt.left =
          f.left ≫ s.π.left := by
        calc
          _ = (f ≫ s.π).left := Category.comp_id _
          _ = f.left ≫ s.π.left := rfl
      change (pullback.congrHom (nestedSourceHom_eq s) rfl).hom ≫
            pullback.map (f ≫ s.π).left p s.π.left p f.left
              (𝟙 U) (𝟙 s.pt.left) eNew (by simp) =
          pullback.map
              (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left p
              (s.ι.app WalkingParallelPair.one ≫ 𝟙 s.pt).left p
              f.left (𝟙 U) (𝟙 s.pt.left) eOld (by simp) ≫
            (pullback.congrHom (nestedMiddleHom_eq s) rfl).hom
      exact pullback_congrHom_map_naturality p f.left
        (nestedSourceHom_eq s) (nestedMiddleHom_eq s) eOld eNew)
    (by
      let eOld :
          (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left ≫
              𝟙 s.pt.left =
            g.left ≫ (s.ι.app WalkingParallelPair.one ≫ 𝟙 s.pt).left := by
        calc
          _ = (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left :=
            Category.comp_id _
          _ = (f ≫ s.π).left := nestedSourceHom_eq s
          _ = f.left ≫ s.π.left := rfl
          _ = g.left ≫ s.π.left :=
            congrArg (fun k ↦ k.left) s.condition
          _ = g.left ≫ (s.ι.app WalkingParallelPair.one ≫ 𝟙 s.pt).left :=
            congrArg (fun k ↦ g.left ≫ k) (nestedMiddleHom_eq s).symm
      let eNew : (f ≫ s.π).left ≫ 𝟙 s.pt.left =
          g.left ≫ s.π.left := by
        calc
          _ = (f ≫ s.π).left := Category.comp_id _
          _ = f.left ≫ s.π.left := rfl
          _ = g.left ≫ s.π.left :=
            congrArg (fun k ↦ k.left) s.condition
      change (pullback.congrHom (nestedSourceHom_eq s) rfl).hom ≫
            pullback.map (f ≫ s.π).left p s.π.left p g.left
              (𝟙 U) (𝟙 s.pt.left) eNew (by simp) =
          pullback.map
              (s.ι.app WalkingParallelPair.zero ≫ 𝟙 s.pt).left p
              (s.ι.app WalkingParallelPair.one ≫ 𝟙 s.pt).left p
              g.left (𝟙 U) (𝟙 s.pt.left) eOld (by simp) ≫
            (pullback.congrHom (nestedMiddleHom_eq s) rfl).hom
      exact pullback_congrHom_map_naturality p g.left
        (nestedSourceHom_eq s) (nestedMiddleHom_eq s) eOld eNew)
    (by
      apply (cancel_epi (nestedMiddleIso s p).hom).1
      simp only [Iso.hom_inv_id_assoc, nestedPointIso, Iso.refl_hom]
      let eOld :
          (s.ι.app WalkingParallelPair.one ≫ 𝟙 s.pt).left ≫
              𝟙 s.pt.left =
            s.π.left ≫ 𝟙 s.pt.left := by
        calc
          _ = (s.ι.app WalkingParallelPair.one ≫ 𝟙 s.pt).left :=
            Category.comp_id _
          _ = s.π.left := nestedMiddleHom_eq s
          _ = s.π.left ≫ 𝟙 s.pt.left := (Category.comp_id _).symm
      let eNew : s.π.left ≫ 𝟙 s.pt.left =
          s.π.left ≫ 𝟙 s.pt.left := rfl
      change pullback.map
              (s.ι.app WalkingParallelPair.one ≫ 𝟙 s.pt).left p
              (𝟙 s.pt.left) p s.π.left (𝟙 U) (𝟙 s.pt.left)
              eOld (by simp) =
          (pullback.congrHom (nestedMiddleHom_eq s) rfl).hom ≫
            pullback.map s.π.left p (𝟙 s.pt.left) p s.π.left
              (𝟙 U) (𝟙 s.pt.left) eNew (by simp)
      exact (pullback_congrHom_map_naturality_right_rfl p s.π.left
        (nestedMiddleHom_eq s) eOld eNew).symm)

private def nestedUnderlyingIsColimitEquiv
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    IsColimit (nestedUnderlyingCofork s p) ≃
      IsColimit (underlyingPullbackCofork s p) :=
  ((IsColimit.precomposeInvEquiv
    (diagramIsoParallelPair (nestedDiagram s p))
    (nestedUnderlyingCofork s p)).symm).trans
      (normalizedUnderlyingIsColimitEquiv s p)

private lemma underlying_left_eq_reverseLeft
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    ((FiniteEtale.pullback p).map (pointLeft s)).left =
      AlgebraicGeometry.reverseLeft p := by
  exact pullbackLeft_left s p

private lemma underlying_right_eq_reverseRight
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    ((FiniteEtale.pullback p).map (pointRight s)).left =
      AlgebraicGeometry.reverseRight
        (congrArg (fun k ↦ k.left) s.condition) p := by
  exact pullbackRight_left s p

private lemma underlying_pi_eq_reversePi
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    (underlyingPullbackCofork s p).π =
      AlgebraicGeometry.reversePi p := by
  exact pullbackPi_left s p

private lemma underlyingPoint_eq
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    (underlyingPullbackCofork s p).pt =
      Limits.pullback (𝟙 s.pt.left) p := by
  rfl

private lemma underlyingSource_eq
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    ((FiniteEtale.pullback p).obj (pointSource s)).left =
      Limits.pullback (f ≫ s.π).left p := by
  rfl

private lemma underlyingMiddle_eq
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    ((FiniteEtale.pullback p).obj (pointMiddle s)).left =
      Limits.pullback s.π.left p := by
  rfl

private noncomputable def underlyingPointIso
    (s : Cofork f g) (p : U ⟶ s.pt.left) :=
  eqToIso (underlyingPoint_eq s p)

private noncomputable def underlyingSourceIso
    (s : Cofork f g) (p : U ⟶ s.pt.left) :=
  eqToIso (underlyingSource_eq s p)

private noncomputable def underlyingMiddleIso
    (s : Cofork f g) (p : U ⟶ s.pt.left) :=
  eqToIso (underlyingMiddle_eq s p)

private lemma scheme_comp_eqToHom_heq
    {W Y Z : Scheme.{u}} (h : W ⟶ Y) (e : Y = Z) :
    h ≫ eqToHom e ≍ h := by
  cases e
  simp

private lemma scheme_eqToHom_comp_comp_eqToHom_heq
    {V W Y Z : Scheme.{u}} (h : W ⟶ Y) (e₁ : V = W) (e₂ : Y = Z) :
    eqToHom e₁ ≫ h ≫ eqToHom e₂ ≍ h := by
  cases e₁
  cases e₂
  simp

/-- The forgotten finite étale pullback cofork is the reverse-oriented
Scheme cofork used in the pullback-symmetry bridge. -/
private def underlyingReverseIsColimitEquiv
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    IsColimit (underlyingPullbackCofork s p) ≃
      IsColimit (AlgebraicGeometry.reverseCofork
        (congrArg (fun k ↦ k.left) s.condition) p) :=
  Cofork.isColimitEquivOfIsos
    (underlyingPullbackCofork s p)
    (AlgebraicGeometry.reverseCofork
      (congrArg (fun k ↦ k.left) s.condition) p)
    (underlyingSourceIso s p) (underlyingMiddleIso s p)
    (underlyingPointIso s p)
    (by
      rw [underlying_left_eq_reverseLeft]
      change eqToHom (underlyingSource_eq s p) ≫
          AlgebraicGeometry.reverseLeft p =
        AlgebraicGeometry.reverseLeft p ≫
          eqToHom (underlyingMiddle_eq s p)
      apply eq_of_heq
      exact (eqToHom_comp_heq _ _).trans
        (scheme_comp_eqToHom_heq _ _).symm)
    (by
      rw [underlying_right_eq_reverseRight]
      change eqToHom (underlyingSource_eq s p) ≫
          AlgebraicGeometry.reverseRight
            (congrArg (fun k ↦ k.left) s.condition) p =
        AlgebraicGeometry.reverseRight
            (congrArg (fun k ↦ k.left) s.condition) p ≫
          eqToHom (underlyingMiddle_eq s p)
      apply eq_of_heq
      exact (eqToHom_comp_heq _ _).trans
        (scheme_comp_eqToHom_heq _ _).symm)
    (by
      rw [underlying_pi_eq_reversePi]
      change eqToHom (underlyingMiddle_eq s p).symm ≫
          AlgebraicGeometry.reversePi p ≫
            eqToHom (underlyingPoint_eq s p) =
        AlgebraicGeometry.reversePi p
      apply eq_of_heq
      exact scheme_eqToHom_comp_comp_eqToHom_heq _ _ _)

/-- Complete transport from the forgotten finite étale pullback cofork to
the literal `pullback.map` cofork required by Tag 0BMN. -/
private def underlyingZeroBMNIsColimitEquiv
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    IsColimit (underlyingPullbackCofork s p) ≃
      IsColimit (AlgebraicGeometry.zeroBMNCofork
        (congrArg (fun k ↦ k.left) s.condition) p) :=
  (underlyingReverseIsColimitEquiv s p).trans
    ((AlgebraicGeometry.reverseForwardIsColimitEquiv
      (congrArg (fun k ↦ k.left) s.condition) p).trans
      (AlgebraicGeometry.forwardZeroBMNIsColimitEquiv
        (congrArg (fun k ↦ k.left) s.condition) p))

private def nestedZeroBMNIsColimitEquiv
    (s : Cofork f g) (p : U ⟶ s.pt.left) :
    IsColimit (nestedUnderlyingCofork s p) ≃
      IsColimit (AlgebraicGeometry.zeroBMNCofork
        (congrArg (fun k ↦ k.left) s.condition) p) :=
  (nestedUnderlyingIsColimitEquiv s p).trans
    (underlyingZeroBMNIsColimitEquiv s p)

private theorem nonempty_isColimit_zeroBMN_of_nested
    (s : Cofork f g) (p : U ⟶ s.pt.left)
    (h : IsColimit
      ((FiniteEtale.pullback p ⋙ forgetToUnderlyingScheme U).mapCocone
        ((overToBase s.pt).mapCocone
          (CategoryTheory.Over.liftCocone s (𝟙 s.pt))))) :
    Nonempty
      (IsColimit (AlgebraicGeometry.zeroBMNCofork
        (congrArg (fun k ↦ k.left) s.condition) p)) :=
  ⟨nestedZeroBMNIsColimitEquiv s p h⟩

end AlgebraicGeometry.FiniteEtale.PullbackCoforkTransport

namespace AlgebraicGeometry.FiniteEtale

variable {X : Scheme.{u}}

private noncomputable def schemePullbackCoforkForDescent
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) {U : Scheme.{u}} (r : U ⟶ s.pt.left) :=
  AlgebraicGeometry.zeroBMNCofork
    (congrArg (fun k ↦ k.left) s.condition) r

private theorem schemePullbackCoforkForDescent_isColimit_congr
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) {U : Scheme.{u}} {r r' : U ⟶ s.pt.left}
    (h : r = r')
    (hr : Nonempty (IsColimit (schemePullbackCoforkForDescent s r))) :
    Nonempty (IsColimit (schemePullbackCoforkForDescent s r')) := by
  subst r'
  exact hr

private theorem localSplitZeroBMNIsColimit
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (hs : IsColimit s)
    (j : Σ i : s.pt.left.affineOpenCover.I₀,
      PrimeSpectrum (s.pt.left.affineOpenCover.X i)) :
    Nonempty
      (IsColimit
        (schemePullbackCoforkForDescent s (localSplitMap s j))) := by
  let := (localSplitComponent s j.1 j.2).commRing
  let := (localSplitComponent s j.1 j.2).algebra
  have hdirect := localSplitCoforkForgetAfterPullbackIsColimit
    s hs j.1 (localSplitComponent s j.1 j.2).split
      (𝟙 (Spec (.of (localSplitComponent s j.1 j.2).S)))
  let r : Spec (.of (localSplitComponent s j.1 j.2).S) ⟶ s.pt.left :=
    𝟙 _ ≫
      (Spec.map (CommRingCat.ofHom
          (algebraMap (s.pt.left.affineOpenCover.X j.1)
            (localSplitComponent s j.1 j.2).S)) ≫
        s.pt.left.affineOpenCover.f j.1)
  have hzero : Nonempty
      (IsColimit (schemePullbackCoforkForDescent s r)) :=
    PullbackCoforkTransport.nonempty_isColimit_zeroBMN_of_nested s r (by
      dsimp only [r]
      exact hdirect)
  apply schemePullbackCoforkForDescent_isColimit_congr s
    (r := r) (r' := localSplitMap s j) _ hzero
  simp only [r, localSplitMap, localSplitObj, Category.id_comp]

private theorem localSplitOverlapZeroBMNIsColimit
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (hs : IsColimit s)
    (j k : Σ i : s.pt.left.affineOpenCover.I₀,
      PrimeSpectrum (s.pt.left.affineOpenCover.X i)) :
    let r := pullback.fst (localSplitMap s j)
        (localSplitMap s k) ≫ localSplitMap s j
    Nonempty (IsColimit (schemePullbackCoforkForDescent s r)) := by
  dsimp only
  let := (localSplitComponent s j.1 j.2).commRing
  let := (localSplitComponent s j.1 j.2).algebra
  let q := pullback.fst (localSplitMap s j) (localSplitMap s k)
  have hdirect := localSplitCoforkForgetAfterPullbackIsColimit
    s hs j.1 (localSplitComponent s j.1 j.2).split q
  apply PullbackCoforkTransport.nonempty_isColimit_zeroBMN_of_nested
    s (q ≫ localSplitMap s j)
  simpa only [q, localSplitMap, localSplitObj, Category.assoc] using hdirect

private def forgetToUnderlyingSchemeMapCoconeIsColimit
    {A B : FiniteEtale X} {f g : A ⟶ B}
    (s : Cofork f g) (hs : IsColimit s) :
    IsColimit ((forgetToUnderlyingScheme X).mapCocone s) := by
  have hc : f.left ≫ s.π.left = g.left ≫ s.π.left := by
    exact congrArg (fun k ↦ k.left) s.condition
  have hscheme : Nonempty
      (IsColimit (Cofork.ofπ s.π.left hc)) :=
    Scheme.isColimit_cofork_of_fpqc_local hc
      (localSplitObj s) (localSplitMap s)
      (localSplitMap_mem_fpqcPrecoverage s)
      (fun j ↦ by
        rcases localSplitZeroBMNIsColimit s hs j with ⟨hj⟩
        exact ⟨hj.ofIsoColimit
          (Cofork.ext (Iso.refl _) (by
            change pullback.fst (localSplitMap s j) s.π.left ≫ 𝟙 _ =
              pullback.fst (localSplitMap s j) s.π.left
            simp))⟩)
      (fun j k ↦ by
        rcases localSplitOverlapZeroBMNIsColimit s hs j k with ⟨hjk⟩
        exact ⟨hjk.ofIsoColimit
          (Cofork.ext (Iso.refl _) (by
            change pullback.fst
                (pullback.fst (localSplitMap s j) (localSplitMap s k) ≫
                  localSplitMap s j) s.π.left ≫ 𝟙 _ =
              pullback.fst
                (pullback.fst (localSplitMap s j) (localSplitMap s k) ≫
                  localSplitMap s j) s.π.left
            simp))⟩)
  let F : Functor (FiniteEtale X) Scheme.{u} :=
    FiniteEtale.forget X ⋙ CategoryTheory.Over.forget X
  have hschemeMapped : IsColimit
      (Cofork.ofπ (f := F.map f) (g := F.map g) (F.map s.π)
        (by rw [← F.map_comp, ← F.map_comp, s.condition])) := by
    change IsColimit (Cofork.ofπ s.π.left hc)
    exact hscheme.some
  have hcanonical : IsColimit
      (F.mapCocone (Cofork.ofπ s.π s.condition)) :=
    (isColimitMapCoconeCoforkEquiv F s.condition).symm hschemeMapped
  let e : F.mapCocone (Cofork.ofπ s.π s.condition) ≅
      (forgetToUnderlyingScheme X).mapCocone s :=
    ((Cocone.functoriality (parallelPair f g) F).mapIso
      (Cofork.isoCoforkOfπ s)).symm
  exact hcanonical.ofIsoColimit e

private theorem forgetCompOverForgetPreservesParallelPair
    {A B : FiniteEtale X} (f g : A ⟶ B) :
    PreservesColimit (parallelPair f g)
      (FiniteEtale.forget X ⋙ CategoryTheory.Over.forget X) := by
  constructor
  intro s hs
  exact ⟨forgetToUnderlyingSchemeMapCoconeIsColimit s hs⟩

/-- Forgetting a finite étale scheme all the way to schemes preserves
coequalizers. -/
instance forgetCompOverForgetPreservesCoequalizers :
    PreservesColimitsOfShape WalkingParallelPair
      (FiniteEtale.forget X ⋙ CategoryTheory.Over.forget X) where
  preservesColimit {K} := by
    let := forgetCompOverForgetPreservesParallelPair
      (K.map WalkingParallelPairHom.left)
      (K.map WalkingParallelPairHom.right)
    exact preservesColimit_of_iso_diagram _ (diagramIsoParallelPair K).symm

/-- The canonical forgetful functor from finite étale schemes over `X` to
schemes over `X` preserves coequalizers. -/
instance forgetPreservesCoequalizers :
    PreservesColimitsOfShape WalkingParallelPair (FiniteEtale.forget X) := by
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (FiniteEtale.forget X) (CategoryTheory.Over.forget X)

/-- The canonical forgetful functor from finite étale schemes over `X` to
schemes over `X` preserves finite colimits. -/
instance forgetPreservesFiniteColimits :
    PreservesFiniteColimits (FiniteEtale.forget X) :=
  preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts _

/-- Forgetting a finite étale scheme all the way to schemes preserves finite
colimits. -/
instance forgetCompOverForgetPreservesFiniteColimits :
    PreservesFiniteColimits
      (FiniteEtale.forget X ⋙ CategoryTheory.Over.forget X) :=
  preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts _

end AlgebraicGeometry.FiniteEtale
