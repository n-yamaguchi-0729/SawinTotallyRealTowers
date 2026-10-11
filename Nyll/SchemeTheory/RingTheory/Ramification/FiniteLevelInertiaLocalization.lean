/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaDiagram
import Mathlib.Algebra.Category.AlgCat.FilteredColimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Data.Finset.Insert
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.OreLocalization.Ring


/-!
# The actual localized finite-level invariant colimit

Every stage is localized at the literal contraction of the chosen upper
prime. The maps are the existing `Localization.localAlgHom`; their composition
and values on fractions use the existing local-ring homomorphism identities.
Finite representatives of numerator and denominator give surjectivity, and
the existing localization map-injectivity theorem detects equality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.Inertia

universe u v w

/-- Expose the one native localization ring dictionary at the categorical
object boundary. Its Ring projection is the native Ore localization Ring. -/
private def primeLocalizationAlgCat
    (B : Type u) (R : Type w) [CommRing B] [CommRing R] [Algebra B R]
    (p : Ideal R) [p.IsPrime] : AlgCat.{w} B := by
  letI : CommRing (Localization.AtPrime p) :=
    inferInstanceAs (CommRing (OreLocalization p.primeCompl R))
  exact AlgCat.of B (Localization.AtPrime p)

/-- Apply the existing localization injectivity theorem before introducing
normalization towers. This keeps the ring carriers fixed at its native API. -/
private theorem localRingHom_injective_of_injective
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (f : R →+* S) (hpq : p = q.comap f) (hf : Function.Injective f) :
    Function.Injective (Localization.localRingHom p q f hpq) := by
  have hden : p.primeCompl ≤ q.primeCompl.comap f :=
    (Localization.le_comap_primeCompl_iff (I := p) (J := q) (f := f)).mpr hpq.ge
  have hmap : Localization.localRingHom p q f hpq =
      IsLocalization.map (M := p.primeCompl) (T := q.primeCompl)
        (Localization.AtPrime q) f hden := rfl
  rw [hmap]
  exact IsLocalization.map_injective_of_injective'
    (R := R) (Rₘ := Localization.AtPrime p) (f := f) (N := q.primeCompl)
    p.primeCompl S (Localization.AtPrime q) hden
    (fun h => h q.zero_mem) hf

attribute [local instance] normalizationInertiaImageAction normalizationInertiaImageTower
  normalizationInertiaCoefficientCommClass

variable (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (integralClosure A L)) [hQ : Q.IsPrime]

local notation "C" => integralClosure A L
local notation "CI" => FixedPoints.subalgebra A C (Q.inertia Gal(L/K))

/-- The chosen prime contracted to the actual upper inertia-fixed algebra. -/
def inertiaInvariantPrime : Ideal CI :=
  Q.comap (FixedPoints.subalgebra A C (Q.inertia Gal(L/K))).val

local instance inertiaInvariantPrime_isPrime : (inertiaInvariantPrime A K L Q).IsPrime :=
  Ideal.IsPrime.comap (FixedPoints.subalgebra A C (Q.inertia Gal(L/K))).val

/-- Its literal contraction to the finite invariant stage. -/
def finiteLevelInertiaPrime (E : FiniteGaloisIntermediateField K L) :
    Ideal (finiteLevelInertiaSubalgebra A K L Q E) :=
  (inertiaInvariantPrime A K L Q).comap (finiteLevelInertiaSubalgebraInclusion A K L Q E)

local instance finiteLevelInertiaPrime_isPrime (E : FiniteGaloisIntermediateField K L) :
    (finiteLevelInertiaPrime A K L Q E).IsPrime :=
  Ideal.IsPrime.comap (finiteLevelInertiaSubalgebraInclusion A K L Q E)

/-- The native localization map between the actual contracted-prime stages. -/
def finiteLevelInertiaLocalizationMap {E F : FiniteGaloisIntermediateField K L} (h : E ≤ F) :
    Localization.AtPrime (finiteLevelInertiaPrime A K L Q E) →ₐ[A]
      Localization.AtPrime (finiteLevelInertiaPrime A K L Q F) :=
  Localization.localAlgHom (finiteLevelInertiaPrime A K L Q E)
    (finiteLevelInertiaPrime A K L Q F) (finiteLevelInertiaSubalgebraMap A K L Q h)
    (by ext b; rfl)

/-- The native localization map into the chosen upper invariant local ring. -/
def finiteLevelInertiaLocalizationInclusion (E : FiniteGaloisIntermediateField K L) :
    Localization.AtPrime (finiteLevelInertiaPrime A K L Q E) →ₐ[A]
      Localization.AtPrime (inertiaInvariantPrime A K L Q) :=
  Localization.localAlgHom (finiteLevelInertiaPrime A K L Q E)
    (inertiaInvariantPrime A K L Q) (finiteLevelInertiaSubalgebraInclusion A K L Q E) rfl

/-- The actual finite-Galois diagram of invariant local rings. -/
def finiteLevelInertiaLocalizationDiagram :
    FiniteGaloisIntermediateField K L ⥤ AlgCat.{w} A where
  obj E := primeLocalizationAlgCat A (finiteLevelInertiaSubalgebra A K L Q E)
    (finiteLevelInertiaPrime A K L Q E)
  map f := AlgCat.ofHom (finiteLevelInertiaLocalizationMap A K L Q f.le)
  map_id E := by
    apply AlgCat.hom_ext
    apply AlgHom.ext
    intro z
    exact congrArg
      (fun f : Localization.AtPrime (finiteLevelInertiaPrime A K L Q E) →+*
        Localization.AtPrime (finiteLevelInertiaPrime A K L Q E) => f z)
      (Localization.localRingHom_id (finiteLevelInertiaPrime A K L Q E))
  map_comp {E F G} f g := by
    apply AlgCat.hom_ext
    apply AlgHom.ext
    intro z
    exact congrArg
      (fun h : Localization.AtPrime (finiteLevelInertiaPrime A K L Q E) →+*
        Localization.AtPrime (finiteLevelInertiaPrime A K L Q G) => h z)
      (Localization.localRingHom_comp (finiteLevelInertiaPrime A K L Q E)
        (finiteLevelInertiaPrime A K L Q F) (finiteLevelInertiaPrime A K L Q G)
        (finiteLevelInertiaSubalgebraMap A K L Q f.le).toRingHom (by ext b; rfl)
        (finiteLevelInertiaSubalgebraMap A K L Q g.le).toRingHom (by ext b; rfl))

/-- The cocone consists of the native maps to the actual upper local ring. -/
def finiteLevelInertiaLocalizationCocone :
    Cocone (finiteLevelInertiaLocalizationDiagram A K L Q) where
  pt := primeLocalizationAlgCat A CI (inertiaInvariantPrime A K L Q)
  ι.app E := AlgCat.ofHom (finiteLevelInertiaLocalizationInclusion A K L Q E)
  ι.naturality E F f := by
    apply AlgCat.hom_ext
    apply AlgHom.ext
    intro z
    exact congrArg
      (fun h : Localization.AtPrime (finiteLevelInertiaPrime A K L Q E) →+*
        Localization.AtPrime (inertiaInvariantPrime A K L Q) => h z)
      (Localization.localRingHom_comp (finiteLevelInertiaPrime A K L Q E)
        (finiteLevelInertiaPrime A K L Q F) (inertiaInvariantPrime A K L Q)
        (finiteLevelInertiaSubalgebraMap A K L Q f.le).toRingHom (by ext b; rfl)
        (finiteLevelInertiaSubalgebraInclusion A K L Q F).toRingHom rfl).symm

omit hQ in
/-- The literal finite invariant-stage inclusion is injective, as witnessed
by its underlying inclusion into the ambient Galois field. -/
theorem finiteLevelInertiaSubalgebraInclusion_injective (E : FiniteGaloisIntermediateField K L) :
    Function.Injective (finiteLevelInertiaSubalgebraInclusion A K L Q E) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun b : CI => ((b : C) : L)) h

private theorem finiteLevelInertiaLocalizationInclusion_injective
    (E : FiniteGaloisIntermediateField K L) :
    Function.Injective
      ((finiteLevelInertiaLocalizationInclusion A K L Q E).toRingHom :
        Localization.AtPrime (finiteLevelInertiaPrime A K L Q E) →+*
          Localization.AtPrime (inertiaInvariantPrime A K L Q)) := by
  have hdom : IsDomain CI := inferInstance
  have hinj := finiteLevelInertiaSubalgebraInclusion_injective A K L Q E
  have hn := localRingHom_injective_of_injective
    (R := finiteLevelInertiaSubalgebra A K L Q E)
    (S := FixedPoints.subalgebra A C (Q.inertia Gal(L/K)))
    (finiteLevelInertiaPrime A K L Q E) (inertiaInvariantPrime A K L Q)
    (finiteLevelInertiaSubalgebraInclusion A K L Q E).toRingHom rfl hinj
  exact hn

/-- The localization of the upper inertia invariants is the actual filtered
colimit of the localizations of its finite invariant stages. The denominator
belongs to a finite stage simultaneously with the numerator and stays outside
its contracted prime by the literal inclusion equation. -/
def finiteLevelInertiaLocalizationCoconeIsColimit :
    IsColimit (finiteLevelInertiaLocalizationCocone A K L Q) := by
  apply isColimitOfReflects (forget₂ (AlgCat.{w} A) RingCat.{w})
  letI : ReflectsColimit
      (finiteLevelInertiaLocalizationDiagram A K L Q ⋙ forget₂ (AlgCat.{w} A) RingCat.{w})
      (forget RingCat.{w}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget RingCat.{w})
  apply Types.FilteredColimit.isColimitOf'
  · change ∀ z : Localization.AtPrime (inertiaInvariantPrime A K L Q),
        ∃ (E : FiniteGaloisIntermediateField K L)
          (x : Localization.AtPrime (finiteLevelInertiaPrime A K L Q E)),
          z = finiteLevelInertiaLocalizationInclusion A K L Q E x
    intro z
    classical
    obtain ⟨n, d, rfl⟩ := IsLocalization.exists_mk'_eq
      (inertiaInvariantPrime A K L Q).primeCompl z
    let s : Finset C := {(n : C), ((d : CI) : C)}
    have hs : ∀ b ∈ s, ∀ σ ∈ Q.inertia Gal(L/K), σ • b = b := by
      intro b hb σ hσ
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact n.property ⟨σ, hσ⟩
      · have hb' : b = ((d : CI) : C) := Finset.mem_singleton.mp hb
        rw [hb']
        exact (d : CI).property ⟨σ, hσ⟩
    obtain ⟨E, hE⟩ := integralClosure_inertia_fixed_finite_representatives A K L Q s hs
    obtain ⟨nE, hnE, _⟩ := hE (n : C) (Finset.mem_insert_self _ _)
    obtain ⟨dE, hdE, _⟩ := hE ((d : CI) : C)
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hnEI : nE ∈ finiteLevelInertiaSubalgebra A K L Q E := by
      change (IsScalarTower.toAlgHom A E L).mapIntegralClosure nE ∈ CI
      rw [hnE]
      exact n.property
    have hdEI : dE ∈ finiteLevelInertiaSubalgebra A K L Q E := by
      change (IsScalarTower.toAlgHom A E L).mapIntegralClosure dE ∈ CI
      rw [hdE]
      exact (d : CI).property
    let n' : finiteLevelInertiaSubalgebra A K L Q E := ⟨nE, hnEI⟩
    let d' : finiteLevelInertiaSubalgebra A K L Q E := ⟨dE, hdEI⟩
    have hn' : finiteLevelInertiaSubalgebraInclusion A K L Q E n' = n := Subtype.ext hnE
    have hd' : finiteLevelInertiaSubalgebraInclusion A K L Q E d' = (d : CI) :=
      Subtype.ext hdE
    have hdP : d' ∈ (finiteLevelInertiaPrime A K L Q E).primeCompl := by
      change finiteLevelInertiaSubalgebraInclusion A K L Q E d' ∉
        inertiaInvariantPrime A K L Q
      rw [hd']
      exact d.property
    refine ⟨E, IsLocalization.mk' (Localization.AtPrime (finiteLevelInertiaPrime A K L Q E))
      n' ⟨d', hdP⟩, ?_⟩
    have hcontract : finiteLevelInertiaPrime A K L Q E =
        (inertiaInvariantPrime A K L Q).comap
          (finiteLevelInertiaSubalgebraInclusion A K L Q E).toRingHom := rfl
    let dImage : (inertiaInvariantPrime A K L Q).primeCompl :=
      ⟨finiteLevelInertiaSubalgebraInclusion A K L Q E d',
        (Localization.le_comap_primeCompl_iff
          (I := finiteLevelInertiaPrime A K L Q E)
          (J := inertiaInvariantPrime A K L Q)
          (f := (finiteLevelInertiaSubalgebraInclusion A K L Q E).toRingHom)).mpr
          hcontract.ge hdP⟩
    have hdImage : dImage = d := Subtype.ext hd'
    have hfrac :
        Localization.localRingHom (finiteLevelInertiaPrime A K L Q E)
            (inertiaInvariantPrime A K L Q)
            (finiteLevelInertiaSubalgebraInclusion A K L Q E).toRingHom hcontract
            (IsLocalization.mk' (Localization.AtPrime (finiteLevelInertiaPrime A K L Q E))
              n' ⟨d', hdP⟩) =
          IsLocalization.mk' (Localization.AtPrime (inertiaInvariantPrime A K L Q))
            (finiteLevelInertiaSubalgebraInclusion A K L Q E n') dImage :=
      Localization.localRingHom_mk' (finiteLevelInertiaPrime A K L Q E)
        (inertiaInvariantPrime A K L Q)
        (finiteLevelInertiaSubalgebraInclusion A K L Q E).toRingHom hcontract n' ⟨d', hdP⟩
    change IsLocalization.mk' (Localization.AtPrime (inertiaInvariantPrime A K L Q)) n d =
      Localization.localRingHom (finiteLevelInertiaPrime A K L Q E)
        (inertiaInvariantPrime A K L Q)
        (finiteLevelInertiaSubalgebraInclusion A K L Q E).toRingHom hcontract
        (IsLocalization.mk' _ n' ⟨d', hdP⟩)
    exact (congrArg₂
      (fun (a : CI) (s₀ : (inertiaInvariantPrime A K L Q).primeCompl) =>
        IsLocalization.mk' (Localization.AtPrime (inertiaInvariantPrime A K L Q)) a s₀)
      hn'.symm hdImage.symm).trans hfrac.symm
  · intro E x y hxy
    refine ⟨E, 𝟙 E, ?_⟩
    have hxy' : x = y :=
      finiteLevelInertiaLocalizationInclusion_injective A K L Q E hxy
    exact congrArg
      (ConcreteCategory.hom
        (((finiteLevelInertiaLocalizationDiagram A K L Q ⋙
          forget₂ (AlgCat.{w} A) RingCat.{w}) ⋙ forget RingCat.{w}).map (𝟙 E))) hxy'

end EtaleFundamentalGroups.Inertia
