/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.LocalRestriction
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Nyll.SchemeTheory.Affine.WeilRestriction.Global
public import Nyll.SchemeTheory.FiniteEtale.Basic

/-!
# A principal open cover carrying finite étale internal Homs

For finite étale `R`-algebras `A` and `B`, we construct an open cover of
`Spec R` by spectra of principal localizations. On each member of the cover,
the restriction of the fixed global internal Hom presheaf is represented by
an explicitly chosen finite étale scheme. These are local witnesses for the
subsequent gluing construction.
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace SchemeTheory.Affine

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [Module.Finite R A] [Algebra.Etale R A]
  [Module.Finite R B] [Algebra.Etale R B]

/-- An element outside `p` whose principal neighborhood admits a finite étale
representer of the restricted internal Hom. -/
def finiteEtaleInternalHomLocalElement (p : PrimeSpectrum R) : R :=
  (exists_finiteEtaleInternalHomRepresentable_restrict_away
    (R := R) (A := A) (B := B) p).choose

lemma finiteEtaleInternalHomLocalElement_not_mem (p : PrimeSpectrum R) :
    finiteEtaleInternalHomLocalElement (R := R) (A := A) (B := B) p ∉ p.asIdeal :=
  (exists_finiteEtaleInternalHomRepresentable_restrict_away
    (R := R) (A := A) (B := B) p).choose_spec.1

/-- A cover of `Spec R` by principal neighborhoods carrying finite étale
representers of the relative internal Hom. -/
def finiteEtaleInternalHomOpenCover : (Spec (CommRingCat.of R)).OpenCover where
  I₀ := PrimeSpectrum R
  X p := Spec (CommRingCat.of (Localization.Away
    (finiteEtaleInternalHomLocalElement (R := R) (A := A) (B := B) p)))
  f p := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away
    (finiteEtaleInternalHomLocalElement (R := R) (A := A) (B := B) p))))
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro p
      refine ⟨p, ?_⟩
      change p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away
        (finiteEtaleInternalHomLocalElement (R := R) (A := A) (B := B) p))))
      rw [PrimeSpectrum.localization_away_comap_range
        (Localization.Away
          (finiteEtaleInternalHomLocalElement (R := R) (A := A) (B := B) p))
        (finiteEtaleInternalHomLocalElement (R := R) (A := A) (B := B) p)]
      exact finiteEtaleInternalHomLocalElement_not_mem (R := R) (A := A) (B := B) p
    · intro p
      exact Scheme.isOpenImmersion_SpecMap_localizationAway
        (R := CommRingCat.of R)
        (finiteEtaleInternalHomLocalElement (R := R) (A := A) (B := B) p)

/-- A finite étale representer on a member of the principal open cover. -/
def finiteEtaleInternalHomOpenCoverRepresenter (p : PrimeSpectrum R) :
    FiniteEtale ((finiteEtaleInternalHomOpenCover (R := R) (A := A) (B := B)).X p) :=
  (exists_finiteEtaleInternalHomRepresentable_restrict_away
    (R := R) (A := A) (B := B) p).choose_spec.2.choose

/-- On each member of the cover, the chosen finite étale scheme represents
the restriction of the same global internal Hom presheaf. -/
def finiteEtaleInternalHomOpenCoverRepresentable (p : PrimeSpectrum R) :
    ((Over.map ((finiteEtaleInternalHomOpenCover
      (R := R) (A := A) (B := B)).f p)).op ⋙
        globalInternalHomFunctor (R := R) (A := A) (B := B)).RepresentableBy
          ((FiniteEtale.forget ((finiteEtaleInternalHomOpenCover
            (R := R) (A := A) (B := B)).X p)).obj
              (finiteEtaleInternalHomOpenCoverRepresenter (R := R) (A := A) (B := B) p)) :=
  Classical.choice (exists_finiteEtaleInternalHomRepresentable_restrict_away
    (R := R) (A := A) (B := B) p).choose_spec.2.choose_spec

end SchemeTheory.Affine
