/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The local rings of a closed subscheme

The kernel of the stalk map of a closed immersion is the stalk ideal of
its defining ideal sheaf. Thus the actual local ring of a closed subscheme
is the quotient of the ambient local ring by its stalk ideal.

The comparison is obtained by localizing the surjective map on sections
over an affine neighbourhood. In particular, the equivalence below is
induced by the actual stalk map of the closed immersion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The ideal of a closed immersion localizes to the kernel of its stalk map. -/
theorem ker_stalkMap_eq_stalkIdeal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (x : X) :
    RingHom.ker (f.stalkMap x).hom = f.ker.stalkIdeal (f x) := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := f x)
      (show f x ∈ (⊤ : Y.Opens) from trivial)
  let V : X.Opens := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let A := Γ(Y, U)
  let B := Γ(X, V)
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let g : A →+* B := (f.app U).hom
  let p : Ideal A := (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal
  let q : Ideal B := (hV.primeIdealOf ⟨x, hxU⟩).asIdeal
  have hp : p.IsPrime := (hU.primeIdealOf ⟨f x, hxU⟩).isPrime
  have hq : q.IsPrime := (hV.primeIdealOf ⟨x, hxU⟩).isPrime
  let : Algebra A R := (Y.presheaf.germ U (f x) hxU).hom.toAlgebra
  let : Algebra B S := (X.presheaf.germ V x hxU).hom.toAlgebra
  have : IsLocalization.AtPrime R p := hU.isLocalization_stalk ⟨f x, hxU⟩
  have : IsLocalization.AtPrime S q := hV.isLocalization_stalk ⟨x, hxU⟩
  have hpq : q.comap g = p := by
    simpa only [V, Scheme.Hom.appLE_eq_app, PrimeSpectrum.comap_asIdeal,
      g, p, q] using
      congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl hxU)
  have hmap : p.primeCompl.map g = q.primeCompl := by
    simpa only [hpq] using
      Ideal.map_primeCompl_comap_of_surjective g (f.app_surjective U hU) q
  let φ : R →+* S :=
    IsLocalization.map S g (hmap.symm ▸ p.primeCompl.le_comap_map)
  have hφ : φ = (f.stalkMap x).hom := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    change φ (algebraMap A R a) = f.stalkMap x (Y.presheaf.germ U (f x) hxU a)
    rw [IsLocalization.map_eq]
    exact (f.germ_stalkMap_apply U x hxU a).symm
  rw [← hφ, IsLocalization.ker_map S g hmap,
    f.ker.stalkIdeal_eq_map_ideal (f x) ⟨U, hU⟩ hxU, f.ker_apply]
  rfl

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- At a point on its support, a closed subscheme has a proper stalk ideal. -/
theorem stalkIdeal_le_maximalIdeal_of_mem_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (x : X) (hx : x ∈ I.support) :
    I.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  have hx' : x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hx
  obtain ⟨z, rfl⟩ := hx'
  have hker : RingHom.ker (I.subschemeι.stalkMap z).hom =
      I.stalkIdeal (I.subschemeι z) := by
    rw [I.subschemeι.ker_stalkMap_eq_stalkIdeal z, I.ker_subschemeι]
  rw [← hker]
  exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (I.subschemeι.stalkMap z).hom)

/-- The actual closed subscheme stalk is the quotient by the ambient stalk ideal. -/
def subschemeStalkQuotientEquiv {X : Scheme.{u}} (I : X.IdealSheafData)
    (x : I.subscheme) :
    (X.presheaf.stalk (I.subschemeι x) ⧸ I.stalkIdeal (I.subschemeι x)) ≃+*
      I.subscheme.presheaf.stalk x :=
  (Ideal.quotEquivOfEq (by
    rw [I.subschemeι.ker_stalkMap_eq_stalkIdeal x, I.ker_subschemeι])).trans
    ((I.subschemeι.stalkMap x).hom.quotientKerEquivOfSurjective
      (I.subschemeι.stalkMap_surjective x))

/-- The quotient comparison is induced by the closed immersion's stalk map. -/
theorem subschemeStalkQuotientEquiv_apply_mk {X : Scheme.{u}}
    (I : X.IdealSheafData) (x : I.subscheme)
    (a : X.presheaf.stalk (I.subschemeι x)) :
    I.subschemeStalkQuotientEquiv x
        (Ideal.Quotient.mk (I.stalkIdeal (I.subschemeι x)) a) =
      I.subschemeι.stalkMap x a := by
  simp only [subschemeStalkQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

end AlgebraicGeometry.Scheme.IdealSheafData
