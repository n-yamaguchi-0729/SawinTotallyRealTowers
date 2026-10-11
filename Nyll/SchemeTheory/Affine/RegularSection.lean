/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.Stalks

/-!
# Restricting a regular global section

A non-zero-divisor on an affine scheme remains a non-zero-divisor on the
sections of every open subset. This follows by testing at the actual
localized stalks and is valid without reducedness or Noetherianity.
-/


open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

namespace AlgebraicGeometry

universe u

/-- A regular global section of an affine scheme acts injectively on sections
of every open subset. -/
theorem isSMulRegular_restrict_of_affine
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens)
    (r : Γ(X, ⊤)) (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) :
    IsSMulRegular Γ(X, U)
      ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) r) := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro s hs
  apply TopCat.Presheaf.section_ext X.sheaf U s 0
  intro p hp
  let htop := isAffineOpen_top X
  let : Algebra Γ(X, ⊤) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (U := ⊤) ⟨p, trivial⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk p)
      (htop.primeIdealOf ⟨p, trivial⟩).asIdeal :=
    htop.isLocalization_stalk ⟨p, trivial⟩
  have hrp : X.presheaf.germ ⊤ p trivial r ∈
      nonZeroDivisors (X.presheaf.stalk p) :=
    IsLocalization.nonZeroDivisors_le_comap
      (htop.primeIdealOf ⟨p, trivial⟩).asIdeal.primeCompl (X.presheaf.stalk p) hr
  have hz : X.presheaf.germ ⊤ p trivial r *
      X.presheaf.germ U p hp s = 0 := by
    have h := congrArg (X.presheaf.germ U p hp) hs
    simpa only [smul_eq_mul, map_mul, map_zero, X.presheaf.germ_res_apply] using h
  rw [map_zero]
  exact mem_nonZeroDivisors_iff_left.mp hrp _ hz

/-- Restriction to the nonvanishing locus of a regular section is injective
on a quasi-compact, quasi-separated open. -/
theorem restrict_basicOpen_injective_of_affine
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens)
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (r : Γ(X, ⊤)) (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) :
    Function.Injective
      (X.presheaf.map (homOfLE (X.basicOpen_le
        ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) r))).op) := by
  let rU : Γ(X, U) := (X.presheaf.map (homOfLE le_top).op) r
  let : IsLocalization.Away rU Γ(X, X.basicOpen rU) :=
    isLocalization_basicOpen_of_qcqs hU hU' rU
  have hregular : IsSMulRegular Γ(X, U) rU :=
    isSMulRegular_restrict_of_affine X U r hr
  have hmem : rU ∈ nonZeroDivisors Γ(X, U) :=
    mem_nonZeroDivisors_iff_left.mpr fun s hs =>
      hregular.right_eq_zero_of_smul hs
  exact IsLocalization.injective Γ(X, X.basicOpen rU)
    (Submonoid.powers_le.mpr hmem)

end AlgebraicGeometry
