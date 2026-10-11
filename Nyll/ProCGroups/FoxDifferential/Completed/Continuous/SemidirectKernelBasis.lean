/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Topology

/-!
# Fox differential: completed — continuous — semidirect kernel basis

The principal declarations in this module are:

- `finiteCoordinateZeroRectangularNeighbourhoods_pi`
  Finite-coordinate product neighborhoods in a function space contain coordinate rectangles. This is
  the generic topological input needed to pass from coefficient-kernel bases for
  \(\mathbb{Z}_C\llbracket H\rrbracket\) to coordinate-kernel bases for \(\mathbb{Z}_C\llbracket
  H\rrbracket^{X}\). It uses the product topology directly and keeps no algebraic assumptions.
- `zcFreeFoxCoordinates_hasFiniteCoordinateZeroRectangularNeighbourhoods`
  Standard product-topology coordinate rectangles for completed Fox-coordinate families.
- `zcCompletedFoxSemidirect_hasRectangularIdentityNeighbourhoods`
  In the standard topology on \(\mathbb{Z}_C\llbracket H\rrbracket^{X} \rtimes H\), every identity
  neighborhood contains a product rectangle around (0,1) in the coordinate and target components.
- `freeProCZCFoxSemiZCBifilteredStageMap_identity_basis_of_component_bases_standardTopology`
  Standard-topology form of the componentwise kernel-basis theorem for actual
  \(\mathbb{Z}_C\llbracket H\rrbracket\) bifiltered finite stages.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC

universe u v


section CoordinateRectangularNeighbourhoods

variable {A : Type u} [AddCommMonoid A] [TopologicalSpace A]
variable {X : Type u}

/--
Finite-coordinate product neighborhoods in a function space contain coordinate rectangles. This
is the generic topological input needed to pass from coefficient-kernel bases for
\(\mathbb{Z}_C\llbracket H\rrbracket\) to coordinate-kernel bases for \(\mathbb{Z}_C\llbracket
H\rrbracket^{X}\). It uses the product topology directly and keeps no algebraic assumptions.
-/
theorem finiteCoordinateZeroRectangularNeighbourhoods_pi :
    HasFiniteCoordinateZeroRectangularNeighbourhoods (A := A) (X := X) := by
  intro U hU hUzero
  classical
  rcases (isOpen_pi_iff.mp hU) (0 : X → A) hUzero with ⟨J, W, hW, hJU⟩
  let V : X → Set A := fun x => if hx : x ∈ J then W x else Set.univ
  refine ⟨V, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ J
    · simpa [V, hx] using hW x hx
    · simp only [dite_eq_ite, hx, ↓reduceIte, isOpen_univ, Set.mem_univ, and_self, V]
  · intro v hv
    apply hJU
    intro x hx
    have hvx := hv x
    have hxJ : x ∈ J := by
      simpa using hx
    have hVx : V x = W x := by
      simp only [dite_eq_ite, hxJ, ↓reduceIte, V]
    rwa [hVx] at hvx

/-- Standard product-topology coordinate rectangles for completed Fox-coordinate families. -/
theorem zcFreeFoxCoordinates_hasFiniteCoordinateZeroRectangularNeighbourhoods
    (C : ProCGroups.FiniteGroupClass.{u}) (X H : Type u)
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    HasFiniteCoordinateZeroRectangularNeighbourhoods
      (A := ZCCompletedGroupAlgebra C H) (X := X) :=
  finiteCoordinateZeroRectangularNeighbourhoods_pi

end CoordinateRectangularNeighbourhoods

section RectangularNeighbourhoods

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (X : Type u) [DecidableEq X]
variable (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [DecidableEq X] in
/--
In the standard topology on \(\mathbb{Z}_C\llbracket H\rrbracket^{X} \rtimes H\), every identity
neighborhood contains a product rectangle around (0,1) in the coordinate and target components.
-/
theorem zcCompletedFoxSemidirect_hasRectangularIdentityNeighbourhoods :
    HasSemidirectRectangularIdentityNeighbourhoods
      (X := X) (H := H) C := by
  intro U hU hUone
  rcases isOpen_induced_iff.mp hU with ⟨V, hVopen, hVeq⟩
  have hVone :
      ((0 : ZCFreeFoxCoordinates C (X := X) (H := H)), (1 : H)) ∈ V := by
    have hpre :
        (1 : ZCCompletedFoxSemidirect C X H) ∈
          (fun a : ZCCompletedFoxSemidirect C X H => (a.left, a.right)) ⁻¹' V := by
      simpa [hVeq]
        using hUone
    simpa using hpre
  have hVnhds : V ∈ 𝓝 ((0 : ZCFreeFoxCoordinates C (X := X) (H := H)), (1 : H)) :=
    hVopen.mem_nhds hVone
  rcases mem_nhds_prod_iff.mp hVnhds with ⟨UL₀, hUL₀, UR₀, hUR₀, hprod⟩
  rcases mem_nhds_iff.mp hUL₀ with ⟨UL, hULsub, hULopen, hULzero⟩
  rcases mem_nhds_iff.mp hUR₀ with ⟨UR, hURsub, hURopen, hURone⟩
  refine ⟨UL, UR, hULopen, hULzero, hURopen, hURone, ?_⟩
  intro y hyL hyR
  have hyV : (y.left, y.right) ∈ V :=
    hprod (show (y.left, y.right) ∈ UL₀ ×ˢ UR₀ from ⟨hULsub hyL, hURsub hyR⟩)
  have hyUpre : y ∈
      (fun a : ZCCompletedFoxSemidirect C X H => (a.left, a.right)) ⁻¹' V := hyV
  simpa [hVeq] using hyUpre

end RectangularNeighbourhoods

section BifilteredZCStandardTopology

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {J : Type v} [Preorder J]
variable (Nstage : J → Subgroup (FreeGroup X)) [∀ j, (Nstage j).Normal]
variable (nstage : J → ℕ) [∀ j, Fact (0 < nstage j)]
variable (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
variable (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
variable (zcIndex : J → ZCCompletedGroupAlgebraIndex C H)
variable (hzcIndex : ∀ {i j : J}, i ≤ j → zcIndex i ≤ zcIndex j)
variable (hmod : ∀ j : J, nstage j ∣ (zcIndex j).1.modulus)
variable (qmap : ∀ j : J,
  CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2 →*
    foxAlgebraicStageTargetQuotient (X := X) (Nstage j))

omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/--
Standard-topology form of the componentwise kernel-basis theorem for actual
\(\mathbb{Z}_C\llbracket H\rrbracket\) bifiltered finite stages.
-/
theorem freeProCZCFoxSemiZCBifilteredStageMap_identity_basis_of_component_bases_standardTopology
    (hdir : Directed (· ≤ ·) (id : J → J))
    (hcoeff_mod : ∀ {i j : J} (hij : i ≤ j),
      ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
        modNCompletedCoeffMap
            (n := nstage i) (m := (zcIndex i).1.modulus) (hmod i)
            (modNCompletedCoeffMap
              (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
              (hzcIndex hij).1 a) =
          modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hn hij)
            (modNCompletedCoeffMap
              (n := nstage j) (m := (zcIndex j).1.modulus) (hmod j) a))
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := C) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    (hleft_basis :
      HasAdditiveIdentityQuotientKernelNeighbourhoodBasis
        (A := ZCFreeFoxCoordinates C (X := X) (H := H))
        (fun j : J =>
          zcFreeFoxCoordinatesBifilteredStageMap
            (C := C) (X := X) (H := H) Nstage nstage
            (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
              (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k) j))
    (hright_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := H)
        (fun j : J =>
          zcCompletedGroupAlgebraBifilteredStageRightMap
            (C := C) (X := X) (H := H) Nstage zcIndex qmap j)) :
    HasIdentityQuotientKernelNeighbourhoodBasis
      (Y := ZCCompletedFoxSemidirect C X H)
      (fun j : J =>
        freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
          (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j) := by
  exact
    freeProCZCFoxSemiZCBifilteredStageMap_identity_basis_of_component_bases
      (C := C) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
      hmod qmap
      (zcCompletedFoxSemidirect_hasRectangularIdentityNeighbourhoods
        (C := C) X H)
      hdir hcoeff_mod hqmap_transition hleft_basis hright_basis


omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/--
Standard-topology additive kernel basis for completed Fox coordinates, reduced to the
coefficient-ring kernel basis. For finite Fox coordinate families, product neighborhoods give
the coordinate rectangles needed for the coordinate-kernel theorem.
-/
theorem zcFreeFoxCoordinatesBifilteredStageMap_additive_basis_of_coeff_basis_standardTopology
    [Finite X] [Nonempty J]
    (hdir : Directed (· ≤ ·) (id : J → J))
    (hcoeff_mod : ∀ {i j : J} (hij : i ≤ j),
      ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
        modNCompletedCoeffMap
            (n := nstage i) (m := (zcIndex i).1.modulus) (hmod i)
            (modNCompletedCoeffMap
              (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
              (hzcIndex hij).1 a) =
          modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hn hij)
            (modNCompletedCoeffMap
              (n := nstage j) (m := (zcIndex j).1.modulus) (hmod j) a))
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := C) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    (hcoeff_basis :
      HasAdditiveIdentityQuotientKernelNeighbourhoodBasis
        (A := ZCCompletedGroupAlgebra C H)
        (fun j : J =>
          (zcCompletedGroupAlgebraBifilteredStageCoeffMap
            (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j).toAddMonoidHom)) :
    HasAdditiveIdentityQuotientKernelNeighbourhoodBasis
      (A := ZCFreeFoxCoordinates C (X := X) (H := H))
      (fun j : J =>
        zcFreeFoxCoordinatesBifilteredStageMap
          (C := C) (X := X) (H := H) Nstage nstage
          (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
            (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k) j) := by
  exact
    zcFreeFoxCoordinatesBifilteredStageMap_additive_basis_of_coeff_basis
      (C := C) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
      hmod qmap
      (zcFreeFoxCoordinates_hasFiniteCoordinateZeroRectangularNeighbourhoods
        (C := C) X H)
      hdir hcoeff_mod hqmap_transition hcoeff_basis

omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/--
The semidirect kernel basis for the standard topology from coefficient and target component
bases. This is the componentwise kernel-basis theorem with the left coordinate basis built
internally from the coefficient maps \(\mathbb{Z}_C\llbracket H\rrbracket \to
(\mathbb{Z}/n_j\mathbb{Z})[F/N_j]\).
-/
theorem semiZCBiStageMap_identityBasis_of_coeff_rightBases
    [Finite X] [Nonempty J]
    (hdir : Directed (· ≤ ·) (id : J → J))
    (hcoeff_mod : ∀ {i j : J} (hij : i ≤ j),
      ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
        modNCompletedCoeffMap
            (n := nstage i) (m := (zcIndex i).1.modulus) (hmod i)
            (modNCompletedCoeffMap
              (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
              (hzcIndex hij).1 a) =
          modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hn hij)
            (modNCompletedCoeffMap
              (n := nstage j) (m := (zcIndex j).1.modulus) (hmod j) a))
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := C) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    (hcoeff_basis :
      HasAdditiveIdentityQuotientKernelNeighbourhoodBasis
        (A := ZCCompletedGroupAlgebra C H)
        (fun j : J =>
          (zcCompletedGroupAlgebraBifilteredStageCoeffMap
            (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j).toAddMonoidHom))
    (hright_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := H)
        (fun j : J =>
          zcCompletedGroupAlgebraBifilteredStageRightMap
            (C := C) (X := X) (H := H) Nstage zcIndex qmap j)) :
    HasIdentityQuotientKernelNeighbourhoodBasis
      (Y := ZCCompletedFoxSemidirect C X H)
      (fun j : J =>
        freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
          (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j) := by
  exact
    freeProCZCFoxSemiZCBifilteredStageMap_identity_basis_of_component_bases_standardTopology
      (C := C) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
      hmod qmap hdir hcoeff_mod hqmap_transition
      (zcFreeFoxCoordinatesBifilteredStageMap_additive_basis_of_coeff_basis_standardTopology
        (C := C) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
        hmod qmap hdir hcoeff_mod hqmap_transition hcoeff_basis)
      hright_basis

end BifilteredZCStandardTopology

end

end FoxDifferential
