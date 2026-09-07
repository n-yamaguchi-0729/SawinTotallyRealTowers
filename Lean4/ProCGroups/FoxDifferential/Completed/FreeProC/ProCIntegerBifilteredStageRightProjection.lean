import ProCGroups.FoxDifferential.Completed.FreeProC.ProCIntegerBifilteredStageProjection
import ProCGroups.FoxDifferential.Completed.FreeProC.QuotientKernelBasis

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — pro c integer bifiltered stage right projection

The principal declarations in this module are:

- `zcCompletedGroupAlgebraBifilteredStageRightMap`
  The right quotient map attached to a bifiltered \(\mathbb{Z}_C\llbracket H\rrbracket\) stage. It
  is not independent data: it is the quotient map \(H \to H/U_j\) followed by the chosen map \(H/U_j
  \to F/N_j\).
- `zcCompletedGroupAlgebraBifilteredStageQuotientMap`
  The intermediate quotient map \(H \to H/U_j\) used by a bifiltered \(\mathbb{Z}_C\llbracket
  H\rrbracket\) stage. The canonical right map factors through it and then through \(q_j\), exposing
  the finite-quotient neighborhood basis of \(H\).
- `zcCompletedGroupAlgebraBifilteredStageRightMap_apply`
  The bifiltered stage right map sends \(h\) to the chosen map \(q_j\) applied to the class of \(h\)
  in the completed group-algebra quotient at \(j\).
- `zcCompletedGroupAlgebraBifilteredStageQuotientMap_apply`
  The intermediate stage quotient map sends \(h\) to its canonical class in the quotient \(H/U_j\).
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v

section BifilteredRightMaps

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)]
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

/--
The right quotient map attached to a bifiltered \(\mathbb{Z}_C\llbracket H\rrbracket\) stage. It
is not independent data: it is the quotient map \(H \to H/U_j\) followed by the chosen map
\(H/U_j \to F/N_j\).
-/
def zcCompletedGroupAlgebraBifilteredStageRightMap
    (j : J) :
    H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j) where
  toFun h := qmap j (QuotientGroup.mk h)
  map_one' := by
    rw [QuotientGroup.mk_one]
    exact map_one (qmap j)
  map_mul' h₁ h₂ := by
    rw [QuotientGroup.mk_mul]
    exact map_mul (qmap j) _ _

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Preorder J] in
/--
The bifiltered stage right map sends \(h\) to the chosen map \(q_j\) applied to the class of
\(h\) in the completed group-algebra quotient at \(j\).
-/
@[simp]
theorem zcCompletedGroupAlgebraBifilteredStageRightMap_apply
    (j : J) (h : H) :
    zcCompletedGroupAlgebraBifilteredStageRightMap
        (C := C) (X := X) (H := H) Nstage zcIndex qmap j h =
      qmap j (QuotientGroup.mk h) :=
  rfl

/--
The intermediate quotient map \(H \to H/U_j\) used by a bifiltered \(\mathbb{Z}_C\llbracket
H\rrbracket\) stage. The canonical right map factors through it and then through \(q_j\),
exposing the finite-quotient neighborhood basis of \(H\).
-/
def zcCompletedGroupAlgebraBifilteredStageQuotientMap
    (j : J) :
    H →* CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2 :=
  openNormalSubgroupInClassProj
    (C := C) (G := H) (zcIndex j).2

omit [Preorder J] in
/--
The intermediate stage quotient map sends \(h\) to its canonical class in the quotient
\(H/U_j\).
-/
@[simp]
theorem zcCompletedGroupAlgebraBifilteredStageQuotientMap_apply
    (j : J) (h : H) :
    zcCompletedGroupAlgebraBifilteredStageQuotientMap
        (C := C) (H := H) (zcIndex := zcIndex) j h =
      QuotientGroup.mk h :=
  rfl

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Preorder J] in
/-- The automatically defined right map is \(qmap\) after the underlying \(H/U_j\) quotient map. -/
theorem zcCompletedGroupAlgebraBifilteredStageRightMap_eq_comp_stageQuotientMap
    (j : J) :
    zcCompletedGroupAlgebraBifilteredStageRightMap
        (C := C) (X := X) (H := H) Nstage zcIndex qmap j =
      (qmap j).comp
        (zcCompletedGroupAlgebraBifilteredStageQuotientMap
          (C := C) (H := H) (zcIndex := zcIndex) j) := by
  ext h
  rfl

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Preorder J] in
/--
The kernels of the underlying quotient maps \(H \to H/U_j\) form an identity-neighborhood basis.
-/
theorem zcCompletedGABifilteredStageRightMap_identity_basis_of_stageQuotient_basis
    (hquotient_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := H)
        (fun j : J =>
          zcCompletedGroupAlgebraBifilteredStageQuotientMap
            (C := C) (H := H) (zcIndex := zcIndex) j))
    (hqmap_injective : ∀ j : J, Function.Injective (qmap j)) :
    HasIdentityQuotientKernelNeighbourhoodBasis
      (Y := H)
      (fun j : J =>
        zcCompletedGroupAlgebraBifilteredStageRightMap
          (C := C) (X := X) (H := H) Nstage zcIndex qmap j) := by
  intro U hU hUone
  rcases hquotient_basis U hU hUone with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  intro h hh
  have hh_eq :
      zcCompletedGroupAlgebraBifilteredStageRightMap
          (C := C) (X := X) (H := H) Nstage zcIndex qmap j h = 1 := by
    simpa [MonoidHom.mem_ker] using hh
  have hq :
      zcCompletedGroupAlgebraBifilteredStageQuotientMap
          (C := C) (H := H) (zcIndex := zcIndex) j h = 1 := by
    apply hqmap_injective j
    simpa [zcCompletedGroupAlgebraBifilteredStageRightMap_eq_comp_stageQuotientMap]
      using hh_eq
  exact hj h (by simpa [MonoidHom.mem_ker] using hq)

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Preorder J] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/--
The group-like formula for coefficient maps, with the right map defined from the same
\(\mathbb{Z}_C\llbracket H\rrbracket\) stage quotient.
-/
theorem zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_autoRight
    (j : J) (h : H) :
    zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j
        (zcGroupLike C H h) =
      MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
        (foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
        (zcCompletedGroupAlgebraBifilteredStageRightMap
          (C := C) (X := X) (H := H) Nstage zcIndex qmap j h) := by
  rw [zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike]
  rfl

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] in
/--
Transition compatibility of the quotient maps induces transition compatibility of the right maps
out of the \(\mathbb{Z}_C\llbracket H\rrbracket\) stage quotients.
-/
theorem zcCompletedGroupAlgebraBifilteredStageRightMap_transition
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := C) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    {i j : J} (hij : i ≤ j) (h : H) :
    foxAlgebraicStageTargetQuotientMap (X := X) (hN hij)
        (zcCompletedGroupAlgebraBifilteredStageRightMap
          (C := C) (X := X) (H := H) Nstage zcIndex qmap j h) =
      zcCompletedGroupAlgebraBifilteredStageRightMap
        (C := C) (X := X) (H := H) Nstage zcIndex qmap i h := by
  change
    foxAlgebraicStageTargetQuotientMap (X := X) (hN hij)
        (qmap j (QuotientGroup.mk h :
          CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2)) =
      qmap i (QuotientGroup.mk h :
        CompletedGroupAlgebraQuotientInClass H C (zcIndex i).2)
  have hmap :
      OpenNormalSubgroupInClass.map
          (C := C) (G := H)
          (U := OrderDual.ofDual (zcIndex i).2)
          (V := OrderDual.ofDual (zcIndex j).2)
          (hzcIndex hij).2
          (QuotientGroup.mk h :
            CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2) =
        (QuotientGroup.mk h :
          CompletedGroupAlgebraQuotientInClass H C (zcIndex i).2) := by
    rfl
  exact
    (hqmap_transition hij
      (QuotientGroup.mk h :
        CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2)).symm.trans
      (congrArg (qmap i) hmap)


omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] in
/-- Homomorphism-level transition compatibility for the automatically defined right maps. -/
theorem zcCompletedGroupAlgebraBifilteredStageRightMap_transition_hom
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := C) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    {i j : J} (hij : i ≤ j) :
    (foxAlgebraicStageTargetQuotientMap (X := X) (hN hij)).comp
        (zcCompletedGroupAlgebraBifilteredStageRightMap
          (C := C) (X := X) (H := H) Nstage zcIndex qmap j) =
      zcCompletedGroupAlgebraBifilteredStageRightMap
        (C := C) (X := X) (H := H) Nstage zcIndex qmap i := by
  ext h
  exact zcCompletedGroupAlgebraBifilteredStageRightMap_transition
    (C := C) (X := X) (H := H) (Nstage := Nstage) (hN := hN)
    (zcIndex := zcIndex) (hzcIndex := hzcIndex) (qmap := qmap)
    hqmap_transition hij h

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Preorder J] in
/-- Generator formula for the automatically defined right map. -/
theorem zcCompletedGroupAlgebraBifilteredStageRightMap_generators
    {φ : X → H}
    (hgenerators : ∀ j : J, ∀ x : X,
      qmap j (QuotientGroup.mk (φ x)) =
        QuotientGroup.mk' (Nstage j) (FreeGroup.of x))
    (j : J) (x : X) :
    zcCompletedGroupAlgebraBifilteredStageRightMap
        (C := C) (X := X) (H := H) Nstage zcIndex qmap j (φ x) =
      QuotientGroup.mk' (Nstage j) (FreeGroup.of x) := by
  exact hgenerators j x

/--
The completed-to-finite semidirect stage map with both coordinates produced from the same
\(\mathbb{Z}_C\llbracket H\rrbracket\) stage projection data.
-/
def freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
    (j : J) :
    ZCCompletedFoxSemidirect C X H →*
      FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j) :=
  freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
    (C := C) (X := X) (H := H) Nstage nstage
    (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
      (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
    (zcCompletedGroupAlgebraBifilteredStageRightMap
      (C := C) (X := X) (H := H) Nstage zcIndex qmap)
    (fun k h => zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_autoRight
      (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k h)
    j

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Preorder J] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/--
The left component of the \(\mathbb{Z}_C\)-bifiltered semidirect stage map is the corresponding
finite Fox coordinate projection.
-/
@[simp]
theorem freeProCZCCompletedFoxSemidirectZCBifilteredStageMap_left
    (j : J) (y : ZCCompletedFoxSemidirect C X H) :
    (freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j y).left =
      zcFreeFoxCoordinatesBifilteredStageMap
        (C := C) (X := X) (H := H) Nstage nstage
        (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
          (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
        j y.left :=
  rfl

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Preorder J] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/--
The right coordinate of the \(\mathbb{Z}_C\)-bifiltered completed Fox semidirect stage map is
the selected target quotient map.
-/
@[simp]
theorem freeProCZCCompletedFoxSemidirectZCBifilteredStageMap_right
    (j : J) (y : ZCCompletedFoxSemidirect C X H) :
    (freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j y).right =
      zcCompletedGroupAlgebraBifilteredStageRightMap
        (C := C) (X := X) (H := H) Nstage zcIndex qmap j y.right :=
  rfl

omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] [TopologicalSpace
    (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/-- The transition law for the automatically defined completed-to-finite semidirect maps. -/
theorem freeProCZCCompletedFoxSemidirectZCBifilteredStageMap_transition
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
    {i j : J} (hij : i ≤ j) :
    (foxAlgebraicStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp
      (freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j) =
    freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
      (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap i := by
  exact
    freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff_transition
      (C := C) (X := X) (H := H) Nstage nstage hN hn
      (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
      (zcCompletedGroupAlgebraBifilteredStageRightMap
        (C := C) (X := X) (H := H) Nstage zcIndex qmap)
      (fun k h => zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_autoRight
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k h)
      (fun hij a => zcCompletedGroupAlgebraBifilteredStageCoeffMap_transition
        (C := C) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex hmod qmap
        hcoeff_mod hqmap_transition hij a)
      (fun hij h => zcCompletedGroupAlgebraBifilteredStageRightMap_transition
        (C := C) (X := X) (H := H) (Nstage := Nstage) (hN := hN)
        (zcIndex := zcIndex) (hzcIndex := hzcIndex) (qmap := qmap) hqmap_transition hij h)
      hij


/--
The canonical \(\mathbb{Z}_C\llbracket H\rrbracket\) bifiltered stage maps assembled into the
finite semidirect inverse limit.
-/
def freeProCZCCompletedFoxSemidirectZCBifilteredLimitMap
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
          foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (qmap j q)) :
    ZCCompletedFoxSemidirect C X H →*
      FoxAlgebraicStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn :=
  freeProCZCCompletedFoxSemidirectBifilteredLimitMap
    (C := C) (X := X) (H := H) Nstage nstage hN hn
    (fun j => freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
      (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j)
    (fun hij => freeProCZCCompletedFoxSemidirectZCBifilteredStageMap_transition
      (C := C) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
      hmod qmap hcoeff_mod hqmap_transition hij)

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
Projection after the free pro-\(C\) \(\mathbb{Z}_C\)-completed Fox semidirect
\(\mathbb{Z}_C\)-bifiltered limit map is computed by the finite-stage coordinate map.
-/
@[simp 900]
theorem freeProCZCCompletedFoxSemidirectZCBifilteredLimitMap_projection
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
    (j : J) (y : ZCCompletedFoxSemidirect C X H) :
    foxAlgebraicStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j
        (freeProCZCCompletedFoxSemidirectZCBifilteredLimitMap
          (C := C) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
          hmod qmap hcoeff_mod hqmap_transition y) =
      freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j y :=
  rfl

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
Completed density from actual \(\mathbb{Z}_C\llbracket H\rrbracket\) finite-stage projections,
with the right maps constructed from the same stage quotients rather than passed as separate
data.
-/
theorem boundaryCycles_subset_kernelClosure_of_zcBiStageProj
    [Fintype X] (φ : X → H)
    (hgenerators : ∀ j : J, ∀ x : X,
      qmap j (QuotientGroup.mk (φ x)) =
        QuotientGroup.mk' (Nstage j) (FreeGroup.of x))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
            (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_zcBiStageProj_relDeriv
      (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap φ
      (zcCompletedGroupAlgebraBifilteredStageRightMap
        (C := C) (X := X) (H := H) Nstage zcIndex qmap)
      (fun _ _ => rfl)
      (fun j x => zcCompletedGroupAlgebraBifilteredStageRightMap_generators
        (C := C) (X := X) (H := H) (Nstage := Nstage)
        (zcIndex := zcIndex) (qmap := qmap) hgenerators j x)
      hidentity_basis hNstage_kernel

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
Completed graph-word density from actual \(\mathbb{Z}_C\llbracket H\rrbracket\) projections and
automatic right maps. This is the auto-right analogue of the graph-word density route; it
removes the unsafe completed kernel-word hypothesis from the finite-stage approximation step.
-/
theorem boundaryCycles_subset_graphWordClosure_of_zcBiStageProj
    [Fintype X] (φ : X → H)
    (hgenerators : ∀ j : J, ∀ x : X,
      qmap j (QuotientGroup.mk (φ x)) =
        QuotientGroup.mk' (Nstage j) (FreeGroup.of x))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
            (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j)) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectGraphWordSet (C := C) φ) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_zcBiStageProj_relDeriv
      (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap φ
      (zcCompletedGroupAlgebraBifilteredStageRightMap
        (C := C) (X := X) (H := H) Nstage zcIndex qmap)
      (fun _ _ => rfl)
      (fun j x => zcCompletedGroupAlgebraBifilteredStageRightMap_generators
        (C := C) (X := X) (H := H) (Nstage := Nstage)
        (zcIndex := zcIndex) (qmap := qmap) hgenerators j x)
      hidentity_basis

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
Closed-generated target membership from actual \(\mathbb{Z}_C\llbracket H\rrbracket\)
projections and automatic right maps, via graph-word density.
-/
theorem boundaryCycles_subset_closedGenTarget_of_zcBiGraph
    [Fintype X] (φ : X → H)
    (hgenerators : ∀ j : J, ∀ x : X,
      qmap j (QuotientGroup.mk (φ x)) =
        QuotientGroup.mk' (Nstage j) (FreeGroup.of x))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
            (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j)) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_graphWord_density (C := C) φ
      (boundaryCycles_subset_graphWordClosure_of_zcBiStageProj
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap φ
        hgenerators hidentity_basis)

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
Closed-generated target membership from actual \(\mathbb{Z}_C\llbracket H\rrbracket\)
projections and automatic right maps.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_zcBiStageProj_autoRight_relDeriv
    [Fintype X] (φ : X → H)
    (hgenerators : ∀ j : J, ∀ x : X,
      qmap j (QuotientGroup.mk (φ x)) =
        QuotientGroup.mk' (Nstage j) (FreeGroup.of x))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
            (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density (C := C) φ
      (boundaryCycles_subset_kernelClosure_of_zcBiStageProj
        (C := C) (X := X) (H := H) Nstage nstage zcIndex hmod qmap φ
        hgenerators hidentity_basis hNstage_kernel)

end BifilteredRightMaps

end

end FoxDifferential
