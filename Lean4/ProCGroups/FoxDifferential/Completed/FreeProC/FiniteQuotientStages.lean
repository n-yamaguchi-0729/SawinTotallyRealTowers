import ProCGroups.FoxDifferential.Completed.FreeProC.ProCIntegerBifilteredStageRightProjection
import ProCGroups.FiniteGeneration.Basic

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — finite quotient stages

The principal declarations in this module are:

- `freeProCFiniteQuotientStageHom`
  The free-group map to a finite quotient of H induced by a family X \(\to\) H.
- `freeProCFiniteQuotientStageKernel`
  The finite-stage relation subgroup \(\ker(F_X \to H/U)\).
- `freeProCFiniteQuotientStageHom_of`
  The finite-quotient stage homomorphism for a free pro-\(C\) group has the stated value on
  representatives.
- `freeProCFiniteQuotientStageHom_eq_comp`
  The free quotient-stage map is the quotient projection after the original free-group map.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC
open ProCGroups.Completion

universe u v

section OneStage

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable {X H : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The free-group map to a finite quotient of H induced by a family X \(\to\) H. -/
def freeProCFiniteQuotientStageHom
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C) :
    FreeGroup X →* CompletedGroupAlgebraQuotientInClass H C U :=
  FreeGroup.lift fun x : X =>
    openNormalSubgroupInClassProj (C := C) (G := H) U (φ x)

/--
The finite-quotient stage homomorphism for a free pro-\(C\) group has the stated value on
representatives.
-/
@[simp]
theorem freeProCFiniteQuotientStageHom_of
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C) (x : X) :
    freeProCFiniteQuotientStageHom (C := C) φ U (FreeGroup.of x) =
      (QuotientGroup.mk (φ x) :
        CompletedGroupAlgebraQuotientInClass H C U) := by
  change
    FreeGroup.lift
        (fun y : X =>
          QuotientGroup.mk'
            (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H) (φ y))
        (FreeGroup.of x) =
      QuotientGroup.mk'
        (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H) (φ x)
  exact FreeGroup.lift_apply_of

/-- The free quotient-stage map is the quotient projection after the original free-group map. -/
theorem freeProCFiniteQuotientStageHom_eq_comp
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C) :
    freeProCFiniteQuotientStageHom (C := C) φ U =
      (openNormalSubgroupInClassProj (C := C) (G := H) U).comp (FreeGroup.lift φ) := by
  ext x
  change
    FreeGroup.lift
        (fun y : X =>
          QuotientGroup.mk'
            (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H) (φ y))
        (FreeGroup.of x) =
      QuotientGroup.mk'
        (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H)
        (FreeGroup.lift φ (FreeGroup.of x))
  exact
    (FreeGroup.lift_apply_of
      (f := fun y : X =>
        QuotientGroup.mk'
          (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H) (φ y))).trans
      (congrArg
        (QuotientGroup.mk'
          (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H))
        (FreeGroup.lift_apply_of (f := φ)).symm)

/-- Compatibility of finite quotient-stage maps under quotient refinement. -/
theorem freeProCFiniteQuotientStageHom_transition
    (φ : X → H) {U V : CompletedGroupAlgebraIndexInClass H C} (hUV : U ≤ V)
    (w : FreeGroup X) :
    (OpenNormalSubgroupInClass.map
      (C := C) (G := H)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (freeProCFiniteQuotientStageHom (C := C) φ V w) =
      freeProCFiniteQuotientStageHom (C := C) φ U w := by
  rw [freeProCFiniteQuotientStageHom_eq_comp,
    freeProCFiniteQuotientStageHom_eq_comp]
  exact congrFun
    (openNormalSubgroupInClassProj_compatible (C := C) (G := H) U V hUV)
    (FreeGroup.lift φ w)

/-- The finite-stage relation subgroup \(\ker(F_X \to H/U)\). -/
def freeProCFiniteQuotientStageKernel
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C) :
    Subgroup (FreeGroup X) :=
  (freeProCFiniteQuotientStageHom (C := C) φ U).ker

/-- The finite-stage relation kernel is a normal subgroup. -/
instance freeProCFiniteQuotientStageKernel_normal
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C) :
    (freeProCFiniteQuotientStageKernel (C := C) φ U).Normal := by
  dsimp [freeProCFiniteQuotientStageKernel]
  infer_instance

/-- The finite-stage relation kernels are antitone with respect to quotient refinement. -/
theorem freeProCFiniteQuotientStageKernel_antitone
    (φ : X → H) {U V : CompletedGroupAlgebraIndexInClass H C} (hUV : U ≤ V) :
    freeProCFiniteQuotientStageKernel (C := C) φ V ≤
      freeProCFiniteQuotientStageKernel (C := C) φ U := by
  intro w hw
  change freeProCFiniteQuotientStageHom (C := C) φ U w = 1
  have htransition :
      freeProCFiniteQuotientStageHom (C := C) φ U w =
        (OpenNormalSubgroupInClass.map
          (C := C) (G := H)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
          (freeProCFiniteQuotientStageHom (C := C) φ V w) :=
    (freeProCFiniteQuotientStageHom_transition (C := C) φ hUV w).symm
  have hmapped :
      (OpenNormalSubgroupInClass.map
        (C := C) (G := H)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (freeProCFiniteQuotientStageHom (C := C) φ V w) = 1 := by
    rw [show freeProCFiniteQuotientStageHom (C := C) φ V w = 1 from hw]
    exact map_one _
  exact htransition.trans hmapped

/--
If the original family topologically generates \(H\), then its image generates every discrete
finite quotient \(H/U\), so the corresponding free-group map is surjective.
-/
theorem freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C)
    [DiscreteTopology (CompletedGroupAlgebraQuotientInClass H C U)]
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U) := by
  let π : H →ₜ* CompletedGroupAlgebraQuotientInClass H C U :=
    { toMonoidHom := openNormalSubgroupInClassProj (C := C) (G := H) U
      continuous_toFun := by
        change Continuous
          (QuotientGroup.mk'
            (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H))
        exact continuous_quotient_mk' }
  have hπsurj : Function.Surjective π :=
    openNormalSubgroupInClassProj_surjective (C := C) (G := H) U
  have hgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := CompletedGroupAlgebraQuotientInClass H C U)
        (Set.range (π ∘ φ)) :=
    ProCGroups.FiniteGeneration.topologicallyGenerates_range_comp_of_surjective
      (G := H) (H := CompletedGroupAlgebraQuotientInClass H C U)
      π hπsurj φ hφgen
  change Function.Surjective (FreeGroup.lift fun x : X => π (φ x))
  exact
    ProCGroups.FiniteGeneration.freeGroup_lift_surjective_of_topologicallyGenerates_discrete
      (G := CompletedGroupAlgebraQuotientInClass H C U)
      (g := fun x : X => π (φ x)) hgen

/-- The canonical identification \(F_X / \ker(F_X \to H/U) \simeq H/U\). -/
def freeProCFiniteQuotientStageTargetEquiv
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C)
    (hsurj : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U)) :
    foxAlgebraicStageTargetQuotient
        (X := X) (freeProCFiniteQuotientStageKernel (C := C) φ U) ≃*
      CompletedGroupAlgebraQuotientInClass H C U :=
  QuotientGroup.quotientKerEquivOfSurjective
    (freeProCFiniteQuotientStageHom (C := C) φ U) hsurj

/--
The finite-quotient target equivalence sends the class of a free word in the stage quotient to
its image under the corresponding finite-stage homomorphism.
-/
@[simp]
theorem freeProCFiniteQuotientStageTargetEquiv_mk
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C)
    (hsurj : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U))
    (w : FreeGroup X) :
    freeProCFiniteQuotientStageTargetEquiv (C := C) φ U hsurj
        (QuotientGroup.mk'
          (freeProCFiniteQuotientStageKernel (C := C) φ U) w) =
      freeProCFiniteQuotientStageHom (C := C) φ U w := by
  rfl

/--
The finite quotient stage map sends a target quotient class into the corresponding free-group
quotient stage through the inverse of the target equivalence.
-/
def freeProCFiniteQuotientStageQMap
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C)
    (hsurj : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U)) :
    CompletedGroupAlgebraQuotientInClass H C U →*
      foxAlgebraicStageTargetQuotient
        (X := X) (freeProCFiniteQuotientStageKernel (C := C) φ U) :=
  (freeProCFiniteQuotientStageTargetEquiv (C := C) φ U hsurj).symm.toMonoidHom

/-- The finite-quotient stage quotient map is injective. -/
theorem freeProCFiniteQuotientStageQMap_injective
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C)
    (hsurj : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U)) :
    Function.Injective (freeProCFiniteQuotientStageQMap (C := C) φ U hsurj) :=
  (freeProCFiniteQuotientStageTargetEquiv (C := C) φ U hsurj).symm.injective

/-- The finite-quotient stage quotient map sends each generator to its quotient-stage image. -/
@[simp]
theorem freeProCFiniteQuotientStageQMap_generator
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C)
    (hsurj : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U))
    (x : X) :
    freeProCFiniteQuotientStageQMap (C := C) φ U hsurj
        (QuotientGroup.mk (φ x)) =
      QuotientGroup.mk'
        (freeProCFiniteQuotientStageKernel (C := C) φ U) (FreeGroup.of x) := by
  let e := freeProCFiniteQuotientStageTargetEquiv (C := C) φ U hsurj
  apply e.injective
  change
    e (e.symm (QuotientGroup.mk (φ x))) =
      e (QuotientGroup.mk'
        (freeProCFiniteQuotientStageKernel (C := C) φ U) (FreeGroup.of x))
  have hroundtrip :
      e (e.symm (QuotientGroup.mk (φ x))) =
        (QuotientGroup.mk (φ x) : CompletedGroupAlgebraQuotientInClass H C U) :=
    e.apply_symm_apply _
  have hgenerator :
      (QuotientGroup.mk (φ x) : CompletedGroupAlgebraQuotientInClass H C U) =
        freeProCFiniteQuotientStageHom (C := C) φ U (FreeGroup.of x) :=
    (freeProCFiniteQuotientStageHom_of (C := C) φ U x).symm
  have hequivalence :
      freeProCFiniteQuotientStageHom (C := C) φ U (FreeGroup.of x) =
        e (QuotientGroup.mk'
          (freeProCFiniteQuotientStageKernel (C := C) φ U) (FreeGroup.of x)) :=
    (freeProCFiniteQuotientStageTargetEquiv_mk (C := C) φ U hsurj
      (FreeGroup.of x)).symm
  exact hroundtrip.trans (hgenerator.trans hequivalence)

/--
The compatibility between the canonical \(F_X/kernel \to H/U\) equivalences and quotient
refinement.
-/
theorem freeProCFiniteQuotientStageTargetEquiv_transition
    (φ : X → H) {U V : CompletedGroupAlgebraIndexInClass H C} (hUV : U ≤ V)
    (hsurjU : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U))
    (hsurjV : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ V))
    (y : foxAlgebraicStageTargetQuotient
      (X := X) (freeProCFiniteQuotientStageKernel (C := C) φ V)) :
    freeProCFiniteQuotientStageTargetEquiv (C := C) φ U hsurjU
        (foxAlgebraicStageTargetQuotientMap
          (X := X) (freeProCFiniteQuotientStageKernel_antitone (C := C) φ hUV) y) =
      (OpenNormalSubgroupInClass.map
        (C := C) (G := H)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (freeProCFiniteQuotientStageTargetEquiv (C := C) φ V hsurjV y) := by
  rcases QuotientGroup.mk'_surjective
      (freeProCFiniteQuotientStageKernel (C := C) φ V) y with ⟨w, rfl⟩
  rw [foxAlgebraicStageTargetQuotientMap_mk,
    freeProCFiniteQuotientStageTargetEquiv_mk,
    freeProCFiniteQuotientStageTargetEquiv_mk,
    freeProCFiniteQuotientStageHom_transition]

/-- The canonical quotient maps commute with quotient refinement. -/
theorem freeProCFiniteQuotientStageQMap_transition
    (φ : X → H) {U V : CompletedGroupAlgebraIndexInClass H C} (hUV : U ≤ V)
    (hsurjU : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U))
    (hsurjV : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ V))
    (q : CompletedGroupAlgebraQuotientInClass H C V) :
    freeProCFiniteQuotientStageQMap (C := C) φ U hsurjU
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := H)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) =
      foxAlgebraicStageTargetQuotientMap
        (X := X) (freeProCFiniteQuotientStageKernel_antitone (C := C) φ hUV)
        (freeProCFiniteQuotientStageQMap (C := C) φ V hsurjV q) := by
  let eU := freeProCFiniteQuotientStageTargetEquiv (C := C) φ U hsurjU
  let eV := freeProCFiniteQuotientStageTargetEquiv (C := C) φ V hsurjV
  let m : CompletedGroupAlgebraQuotientInClass H C V →*
      CompletedGroupAlgebraQuotientInClass H C U :=
    OpenNormalSubgroupInClass.map
      (C := C) (G := H)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV
  apply eU.injective
  change
    eU (eU.symm (m q)) =
      eU (foxAlgebraicStageTargetQuotientMap
        (X := X) (freeProCFiniteQuotientStageKernel_antitone (C := C) φ hUV)
        (eV.symm q))
  calc
    eU (eU.symm (m q)) = m q := eU.apply_symm_apply _
    _ = m (eV (eV.symm q)) :=
      congrArg (fun y : CompletedGroupAlgebraQuotientInClass H C V => m y)
        (eV.apply_symm_apply q).symm
    _ = eU (foxAlgebraicStageTargetQuotientMap
          (X := X) (freeProCFiniteQuotientStageKernel_antitone (C := C) φ hUV)
          (eV.symm q)) :=
      (freeProCFiniteQuotientStageTargetEquiv_transition
        (C := C) φ hUV hsurjU hsurjV (eV.symm q)).symm

end OneStage

section StageFamily

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable {X H : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {J : Type v}

/--
The finite relation subgroup family attached to a family of \(\mathbb{Z}_C\llbracket
H\rrbracket\) stage indices.
-/
def freeProCFiniteQuotientStageKernelFamily
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H) :
    J → Subgroup (FreeGroup X) :=
  fun j => freeProCFiniteQuotientStageKernel (C := C) φ (zcIndex j).2

/-- The finite-stage relation kernel is a normal subgroup. -/
instance freeProCFiniteQuotientStageKernelFamily_normal
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H) (j : J) :
    (freeProCFiniteQuotientStageKernelFamily (C := C) φ zcIndex j).Normal := by
  dsimp [freeProCFiniteQuotientStageKernelFamily]
  infer_instance

/--
The finite relation subgroup family is antitone under refinement of the \(\mathbb{Z}_C\llbracket
H\rrbracket\) stages.
-/
theorem freeProCFiniteQuotientStageKernelFamily_antitone
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H)
    [Preorder J]
    (hzcIndex : ∀ {i j : J}, i ≤ j → zcIndex i ≤ zcIndex j) :
    ∀ {i j : J}, i ≤ j →
      freeProCFiniteQuotientStageKernelFamily (C := C) φ zcIndex j ≤
        freeProCFiniteQuotientStageKernelFamily (C := C) φ zcIndex i := by
  intro i j hij
  exact freeProCFiniteQuotientStageKernel_antitone (C := C) φ (hzcIndex hij).2

/-- The canonical \(H/U_j \to F/N_j\) comparison maps for a finite quotient stage family. -/
def freeProCFiniteQuotientStageQMapFamily
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H)
    [∀ j, DiscreteTopology (CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2)]
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    ∀ j : J,
      CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2 →*
        foxAlgebraicStageTargetQuotient
          (X := X) (freeProCFiniteQuotientStageKernelFamily (C := C) φ zcIndex j) :=
  fun j =>
    freeProCFiniteQuotientStageQMap (C := C) φ (zcIndex j).2
      (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
        (C := C) φ (zcIndex j).2 hφgen)

/-- The finite-quotient stage family map is injective. -/
theorem freeProCFiniteQuotientStageQMapFamily_injective
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H)
    [∀ j, DiscreteTopology (CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2)]
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    ∀ j : J,
      Function.Injective
        (freeProCFiniteQuotientStageQMapFamily (C := C) φ zcIndex hφgen j) := by
  intro j
  exact freeProCFiniteQuotientStageQMap_injective (C := C) φ (zcIndex j).2
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := C) φ (zcIndex j).2 hφgen)

/-- The finite-quotient stage family sends each generator to its quotient-stage image. -/
@[simp]
theorem freeProCFiniteQuotientStageQMapFamily_generator
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H)
    [∀ j, DiscreteTopology (CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2)]
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ))
    (j : J) (x : X) :
    freeProCFiniteQuotientStageQMapFamily (C := C) φ zcIndex hφgen j
        (QuotientGroup.mk (φ x)) =
      QuotientGroup.mk'
        (freeProCFiniteQuotientStageKernelFamily (C := C) φ zcIndex j)
        (FreeGroup.of x) := by
  exact freeProCFiniteQuotientStageQMap_generator (C := C) φ (zcIndex j).2
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := C) φ (zcIndex j).2 hφgen) x

/--
The canonical comparison maps commute with refinement of the \(\mathbb{Z}_C\llbracket
H\rrbracket\) stage family.
-/
theorem freeProCFiniteQuotientStageQMapFamily_transition
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H)
    [Preorder J]
    (hzcIndex : ∀ {i j : J}, i ≤ j → zcIndex i ≤ zcIndex j)
    [∀ j, DiscreteTopology (CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2)]
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2,
        freeProCFiniteQuotientStageQMapFamily (C := C) φ zcIndex hφgen i
            ((OpenNormalSubgroupInClass.map
              (C := C) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          foxAlgebraicStageTargetQuotientMap
            (X := X)
            (freeProCFiniteQuotientStageKernelFamily_antitone
              (C := C) φ zcIndex hzcIndex hij)
            (freeProCFiniteQuotientStageQMapFamily (C := C) φ zcIndex hφgen j q) := by
  intro i j hij q
  exact freeProCFiniteQuotientStageQMap_transition (C := C) φ (hzcIndex hij).2
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := C) φ (zcIndex i).2 hφgen)
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := C) φ (zcIndex j).2 hφgen)
    q

end StageFamily

section BifilteredFiniteQuotientStages

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)]
variable {J : Type v} [Preorder J]

/--
The completed-to-finite coefficient map for the actual finite quotient stages \(F_X \to H/U_j\).
-/
def freeProCZCBifilteredFiniteQuotientStageCoeffMap
    (φ : X → H) (nstage : J → ℕ)
    (zcIndex : J → ZCCompletedGroupAlgebraIndex C H)
    (hmod : ∀ j : J, nstage j ∣ (zcIndex j).1.modulus)
    [∀ j, DiscreteTopology
      (CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2)]
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ))
    (j : J) :
    ZCCompletedGroupAlgebra C H →+*
      foxAlgebraicStageTargetGroupAlgebra
        (X := X)
        (freeProCFiniteQuotientStageKernelFamily
          (C := C) φ zcIndex j)
        (nstage j) :=
  zcCompletedGroupAlgebraBifilteredStageCoeffMap
    (C := C) (X := X) (H := H)
    (freeProCFiniteQuotientStageKernelFamily
      (C := C) φ zcIndex)
    nstage zcIndex hmod
    (freeProCFiniteQuotientStageQMapFamily
      (C := C) φ zcIndex hφgen) j

/--
The completed-to-finite coefficient map for the standard all-stage family \(j\), a
\(\mathbb{Z}_C\)-completed group-algebra index for \(C\) and \(H\), with finite relation
subgroup \(\ker(F_X \to H/U_j)\) and the specified coefficient modulus.
-/
def freeProCZCBifilteredAllFiniteQuotientStageCoeffMap
    (φ : X → H)
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ))
    (j : ZCCompletedGroupAlgebraIndex C H) :
    ZCCompletedGroupAlgebra C H →+*
      foxAlgebraicStageTargetGroupAlgebra
        (X := X)
        (freeProCFiniteQuotientStageKernelFamily
          (C := C) φ
          (id : ZCCompletedGroupAlgebraIndex C H →
            ZCCompletedGroupAlgebraIndex C H) j)
        j.1.modulus := by
  letI :
      ∀ j : ZCCompletedGroupAlgebraIndex C H,
        Fact (0 < j.1.modulus) :=
    fun j => ProCIntegerIndex.positiveFact j.1
  letI :
      ∀ j : ZCCompletedGroupAlgebraIndex C H,
        DiscreteTopology
          (CompletedGroupAlgebraQuotientInClass H C j.2) :=
    fun j =>
      QuotientGroup.discreteTopology
        (ProCGroups.openNormalSubgroup_isOpen (G := H)
          ((OrderDual.ofDual j.2).1 : OpenNormalSubgroup H))
  exact
    freeProCZCBifilteredFiniteQuotientStageCoeffMap
      (C := C) (X := X) (H := H) φ (fun j => j.1.modulus)
      (id : ZCCompletedGroupAlgebraIndex C H →
        ZCCompletedGroupAlgebraIndex C H)
      (fun _ => dvd_rfl) hφgen j

end BifilteredFiniteQuotientStages

section FullStageQuotientBasis

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable {H : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [IsTopologicalGroup H] in
/-- The full family of quotient maps \(H \to H/U\), indexed by the
\(\mathbb{Z}_C\)-completed group-algebra indices for \(C\) and \(H\), has identity-neighborhood
kernels whenever \(H\) has an open-normal \(C\)-basis. The coefficient coordinate of the index is
unspecified here; it is filled with the terminal coefficient quotient. -/
theorem zcCompletedGroupAlgebraAllStageQuotientMap_identity_basis_of_hasOpenNormalBasisInClass
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hH : HasOpenNormalBasisInClass C H) :
    HasIdentityQuotientKernelNeighbourhoodBasis
      (Y := H)
      (fun j : ZCCompletedGroupAlgebraIndex C H =>
        openNormalSubgroupInClassProj (C := C) (G := H) j.2) := by
  intro U hU hUone
  rcases hH U hU hUone with ⟨V, hVU, hCV⟩
  let Vc : OpenNormalSubgroupInClass C H := ⟨V, hCV⟩
  refine ⟨(ProCIntegerIndex.terminal (C := C) inferInstance, OrderDual.toDual Vc), ?_⟩
  intro z hz
  apply hVU
  exact
    (QuotientGroup.eq_one_iff
      (N := ((V : OpenNormalSubgroup H) : Subgroup H)) z).1 hz

end FullStageQuotientBasis

end

end FoxDifferential
