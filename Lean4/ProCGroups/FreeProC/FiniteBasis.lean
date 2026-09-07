import ProCGroups.FreeProC.Basic

set_option autoImplicit false

/-!
# Free pro-C finite-basis utilities

This module develops the finite-basis interface for
`ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData`.
Its canonical finite index is `ULift (Fin n)`, which lies in the carrier
universe required by the generated-target lifting property. Concrete `Fin n`
displays can be obtained by reindexing with `ULift.up`.
-/

namespace CrowellExactSequence

noncomputable section

open scoped Topology

open ProCGroups.ProC
open ProCGroups.ProC.HasOpenNormalBasisInClass

universe u

/-- Choose an equivalence from a finite epimorphically free pro-\(C\) basis to
\(\operatorname{Fin} n\). -/
def freeProCChosenBasisEquivOfBasisCard
    {C : ProCGroups.FiniteGroupClass.{u}}
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n) :
    sourceData.basis ≃ Fin n :=
  Classical.choice ((Cardinal.mk_eq_nat_iff).1 hbasis)

/-- The canonical chosen finite family.  The universe lift keeps its generator
type in the same universe as the pro-\(C\) carrier. -/
def freeProCChosenULiftFamilyOfBasisCard
    {C : ProCGroups.FiniteGroupClass.{u}}
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n) :
    ULift.{u} (Fin n) → sourceData.carrier :=
  fun i =>
    sourceData.inclusion
      ((freeProCChosenBasisEquivOfBasisCard (C := C) sourceData hbasis).symm i.down)

/-- Reindexing preserves the epimorphically free pro-\(C\) converging-basis property. -/
theorem freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree
    {C : ProCGroups.FiniteGroupClass.{u}}
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n) :
    ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) (ULift.{u} (Fin n)) sourceData.carrier
      (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) := by
  classical
  let e : ULift.{u} (Fin n) ≃ sourceData.basis :=
    { toFun := fun i =>
        (freeProCChosenBasisEquivOfBasisCard (C := C) sourceData hbasis).symm i.down
      invFun := fun b =>
        ULift.up ((freeProCChosenBasisEquivOfBasisCard (C := C) sourceData hbasis) b)
      left_inv := by
        intro i
        cases i
        simp only [Equiv.apply_symm_apply]
      right_inv := by
        intro b
        simp only [Equiv.symm_apply_apply]}
  have : Finite sourceData.basis := Finite.of_equiv (ULift.{u} (Fin n)) e
  apply ProCGroups.FreeProC.finite_generatingFamily_is_basis
      (C := C) sourceData.isEpimorphicallyFree (Cardinal.mk_congr e).symm
  have hRange :
      Set.range (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis) =
        Set.range sourceData.inclusion := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨b, rfl⟩
      refine ⟨e.symm b, ?_⟩
      dsimp [freeProCChosenULiftFamilyOfBasisCard, e]
      rw [Equiv.symm_apply_apply]
  rw [hRange]
  exact sourceData.isEpimorphicallyFree.generates_range

/--
The canonical chosen family topologically generates the epimorphically free pro-\(C\) source.
-/
theorem freeProCChosenULiftFamilyOfBasisCard_generates
    {C : ProCGroups.FiniteGroupClass.{u}}
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n) :
    ProCGroups.Generation.TopologicallyGenerates
      (G := sourceData.carrier)
      (Set.range (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis)) := by
  exact
    (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree
      (C := C) sourceData hbasis).generates_range

/-- The image of the finite lifted basis under any target homomorphism satisfies the
open-subgroup convergence condition used by the epimorphically free pro-\(C\) formulation. -/
theorem freeProCChosenULiftFamilyOfBasisCard_image_convergesToOneAlongOpenSubgroups
    {C : ProCGroups.FiniteGroupClass.{u}}
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n)
    {H : Type u} [Group H] [TopologicalSpace H]
    (ψ : sourceData.carrier →* H) :
    ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
      (G := H)
      (fun i : ULift.{u} (Fin n) =>
        ψ (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis i)) := by
  exact ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain
    (G := H)
    (fun i : ULift.{u} (Fin n) =>
      ψ (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis i))

/-- A surjective continuous homomorphism carries the lifted chosen finite basis to a
topological generating family of the target. -/
theorem freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
    {C : ProCGroups.FiniteGroupClass.{u}}
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (psi : ContinuousMonoidHom sourceData.carrier H) (hpsi : Function.Surjective psi) :
    ProCGroups.Generation.TopologicallyGenerates
      (G := H)
      (Set.range
        (fun i : ULift.{u} (Fin n) =>
          psi (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis i))) := by
  let family : ULift.{u} (Fin n) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis
  have hsourceGen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := sourceData.carrier) (Set.range family) := by
    simpa [family] using
      freeProCChosenULiftFamilyOfBasisCard_generates (C := C) sourceData hbasis
  have himage :=
    ProCGroups.Generation.topologicallyGenerates_image_of_continuousMonoidHom_surjective
      (G := sourceData.carrier) (H := H) psi hpsi hsourceGen
  have hrange :
      psi '' Set.range family = Set.range (fun i => psi (family i)) := by
    ext h
    constructor
    · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨family i, ⟨i, rfl⟩, rfl⟩
  simpa [family, hrange] using himage

/-- For the lifted finite basis, the generated-target lift of a surjective target map is the
target map itself. This is the concrete bridge needed when Fox constructions produce a right
component from the epimorphic lifting property. -/
theorem freeProCChosenULiftFamilyOfBasisCard_liftHom_eq_of_surjective
    {C : ProCGroups.FiniteGroupClass.{u}}
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (psi : ContinuousMonoidHom sourceData.carrier H) (hpsi : Function.Surjective psi) :
    (freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree
      (C := C) sourceData hbasis).liftHom hH
        (fun i : ULift.{u} (Fin n) =>
          psi (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis i))
        (freeProCChosenULiftFamilyOfBasisCard_image_convergesToOneAlongOpenSubgroups
          (C := C) sourceData hbasis psi.toMonoidHom)
        (freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
          (C := C) sourceData hbasis psi hpsi) =
      psi := by
  let hfree :=
    freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree (C := C) sourceData hbasis
  let liftedFamily : ULift.{u} (Fin n) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis
  let φ : ULift.{u} (Fin n) → H := fun i => psi (liftedFamily i)
  let hconv :
      ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups (G := H) φ :=
    by
      simpa [φ, liftedFamily] using
        freeProCChosenULiftFamilyOfBasisCard_image_convergesToOneAlongOpenSubgroups
          (C := C) sourceData hbasis psi.toMonoidHom
  let hgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ) := by
    simpa [φ, liftedFamily] using
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (C := C) sourceData hbasis psi hpsi
  ext g
  have hmon :
      psi.toMonoidHom = hfree.lift hH φ hconv hgen :=
    hfree.lift_unique hH φ hconv hgen psi.continuous_toFun (by
      intro i
      rfl)
  exact (congrArg (fun f : sourceData.carrier →* H => f g) hmon).symm

/--
The chosen lifted finite free basis surjects onto every finite open-normal quotient of the free
pro-\(C\) source.
-/
theorem freeProCChosenULiftFamilyOfBasisCard_quotient_lift_surjective
    {C : ProCGroups.FiniteGroupClass.{u}}
    (sourceData : ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (V : OpenNormalSubgroupInClass C sourceData.carrier) :
    Function.Surjective
      ((QuotientGroup.mk' (V.1 : Subgroup sourceData.carrier)).comp
        (FreeGroup.lift
          (freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis))) := by
  classical
  let X : Type u := ULift.{u} (Fin r)
  let ι : X → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis
  let Q : Type u := sourceData.carrier ⧸ (V.1 : Subgroup sourceData.carrier)
  let : DiscreteTopology Q :=
    QuotientGroup.discreteTopology V.1.toOpenSubgroup.isOpen'
  let g : X → Q :=
    fun i => QuotientGroup.mk' (V.1 : Subgroup sourceData.carrier) (ι i)
  have hsource :
      ProCGroups.Generation.TopologicallyGenerates
        (G := sourceData.carrier) (Set.range ι) := by
    simpa [X, ι] using
      freeProCChosenULiftFamilyOfBasisCard_generates (C := C) sourceData hbasis
  have hquot_image :
      ProCGroups.Generation.TopologicallyGenerates
        (G := Q)
        ((QuotientGroup.mk' (V.1 : Subgroup sourceData.carrier)) '' Set.range ι) :=
    ProCGroups.Generation.topologicallyGenerates_quotient_image
      (G := sourceData.carrier) (N := (V.1 : Subgroup sourceData.carrier)) hsource
  have hrange :
      (QuotientGroup.mk' (V.1 : Subgroup sourceData.carrier)) '' Set.range ι =
        Set.range g := by
    ext y
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ι i, ⟨i, rfl⟩, rfl⟩
  have hg :
      ProCGroups.Generation.TopologicallyGenerates (G := Q) (Set.range g) := by
    rw [← hrange]
    exact hquot_image
  have hsurj :
      Function.Surjective (FreeGroup.lift g) :=
    ProCGroups.FiniteGeneration.freeGroup_lift_surjective_of_topologicallyGenerates_discrete
      (G := Q) g hg
  have hlift :
      FreeGroup.lift g =
        (QuotientGroup.mk' (V.1 : Subgroup sourceData.carrier)).comp
          (FreeGroup.lift ι) := by
    apply FreeGroup.ext_hom
    intro i
    rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, FreeGroup.lift_apply_of]
  simpa [hlift, X, ι] using hsurj

/--
The finite-index lift comparison is an equivalence, with inverse given by the reverse
comparison map.
-/
def finULiftEquiv (r : Nat) : Fin r ≃ ULift.{u} (Fin r) where
  toFun i := ULift.up i
  invFun i := i.down
  left_inv := by
    intro i
    rfl
  right_inv := by
    intro i
    cases i
    rfl

end

end CrowellExactSequence
