import GaloisCohomology.ProP.H2CocycleExtensionSplitting

set_option autoImplicit false
/-!
# Pullback and local lifting for degree-two cocycle extensions

Restriction of a homogeneous degree-two cocycle is evaluated explicitly on
the standard continuous resolution.  The resulting pullback cocycle extension
maps to the original extension, so vanishing of the restricted class produces
an honest continuous lift of the restricting group homomorphism.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CategoryTheory TopRep ContRepresentation
open FreeProPH2Cocycle

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Restriction of a lifted homogeneous degree-two cocycle along a continuous
group homomorphism. -/
noncomputable def pulledBackH2Cocycle
    (f : H →ₜ* G)
    (z : Cohomology.trivialZModPCocyclesLifted p G 2) :
    Cohomology.trivialZModPCocyclesLifted p H 2 :=
  (Cohomology.trivialZModPCocyclesMapLifted p f 2).hom z

omit [Fact p.Prime] in
/-- Restriction evaluates a homogeneous cocycle by applying the base
homomorphism to each argument. -/
theorem pulledBackH2Cocycle_cochain_apply
    (f : H →ₜ* G)
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (x y w : H) :
    (((Cohomology.trivialZModPCochainsLifted p H).iCycles 2).hom
      (pulledBackH2Cocycle f z)).1 x y w =
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1
        (f x) (f y) (f w) := by
  let φ := Cohomology.trivialZModPCochainsMapLifted p f
  change
    (((Cohomology.trivialZModPCochainsLifted p H).iCycles 2).hom
      ((HomologicalComplex.cyclesMap φ 2).hom z)).1 x y w = _
  have hcochain :
      ((Cohomology.trivialZModPCochainsLifted p H).iCycles 2).hom
          ((HomologicalComplex.cyclesMap φ 2).hom z) =
        (φ.f 2).hom
          (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z) := by
    rw [← ConcreteCategory.comp_apply,
      HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  rw [hcochain]
  change
    ((ContinuousCohomology.resolutionMap f
        (Cohomology.trivialZModPRestrictionHomLifted p f) 3).hom
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1)
        x y w = _
  simp only [ContinuousCohomology.resolutionMap_succ,
    TopRep.hom_ofHom, ContRepresentation.coind₁ResMap_apply,
    ContinuousCohomology.resolutionMap_zero]
  rfl

omit [Fact p.Prime] in
/-- Restriction commutes with the degree-two cocycle quotient map. -/
theorem pulledBackH2Cocycle_π
    (f : H →ₜ* G)
    (z : Cohomology.trivialZModPCocyclesLifted p G 2) :
    ContinuousCohomology.π (Cohomology.trivialZModPLifted p H) 2
        (pulledBackH2Cocycle f z) =
      (Cohomology.continuousCohomologyZModPMapLifted p f 2).hom
        (ContinuousCohomology.π
          (Cohomology.trivialZModPLifted p G) 2 z) := by
  have h := ConcreteCategory.congr_hom
    (Cohomology.trivialZModPLifted_π_naturality p f 2) z
  exact h.symm

omit [Fact p.Prime] in
/-- The normalized inhomogeneous cocycle also restricts pointwise. -/
@[simp]
theorem normalizedCocycle_pulledBackH2Cocycle
    (f : H →ₜ* G)
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (g h : H) :
    normalizedCocycle (pulledBackH2Cocycle f z) g h =
      normalizedCocycle z (f g) (f h) := by
  change
    (((Cohomology.trivialZModPCochainsLifted p H).iCycles 2).hom
        (pulledBackH2Cocycle f z)).1 1 g (g * h) -
      (((Cohomology.trivialZModPCochainsLifted p H).iCycles 2).hom
        (pulledBackH2Cocycle f z)).1 1 1 1 =
    (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1
        1 (f g) (f g * f h) -
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 1 1 1
  rw [pulledBackH2Cocycle_cochain_apply f z 1 g (g * h),
    pulledBackH2Cocycle_cochain_apply f z 1 1 1]
  simp only [map_one, map_mul]
  rfl

/-- The pullback cocycle extension maps continuously to the original
extension over the base homomorphism. -/
noncomputable def H2CocycleExtension.pullbackToOriginal
    (f : H →ₜ* G)
    (z : Cohomology.trivialZModPCocyclesLifted p G 2) :
    H2CocycleExtension (pulledBackH2Cocycle f z) →ₜ*
      H2CocycleExtension z where
  toFun x := ⟨x.left, f x.right⟩
  map_one' := by
    apply H2CocycleExtension.ext
    · rfl
    · exact f.map_one
  map_mul' x y := by
    apply H2CocycleExtension.ext
    · exact congrArg (x.left + y.left + ·)
        (normalizedCocycle_pulledBackH2Cocycle f z x.right y.right)
    · exact f.map_mul x.right y.right
  continuous_toFun := by
    rw [continuous_induced_rng]
    change Continuous fun x : H2CocycleExtension (pulledBackH2Cocycle f z) =>
      (x.left, f x.right)
    have hecont : Continuous
        (H2CocycleExtension.toProdEquiv (pulledBackH2Cocycle f z)) :=
      continuous_induced_dom
    exact (continuous_fst.comp hecont).prodMk
      (f.continuous_toFun.comp (continuous_snd.comp hecont))

@[simp]
theorem H2CocycleExtension.projection_comp_pullbackToOriginal
    (f : H →ₜ* G)
    (z : Cohomology.trivialZModPCocyclesLifted p G 2) :
    (H2CocycleExtension.projection z).comp
        (H2CocycleExtension.pullbackToOriginal f z) =
      f.comp (H2CocycleExtension.projection (pulledBackH2Cocycle f z)) :=
  rfl

/-- Vanishing of the pulled-back class produces an explicit continuous lift
of the base homomorphism to the original cocycle extension. -/
theorem H2CocycleExtension.exists_lift_of_pullback_π_eq_zero
    [LocallyCompactSpace H]
    (f : H →ₜ* G)
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (hz : ContinuousCohomology.π
      (Cohomology.trivialZModPLifted p H) 2
        (pulledBackH2Cocycle f z) = 0) :
    ∃ s : H →ₜ* H2CocycleExtension z,
      (H2CocycleExtension.projection z).comp s = f := by
  obtain ⟨t, ht⟩ :=
    H2CocycleExtension.exists_section_of_π_eq_zero
      (pulledBackH2Cocycle f z) hz
  refine ⟨(H2CocycleExtension.pullbackToOriginal f z).comp t, ?_⟩
  ext h
  change f (t h).right = f h
  have hright := congrArg
    (fun q : H →ₜ* H => q h) ht
  exact congrArg f hright

/-- The cohomological restriction being zero is the source-level local
splitting criterion for the original cocycle extension. -/
theorem H2CocycleExtension.exists_lift_of_restriction_eq_zero
    [LocallyCompactSpace H]
    (f : H →ₜ* G)
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (hz : (Cohomology.continuousCohomologyZModPMapLifted p f 2).hom
      (ContinuousCohomology.π
        (Cohomology.trivialZModPLifted p G) 2 z) = 0) :
    ∃ s : H →ₜ* H2CocycleExtension z,
      (H2CocycleExtension.projection z).comp s = f := by
  apply H2CocycleExtension.exists_lift_of_pullback_π_eq_zero f z
  rw [pulledBackH2Cocycle_π]
  exact hz

/-- A continuous lift gives a section of the pullback extension and hence
makes the restricted degree-two class vanish. -/
theorem H2CocycleExtension.restriction_eq_zero_of_lift
    [LocallyCompactSpace H]
    (f : H →ₜ* G)
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (s : H →ₜ* H2CocycleExtension z)
    (hs : (H2CocycleExtension.projection z).comp s = f) :
    (Cohomology.continuousCohomologyZModPMapLifted p f 2).hom
      (ContinuousCohomology.π
        (Cohomology.trivialZModPLifted p G) 2 z) = 0 := by
  have hsright (h : H) : (s h).right = f h := by
    have hpoint := congrArg (fun q : H →ₜ* G => q h) hs
    exact hpoint
  let t : H →ₜ* H2CocycleExtension (pulledBackH2Cocycle f z) :=
    { toFun h := ⟨(s h).left, h⟩
      map_one' := by
        apply H2CocycleExtension.ext
        · change (s 1).left = 0
          exact congrArg (fun x : H2CocycleExtension z => x.left) s.map_one
        · rfl
      map_mul' g h := by
        apply H2CocycleExtension.ext
        · have hmul := congrArg H2CocycleExtension.left (s.map_mul g h)
          change (s (g * h)).left =
            (s g).left + (s h).left +
              normalizedCocycle z (s g).right (s h).right at hmul
          change (s (g * h)).left =
            (s g).left + (s h).left +
              normalizedCocycle (pulledBackH2Cocycle f z) g h
          rw [normalizedCocycle_pulledBackH2Cocycle]
          simpa only [hsright] using hmul
        · rfl
      continuous_toFun := by
        rw [continuous_induced_rng]
        change Continuous fun h : H => ((s h).left, h)
        exact ((continuous_fst.comp
          (H2CocycleExtension.toProdHomeomorph z).continuous).comp
            s.continuous_toFun).prodMk continuous_id }
  have ht :
      (H2CocycleExtension.projection (pulledBackH2Cocycle f z)).comp t =
        ContinuousMonoidHom.id H := rfl
  rw [← pulledBackH2Cocycle_π f z]
  exact H2CocycleExtension.π_eq_zero_of_section
    (pulledBackH2Cocycle f z) t ht

/-- A homomorphism lifts continuously to the cocycle extension exactly when
the corresponding restriction of its degree-two class vanishes. -/
theorem H2CocycleExtension.exists_lift_iff_restriction_eq_zero
    [LocallyCompactSpace H]
    (f : H →ₜ* G)
    (z : Cohomology.trivialZModPCocyclesLifted p G 2) :
    (∃ s : H →ₜ* H2CocycleExtension z,
      (H2CocycleExtension.projection z).comp s = f) ↔
    (Cohomology.continuousCohomologyZModPMapLifted p f 2).hom
      (ContinuousCohomology.π
        (Cohomology.trivialZModPLifted p G) 2 z) = 0 := by
  constructor
  · rintro ⟨s, hs⟩
    exact H2CocycleExtension.restriction_eq_zero_of_lift f z s hs
  · exact H2CocycleExtension.exists_lift_of_restriction_eq_zero f z

end

end ClassFieldTower.ProP
