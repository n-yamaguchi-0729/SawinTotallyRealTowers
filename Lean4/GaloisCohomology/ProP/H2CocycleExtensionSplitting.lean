import GaloisCohomology.ProP.H2CentralExtensionClass
import GaloisCohomology.ProP.FiniteTransgressionKernel

set_option autoImplicit false
/-!
# Splitting a cocycle extension whose degree-two class vanishes

A homogeneous degree-one boundary is converted to a normalized continuous
inhomogeneous primitive.  That primitive gives an explicit continuous group
section of the associated degree-two cocycle extension.  In particular, a
cocycle with zero homology class has a continuous splitting.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CategoryTheory TopRep ContRepresentation
open FreeProPH2Cocycle

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact p.Prime] in
/-- A homogeneous degree-one cochain is invariant under simultaneous left
translation. -/
theorem homogeneousOneCochain_leftInvariant
    (c : (Cohomology.trivialZModPCochainsLifted p G).X 1)
    (a x y : G) :
    c.1 (a⁻¹ * x) (a⁻¹ * y) = c.1 x y := by
  have hc := c.2 a
  have hxy := congrArg (fun tau => tau x y) hc
  have hxy' :
      (Cohomology.trivialZModPLifted p G).ρ a
          (c.1 (a⁻¹ * x) (a⁻¹ * y)) =
        c.1 x y := by
    simpa only [ContRepresentation.coind₁_apply_apply] using hxy
  exact
    (Cohomology.trivialZModPLifted_action p G a _).symm.trans hxy'

/-- The normalized inhomogeneous primitive extracted from a homogeneous
degree-one cochain. -/
def normalizedPrimitiveValue
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (c : (Cohomology.trivialZModPCochainsLifted p G).X 1) :
    C(G, FreeProPH2Cocycle.A p) :=
  ⟨fun g =>
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 1 1 1 -
        c.1 1 g,
    continuous_const.sub (c.1 1).continuous⟩

@[simp]
theorem normalizedPrimitiveValue_apply
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (c : (Cohomology.trivialZModPCochainsLifted p G).X 1)
    (g : G) :
    normalizedPrimitiveValue z c g =
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1 1 1 1 -
        c.1 1 g :=
  rfl

/-- A homogeneous boundary gives the multiplication formula needed for a
section of the associated cocycle extension. -/
theorem normalizedPrimitiveValue_mul
    [LocallyCompactSpace G]
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (c : (Cohomology.trivialZModPCochainsLifted p G).X 1)
    (hc : ((Cohomology.trivialZModPCochainsLifted p G).d 1 2).hom c =
      ((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z)
    (g h : G) :
    normalizedPrimitiveValue z c (g * h) =
      normalizedPrimitiveValue z c g + normalizedPrimitiveValue z c h +
        normalizedCocycle z g h := by
  let X := Cohomology.trivialZModPLifted p G
  have hd := TopRep.homogeneousCochains.d_apply X 1 c
  have hdpoint := congrArg (fun tau => tau 1 g (g * h)) hd
  have hcpoint := congrArg (fun tau => tau.1 1 g (g * h)) hc
  rw [hdpoint] at hcpoint
  simp [X, TopRep.d_succ, TopRep.d_zero, TopRep.hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun] at hcpoint
  have hinv := homogeneousOneCochain_leftInvariant c g g (g * h)
  have hinv' : c.1 g (g * h) = c.1 1 h := by
    convert hinv.symm using 1
    all_goals group
  rw [hinv'] at hcpoint
  have hnorm : normalizedCocycle z g h =
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1
          1 g (g * h) -
        (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z).1
          1 1 1 :=
    rfl
  rw [normalizedPrimitiveValue_apply, normalizedPrimitiveValue_apply,
    normalizedPrimitiveValue_apply, hnorm]
  rw [← hcpoint]
  abel

/-- A chosen homogeneous primitive gives a continuous section of its cocycle
extension. -/
noncomputable def H2CocycleExtension.sectionOfBoundary
    [LocallyCompactSpace G]
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (c : (Cohomology.trivialZModPCochainsLifted p G).X 1)
    (hc : ((Cohomology.trivialZModPCochainsLifted p G).d 1 2).hom c =
      ((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z) :
    G →ₜ* H2CocycleExtension z where
  toFun g := ⟨normalizedPrimitiveValue z c g, g⟩
  map_one' := by
    apply H2CocycleExtension.ext
    · change normalizedPrimitiveValue z c 1 = 0
      have hb := normalizedPrimitiveValue_mul z c hc 1 1
      rw [one_mul, normalizedCocycle_one_left] at hb
      apply add_left_cancel (a := normalizedPrimitiveValue z c 1)
      calc
        normalizedPrimitiveValue z c 1 + normalizedPrimitiveValue z c 1 =
            normalizedPrimitiveValue z c 1 + normalizedPrimitiveValue z c 1 + 0 :=
          (add_zero _).symm
        _ = normalizedPrimitiveValue z c 1 := hb.symm
        _ = normalizedPrimitiveValue z c 1 + 0 := (add_zero _).symm
    · rfl
  map_mul' g h := by
    apply H2CocycleExtension.ext
    · exact normalizedPrimitiveValue_mul z c hc g h
    · rfl
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact (normalizedPrimitiveValue z c).continuous.prodMk continuous_id

@[simp]
theorem H2CocycleExtension.projection_comp_sectionOfBoundary
    [LocallyCompactSpace G]
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (c : (Cohomology.trivialZModPCochainsLifted p G).X 1)
    (hc : ((Cohomology.trivialZModPCochainsLifted p G).d 1 2).hom c =
      ((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom z) :
    (H2CocycleExtension.projection z).comp
        (H2CocycleExtension.sectionOfBoundary z c hc) =
      ContinuousMonoidHom.id G :=
  rfl

/-- A degree-two cocycle with zero homology class has a continuous splitting. -/
theorem H2CocycleExtension.exists_section_of_π_eq_zero
    [LocallyCompactSpace G]
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (hz : ContinuousCohomology.π
      (Cohomology.trivialZModPLifted p G) 2 z = 0) :
    ∃ s : G →ₜ* H2CocycleExtension z,
      (H2CocycleExtension.projection z).comp s =
        ContinuousMonoidHom.id G := by
  obtain ⟨c, hc⟩ := Cohomology.exists_boundary_of_homologyπ_apply_eq_zero
    (Cohomology.trivialZModPLifted p G) 1 z hz
  exact ⟨H2CocycleExtension.sectionOfBoundary z c hc,
    H2CocycleExtension.projection_comp_sectionOfBoundary z c hc⟩

/-- Conversely, a continuous section of a cocycle extension makes the
represented degree-two class vanish. -/
theorem H2CocycleExtension.π_eq_zero_of_section
    [LocallyCompactSpace G]
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (s : G →ₜ* H2CocycleExtension z)
    (hs : (H2CocycleExtension.projection z).comp s =
      ContinuousMonoidHom.id G) :
    ContinuousCohomology.π
      (Cohomology.trivialZModPLifted p G) 2 z = 0 := by
  let b : C(G, FreeProPH2Cocycle.A p) :=
    { toFun := fun g => (s g).left
      continuous_toFun :=
        (continuous_fst.comp
          (H2CocycleExtension.toProdHomeomorph z).continuous).comp
            s.continuous_toFun }
  have hsright (g : G) : (s g).right = g := by
    have h := congrArg (fun f : G →ₜ* G => f g) hs
    exact h
  have hb : ∀ g h, b (g * h) =
      b g + b h + normalizedCocycle z g h := by
    intro g h
    have hmul := congrArg H2CocycleExtension.left (s.map_mul g h)
    change (s (g * h)).left =
      (s g).left + (s h).left +
        normalizedCocycle z (s g).right (s h).right at hmul
    change (s (g * h)).left =
      (s g).left + (s h).left + normalizedCocycle z g h
    simpa only [hsright] using hmul
  let K := Cohomology.trivialZModPCochainsLifted p G
  let c : K.X 1 := homogeneousPrimitive z b
  have hc : (K.d 1 2).hom c = (K.iCycles 2).hom z :=
    homogeneousPrimitive_boundary z b hb
  have hzc : (K.toCycles 1 2).hom c = z := by
    apply Cohomology.topModule_mono_injective_lifted (K.iCycles 2)
    calc
      (K.iCycles 2).hom ((K.toCycles 1 2).hom c) = (K.d 1 2).hom c := by
        exact ConcreteCategory.congr_hom (K.toCycles_i 1 2) c
      _ = (K.iCycles 2).hom z := hc
  rw [← hzc]
  exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ 1 2) c

/-- A degree-two cocycle extension splits continuously exactly when its
represented class vanishes. -/
theorem H2CocycleExtension.exists_section_iff_π_eq_zero
    [LocallyCompactSpace G]
    (z : Cohomology.trivialZModPCocyclesLifted p G 2) :
    (∃ s : G →ₜ* H2CocycleExtension z,
      (H2CocycleExtension.projection z).comp s =
        ContinuousMonoidHom.id G) ↔
      ContinuousCohomology.π
        (Cohomology.trivialZModPLifted p G) 2 z = 0 := by
  constructor
  · rintro ⟨s, hs⟩
    exact H2CocycleExtension.π_eq_zero_of_section z s hs
  · exact H2CocycleExtension.exists_section_of_π_eq_zero z

end


end ClassFieldTower.ProP
