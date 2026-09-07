import GaloisCohomology.ProP.H2CocycleExtension
import GaloisCohomology.ProP.PresentationH2Primitive

set_option autoImplicit false
/-!
# Degree-two classes as nonsplit central extensions

This file chooses a homogeneous cocycle representative of a lifted continuous
degree-two class and attaches its explicit central extension.  A continuous
group-theoretic section of the extension forces the represented cohomology
class to vanish.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CategoryTheory TopRep ContRepresentation
open FreeProPH2Cocycle

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

/-- A linear choice of cocycle representative of a lifted degree-two class. -/
noncomputable def degreeTwoCocycleRepresentative
    (x : Cohomology.continuousCohomologyZModPLifted p Q 2) :
    Cohomology.trivialZModPCocyclesLifted p Q 2 :=
  PresentationH2Aux.homologyRepresentativeSection
    (Cohomology.trivialZModPLifted p Q) 2 x

/-- The chosen cocycle represents the prescribed degree-two class. -/
theorem degreeTwoCocycleRepresentative_π
    (x : Cohomology.continuousCohomologyZModPLifted p Q 2) :
    ContinuousCohomology.π (Cohomology.trivialZModPLifted p Q) 2
        (degreeTwoCocycleRepresentative x) = x := by
  have h := congrArg
    (fun f : Cohomology.continuousCohomologyZModPLifted p Q 2 →ₗ[ZMod p]
        Cohomology.continuousCohomologyZModPLifted p Q 2 => f x)
    (PresentationH2Aux.homologyRepresentativeSection_rightInverse
      (Cohomology.trivialZModPLifted p Q) 2)
  exact h

/-- The explicit central extension attached to a lifted degree-two class. -/
abbrev DegreeTwoCentralExtension
    (x : Cohomology.continuousCohomologyZModPLifted p Q 2) :=
  H2CocycleExtension (degreeTwoCocycleRepresentative x)

/-- A continuous splitting of the cocycle extension makes its degree-two
class zero. -/
theorem eq_zero_of_degreeTwoCentralExtension_section
    [LocallyCompactSpace Q]
    (x : Cohomology.continuousCohomologyZModPLifted p Q 2)
    (hsection : ∃ s : Q →ₜ* DegreeTwoCentralExtension x,
      (H2CocycleExtension.projection
        (degreeTwoCocycleRepresentative x)).comp s =
          ContinuousMonoidHom.id Q) :
    x = 0 := by
  let z := degreeTwoCocycleRepresentative x
  obtain ⟨s, hs⟩ := hsection
  let b : C(Q, A p) :=
    { toFun := fun q => (s q).left
      continuous_toFun :=
        (continuous_fst.comp
          (H2CocycleExtension.toProdHomeomorph z).continuous).comp
            s.continuous_toFun }
  have hsright (q : Q) : (s q).right = q := by
    have h := congrArg (fun f : Q →ₜ* Q => f q) hs
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
  let K := Cohomology.trivialZModPCochainsLifted p Q
  let c : K.X 1 := homogeneousPrimitive z b
  have hc : (K.d 1 2).hom c = (K.iCycles 2).hom z :=
    homogeneousPrimitive_boundary z b hb
  have hzc : (K.toCycles 1 2).hom c = z := by
    apply Cohomology.topModule_mono_injective_lifted (K.iCycles 2)
    calc
      (K.iCycles 2).hom ((K.toCycles 1 2).hom c) = (K.d 1 2).hom c := by
        exact ConcreteCategory.congr_hom (K.toCycles_i 1 2) c
      _ = (K.iCycles 2).hom z := hc
  have hπ : ContinuousCohomology.π
      (Cohomology.trivialZModPLifted p Q) 2 z = 0 := by
    rw [← hzc]
    exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ 1 2) c
  rw [← degreeTwoCocycleRepresentative_π x]
  exact hπ

/-- A nonzero degree-two class gives a nonsplit continuous central
extension. -/
theorem degreeTwoCentralExtension_no_section_of_ne_zero
    [LocallyCompactSpace Q]
    {x : Cohomology.continuousCohomologyZModPLifted p Q 2}
    (hx : x ≠ 0) :
    ¬ ∃ s : Q →ₜ* DegreeTwoCentralExtension x,
      (H2CocycleExtension.projection
        (degreeTwoCocycleRepresentative x)).comp s =
          ContinuousMonoidHom.id Q := by
  intro hsection
  exact hx (eq_zero_of_degreeTwoCentralExtension_section x hsection)

end

end ClassFieldTower.ProP
