import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import Mathlib.Topology.Instances.ZMod

set_option autoImplicit false
/-!
# Continuous cohomology with trivial `ZMod p` coefficients

This is the coefficient object used by the relation-rank benchmark, together with its canonical
restriction maps on homogeneous cochains, cocycles, and continuous cohomology.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

variable (p : ℕ) (G : Type) [Group G]

/-- The trivial continuous `ZMod p`-representation of a group. -/
noncomputable def trivialZModP : TopRep (ZMod p) G :=
  TopRep.of (ContRepresentation.trivial (ZMod p) G (ZMod p))

@[simp]
theorem trivialZModP_action (g : G) (x : ZMod p) :
    (trivialZModP p G).ρ g x = x :=
  rfl

section Restriction

variable {G : Type} [Group G] [TopologicalSpace G]
variable {H : Type} [Group H] [TopologicalSpace H]

/-- The canonical coefficient morphism used to restrict trivial coefficients along a continuous
group homomorphism. -/
noncomputable def trivialZModPRestrictionHom (f : H →ₜ* G) :
    TopRep.res f (trivialZModP p G) ⟶ trivialZModP p H :=
  TopRep.ofHom (.id (π₁ := ContRepresentation.trivial (ZMod p) H (ZMod p)))

@[simp]
theorem trivialZModPRestrictionHom_id :
    trivialZModPRestrictionHom p (ContinuousMonoidHom.id G) = 𝟙 (trivialZModP p G) :=
  rfl

@[simp]
theorem trivialZModPRestrictionHom_comp
    {K : Type} [Group K] [TopologicalSpace K]
    (f : H →ₜ* G) (g : K →ₜ* H) :
    (TopRep.resFunctor (g : K →* H)).map (trivialZModPRestrictionHom p f) ≫
        trivialZModPRestrictionHom p g =
      trivialZModPRestrictionHom p (f.comp g) :=
  rfl

end Restriction

section Cohomology

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Homogeneous continuous cochains with trivial `ZMod p` coefficients. -/
abbrev trivialZModPCochains := TopRep.homogeneousCochains (trivialZModP p G)

/-- Continuous cocycles with trivial `ZMod p` coefficients. -/
noncomputable abbrev trivialZModPCocycles (n : ℕ) :=
  ContinuousCohomology.cocycles (trivialZModP p G) n

/-- Continuous cohomology with trivial `ZMod p` coefficients. -/
noncomputable abbrev continuousCohomologyZModP (n : ℕ) :=
  continuousCohomology n (trivialZModP p G)

variable {G}
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Restriction of homogeneous cochains with trivial `ZMod p` coefficients. -/
noncomputable def trivialZModPCochainsMap (f : H →ₜ* G) :
    trivialZModPCochains p G ⟶ trivialZModPCochains p H :=
  ContinuousCohomology.cochainsMap f (trivialZModPRestrictionHom p f)

/-- Restriction of continuous cocycles with trivial `ZMod p` coefficients. -/
noncomputable abbrev trivialZModPCocyclesMap (f : H →ₜ* G) (n : ℕ) :
    trivialZModPCocycles p G n ⟶ trivialZModPCocycles p H n :=
  ContinuousCohomology.cocyclesMap f (trivialZModPRestrictionHom p f) n

/-- Restriction on continuous cohomology with trivial `ZMod p` coefficients. -/
noncomputable abbrev continuousCohomologyZModPMap (f : H →ₜ* G) (n : ℕ) :
    continuousCohomologyZModP p G n ⟶ continuousCohomologyZModP p H n :=
  ContinuousCohomology.map f (trivialZModPRestrictionHom p f) n

@[simp]
theorem trivialZModPCochainsMap_id :
    trivialZModPCochainsMap p (ContinuousMonoidHom.id G) =
      𝟙 (trivialZModPCochains p G) := by
  simp [trivialZModPCochainsMap]

@[simp]
theorem trivialZModPCochainsMap_comp
    {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (f : H →ₜ* G) (g : K →ₜ* H) :
    trivialZModPCochainsMap p (f.comp g) =
      trivialZModPCochainsMap p f ≫ trivialZModPCochainsMap p g := by
  rw [trivialZModPCochainsMap, ← trivialZModPRestrictionHom_comp p f g]
  exact ContinuousCohomology.cochainsMap_comp f g
    (trivialZModPRestrictionHom p f) (trivialZModPRestrictionHom p g)

@[simp]
theorem continuousCohomologyZModPMap_id (n : ℕ) :
    continuousCohomologyZModPMap p (ContinuousMonoidHom.id G) n =
      𝟙 (continuousCohomologyZModP p G n) := by
  simp [continuousCohomologyZModPMap]

@[simp]
theorem continuousCohomologyZModPMap_comp
    {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (f : H →ₜ* G) (g : K →ₜ* H) (n : ℕ) :
    continuousCohomologyZModPMap p (f.comp g) n =
      continuousCohomologyZModPMap p f n ≫ continuousCohomologyZModPMap p g n := by
  rw [continuousCohomologyZModPMap, ← trivialZModPRestrictionHom_comp p f g]
  exact ContinuousCohomology.map_comp f g
    (trivialZModPRestrictionHom p f) (trivialZModPRestrictionHom p g) n

/-- The cocycle quotient map commutes with restriction. -/
theorem trivialZModP_π_naturality (f : H →ₜ* G) (n : ℕ) :
    ContinuousCohomology.π (trivialZModP p G) n ≫ continuousCohomologyZModPMap p f n =
      trivialZModPCocyclesMap p f n ≫ ContinuousCohomology.π (trivialZModP p H) n :=
  ContinuousCohomology.π_map f (trivialZModPRestrictionHom p f) n

end Cohomology

section Lifted

variable (p : ℕ) (G : Type u) [Group G]

/-- The trivial `ZMod p`-representation with its carrier lifted to the universe of `G`.

Mathlib's homogeneous continuous-cochain resolution places its representation carrier in at
least the universe of the acting group.  This lift therefore supplies the universe-polymorphic
cohomology coefficient object; `trivialZModP` retains its original small-universe API. -/
noncomputable def trivialZModPLifted : TopRep.{u} (ZMod p) G := by
  letI : ContinuousSMul (ZMod p) (ULift.{u} (ZMod p)) :=
    ContinuousSMul.induced ULift.moduleEquiv.toLinearMap
  exact TopRep.of
    (ContRepresentation.trivial (ZMod p) G (ULift.{u} (ZMod p)))

@[simp]
theorem trivialZModPLifted_action (g : G) (x : ULift.{u} (ZMod p)) :
    (trivialZModPLifted p G).ρ g x = x :=
  rfl

variable {G H : Type u} [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H]

/-- Restriction of the universe-lifted trivial coefficient representation. -/
noncomputable def trivialZModPRestrictionHomLifted (f : H →ₜ* G) :
    TopRep.res f (trivialZModPLifted p G) ⟶ trivialZModPLifted p H := by
  letI : ContinuousSMul (ZMod p) (ULift.{u} (ZMod p)) :=
    ContinuousSMul.induced ULift.moduleEquiv.toLinearMap
  exact TopRep.ofHom (.id (π₁ := (trivialZModPLifted p H).ρ))

@[simp]
theorem trivialZModPRestrictionHomLifted_id :
    trivialZModPRestrictionHomLifted p (ContinuousMonoidHom.id G) =
      𝟙 (trivialZModPLifted p G) :=
  rfl

@[simp]
theorem trivialZModPRestrictionHomLifted_comp
    {K : Type u} [Group K] [TopologicalSpace K]
    (f : H →ₜ* G) (g : K →ₜ* H) :
    (TopRep.resFunctor (g : K →* H)).map (trivialZModPRestrictionHomLifted p f) ≫
        trivialZModPRestrictionHomLifted p g =
      trivialZModPRestrictionHomLifted p (f.comp g) :=
  rfl

section LiftedCohomology

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Homogeneous continuous cochains with universe-lifted trivial `ZMod p` coefficients. -/
abbrev trivialZModPCochainsLifted :=
  TopRep.homogeneousCochains (trivialZModPLifted p G)

/-- Continuous cocycles with universe-lifted trivial `ZMod p` coefficients. -/
noncomputable abbrev trivialZModPCocyclesLifted (n : ℕ) :=
  ContinuousCohomology.cocycles (trivialZModPLifted p G) n

/-- Continuous cohomology with universe-lifted trivial `ZMod p` coefficients. -/
noncomputable abbrev continuousCohomologyZModPLifted (n : ℕ) :=
  continuousCohomology n (trivialZModPLifted p G)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Restriction of lifted homogeneous cochains with trivial `ZMod p` coefficients. -/
noncomputable def trivialZModPCochainsMapLifted (f : H →ₜ* G) :
    trivialZModPCochainsLifted p G ⟶ trivialZModPCochainsLifted p H :=
  ContinuousCohomology.cochainsMap f (trivialZModPRestrictionHomLifted p f)

/-- Restriction of lifted continuous cocycles with trivial `ZMod p` coefficients. -/
noncomputable abbrev trivialZModPCocyclesMapLifted (f : H →ₜ* G) (n : ℕ) :
    trivialZModPCocyclesLifted p G n ⟶ trivialZModPCocyclesLifted p H n :=
  ContinuousCohomology.cocyclesMap f (trivialZModPRestrictionHomLifted p f) n

/-- Restriction on lifted continuous cohomology with trivial `ZMod p` coefficients. -/
noncomputable abbrev continuousCohomologyZModPMapLifted (f : H →ₜ* G) (n : ℕ) :
    continuousCohomologyZModPLifted p G n ⟶ continuousCohomologyZModPLifted p H n :=
  ContinuousCohomology.map f (trivialZModPRestrictionHomLifted p f) n

@[simp]
theorem trivialZModPCochainsMapLifted_id :
    trivialZModPCochainsMapLifted p (ContinuousMonoidHom.id G) =
      𝟙 (trivialZModPCochainsLifted p G) := by
  simp [trivialZModPCochainsMapLifted]

@[simp]
theorem trivialZModPCochainsMapLifted_comp
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (f : H →ₜ* G) (g : K →ₜ* H) :
    trivialZModPCochainsMapLifted p (f.comp g) =
      trivialZModPCochainsMapLifted p f ≫ trivialZModPCochainsMapLifted p g := by
  rw [trivialZModPCochainsMapLifted, ← trivialZModPRestrictionHomLifted_comp p f g]
  exact ContinuousCohomology.cochainsMap_comp f g
    (trivialZModPRestrictionHomLifted p f) (trivialZModPRestrictionHomLifted p g)

@[simp]
theorem continuousCohomologyZModPMapLifted_id (n : ℕ) :
    continuousCohomologyZModPMapLifted p (ContinuousMonoidHom.id G) n =
      𝟙 (continuousCohomologyZModPLifted p G n) := by
  simp [continuousCohomologyZModPMapLifted]

@[simp]
theorem continuousCohomologyZModPMapLifted_comp
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (f : H →ₜ* G) (g : K →ₜ* H) (n : ℕ) :
    continuousCohomologyZModPMapLifted p (f.comp g) n =
      continuousCohomologyZModPMapLifted p f n ≫
        continuousCohomologyZModPMapLifted p g n := by
  rw [continuousCohomologyZModPMapLifted,
    ← trivialZModPRestrictionHomLifted_comp p f g]
  exact ContinuousCohomology.map_comp f g
    (trivialZModPRestrictionHomLifted p f)
    (trivialZModPRestrictionHomLifted p g) n

/-- The lifted cocycle quotient map commutes with restriction. -/
theorem trivialZModPLifted_π_naturality (f : H →ₜ* G) (n : ℕ) :
    ContinuousCohomology.π (trivialZModPLifted p G) n ≫
        continuousCohomologyZModPMapLifted p f n =
      trivialZModPCocyclesMapLifted p f n ≫
        ContinuousCohomology.π (trivialZModPLifted p H) n :=
  ContinuousCohomology.π_map f (trivialZModPRestrictionHomLifted p f) n

end LiftedCohomology

end Lifted

end

end ClassFieldTower.Cohomology
