import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Instances.ZMod
import ProCGroups.Completion.UniversalProperty
import ProCGroups.FiniteGroups.StandardClasses
import ProCGroups.FiniteGeneration.CharacteristicChainsAndIndices
import ProCGroups.ProC.Category.Basic
import ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation

set_option autoImplicit false

/-!
# Pro C Groups / Free pro-C / Basic

This module defines the free and pointed free pro-\(C\) universal properties,
their converging-set form, and the bundled canonical source data used by later
constructions.
-/

open Set
open scoped Topology

namespace ProCGroups.FreeProC

universe u v w

open ProCGroups
open ProCGroups.FiniteGeneration

section

variable {C : ProCGroups.FiniteGroupClass}

/--
Free pro-\(C\) groups via a strengthened universal property. The lifting property quantifies
over all continuous maps into pro-\(C\) groups, rather than only maps whose image generates the
target.
-/
structure IsFreeProCGroup
    {X : Type u} [TopologicalSpace X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (ι : X → F) : Prop where
  /--
  Open normal subgroups with quotients in `C` form a neighborhood basis at one in `F`.
  -/
  hasOpenNormalBasisInClass : ProCGroups.ProC.HasOpenNormalBasisInClass C F
  /-- The canonical map from the generating space into `F` is continuous. -/
  continuous_ι : Continuous ι
  /-- The image of the canonical map topologically generates `F`. -/
  generates_range : Generation.TopologicallyGenerates (G := F) (Set.range ι)
  /--
  Every continuous map from `X` to a pro-`C` target extends to a unique continuous group
  homomorphism from `F`.
  -/
  existsUnique_lift :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G],
    ProCGroups.ProC.HasOpenNormalBasisInClass C (G) →
      ∀ (φ : X → G), Continuous φ →
        ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x


namespace IsFreeProCGroup

variable {X : Type u} [TopologicalSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable {ι : X → F}

/--
A map from the chosen generators into a pro-\(C\) target extends to the corresponding continuous
homomorphism from the free pro-\(C\) group.
-/
noncomputable def lift (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ) : F →* G :=
  Classical.choose (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ))

/-- The universal-property lift has the prescribed values on the chosen generators. -/
theorem lift_spec (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ) :
    Continuous (hι.lift hG φ hφ) ∧ ∀ x, hι.lift hG φ hφ (ι x) = φ x :=
  Classical.choose_spec (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ))

/-- The universal-property lift is unique among continuous maps with the prescribed values. -/
theorem lift_unique (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ)
    {f : F →* G} (hf : Continuous f) (hfac : ∀ x, f (ι x) = φ x) :
    f = hι.lift hG φ hφ := by
  exact (hι.existsUnique_lift hG φ hφ).unique ⟨hf, hfac⟩ (hι.lift_spec hG φ hφ)

/-- The universal-property lift bundled as a continuous monoid homomorphism. -/
noncomputable def liftHom (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ) : F →ₜ* G where
  toMonoidHom := hι.lift hG φ hφ
  continuous_toFun := (hι.lift_spec hG φ hφ).1

/-- Forgetting continuity from liftHom gives the underlying universal-property lift. -/
@[simp] theorem liftHom_toMonoidHom (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ) :
    (hι.liftHom hG φ hφ).toMonoidHom = hι.lift hG φ hφ :=
  rfl

/--
The lift homomorphism from a free pro-\(C\) group evaluates according to the chosen generator
map.
-/
@[simp] theorem liftHom_apply (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ) (x : X) :
    hι.liftHom hG φ hφ (ι x) = φ x :=
  (hι.lift_spec hG φ hφ).2 x

/-- The lift homomorphism is uniquely determined by its values on the generators. -/
theorem liftHom_unique (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ)
    {f : F →ₜ* G} (hfac : ∀ x, f (ι x) = φ x) :
    f = hι.liftHom hG φ hφ := by
  ext y
  exact congrArg (fun g : F →* G => g y)
    (hι.lift_unique hG φ hφ f.continuous_toFun hfac)

/--
Continuous homomorphisms out of a free pro-\(C\) group are determined by their values on the
chosen generators.
-/
theorem hom_ext (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    {f g : F →* G} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f (ι x) = g (ι x)) :
    f = g := by
  let φ : X → G := fun x => f (ι x)
  have hφ : Continuous φ := hf.comp hι.continuous_ι
  exact
    (hι.existsUnique_lift hG φ hφ).unique
      ⟨hf, fun _ => rfl⟩ ⟨hg, fun x => (hfg x).symm⟩

/-- Two universal-property lifts are equal when they agree on all generators. -/
theorem lift_eq_of_forall (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    {φ ψ : X → G} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : ∀ x, φ x = ψ x) :
    hι.lift hG φ hφ = hι.lift hG ψ hψ := by
  apply hι.hom_ext hG
    (hι.lift_spec hG φ hφ).1
    (hι.lift_spec hG ψ hψ).1
  intro x
  calc
    hι.lift hG φ hφ (ι x) = φ x := (hι.lift_spec hG φ hφ).2 x
    _ = ψ x := h x
    _ = hι.lift hG ψ hψ (ι x) := ((hι.lift_spec hG ψ hψ).2 x).symm

/-- The lift of the canonical generator map to the same free pro-\(C\) group is the identity. -/
@[simp] theorem lift_id (hι : IsFreeProCGroup (C := C) ι) :
    hι.lift hι.hasOpenNormalBasisInClass ι hι.continuous_ι = MonoidHom.id F := by
  symm
  exact hι.lift_unique hι.hasOpenNormalBasisInClass ι hι.continuous_ι continuous_id (by
    intro x
    rfl)

/-- An endomorphism of a free pro-\(C\) group fixing the generators is the identity. -/
theorem endomorphism_eq_id (hι : IsFreeProCGroup (C := C) ι)
    {f : F →* F} (hf : Continuous f) (hfac : ∀ x, f (ι x) = ι x) :
    f = MonoidHom.id F := by
  exact hι.hom_ext hι.hasOpenNormalBasisInClass hf continuous_id hfac

/-- Composition of free pro-\(C\) lifts is again the lift of the composed generator map. -/
theorem lift_comp (hι : IsFreeProCGroup (C := C) ι)
    {G H : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (φ : X → G) (hφ : Continuous φ)
    (ψ : G →* H) (hψ : Continuous ψ) :
    ψ.comp (hι.lift hG φ hφ) =
      hι.lift hH (fun x => ψ (φ x)) (hψ.comp hφ) := by
  apply hι.lift_unique hH (fun x => ψ (φ x)) (hψ.comp hφ)
    (hψ.comp (hι.lift_spec hG φ hφ).1)
  intro x
  simp only [MonoidHom.coe_comp, Function.comp_apply, (hι.lift_spec hG φ hφ).2 x]


end IsFreeProCGroup


end

section

variable {C : ProCGroups.FiniteGroupClass}

/-- A family converges to `1` when it tends to `1` along the cofinite filter. -/
def FamilyConvergesToOne
    {X : Type v}
    {G : Type u} [Group G] [TopologicalSpace G]
    (μ : X → G) : Prop :=
  Filter.Tendsto μ Filter.cofinite (𝓝 1)

/-- The weaker condition obtained by testing family convergence only against open subgroups. -/
def FamilyConvergesToOneAlongOpenSubgroups
    {X : Type v}
    {G : Type u} [Group G] [TopologicalSpace G]
    (μ : X → G) : Prop :=
  ∀ U : OpenSubgroup G, {x : X | μ x ∉ (U : Set G)}.Finite

namespace FamilyConvergesToOne

variable {X : Type v}
variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Genuine family convergence implies convergence along open subgroups. -/
theorem to_alongOpenSubgroups {μ : X → G}
    (hμ : FamilyConvergesToOne (G := G) μ) :
    FamilyConvergesToOneAlongOpenSubgroups (G := G) μ := by
  intro U
  have hU : (U : Set G) ∈ 𝓝 (1 : G) :=
    U.isOpen.mem_nhds U.one_mem
  have heventually : ∀ᶠ x : X in Filter.cofinite, μ x ∈ U :=
    hμ.eventually hU
  change {x : X | μ x ∈ U} ∈ Filter.cofinite at heventually
  rw [Filter.mem_cofinite] at heventually
  simpa only [Set.compl_ofPred, SetLike.mem_coe] using heventually

/-- Convergence is preserved by a continuous homomorphism. -/
theorem comp
    {H : Type*} [TopologicalSpace H] [Group H]
    {μ : X → G}
    (hμ : FamilyConvergesToOne (G := G) μ) (f : G →ₜ* H) :
    FamilyConvergesToOne (G := H) (fun x => f (μ x)) := by
  change Filter.Tendsto (f.toContinuousMap ∘ μ) Filter.cofinite (𝓝 1)
  have hf1 : f.toContinuousMap (1 : G) = 1 := f.map_one
  simpa only [hf1] using (f.continuous.tendsto (1 : G)).comp hμ

/-- Families indexed by a finite type converge to `1`. -/
theorem of_finite_domain [Finite X] (μ : X → G) :
    FamilyConvergesToOne (G := G) μ := by
  rw [FamilyConvergesToOne, Filter.tendsto_def]
  intro W _
  rw [Filter.mem_cofinite]
  exact Set.toFinite _

/-- On an infinite index type in a `T₁` space, a constant family converges to `1` exactly when
its value is `1`. In particular, the old open-subgroup-only counterexample is rejected. -/
theorem const_iff [Infinite X] [T1Space G] (g : G) :
    FamilyConvergesToOne (G := G) (fun _ : X => g) ↔ g = 1 := by
  simp only [FamilyConvergesToOne, tendsto_const_nhds_iff]

end FamilyConvergesToOne

namespace FamilyConvergesToOneAlongOpenSubgroups

variable {X : Type v}
variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A family converging to `1` has range converging to `1` as a set. -/
theorem range {μ : X → G} (hμ : FamilyConvergesToOneAlongOpenSubgroups (G := G) μ) :
    Generation.ConvergesToOneAlongOpenSubgroups (G := G) (Set.range μ) := by
  intro U
  have hsubset :
      Set.range μ \ (U : Set G) ⊆ μ '' {x : X | μ x ∉ (U : Set G)} := by
    rintro y ⟨⟨x, rfl⟩, hxU⟩
    exact ⟨x, hxU, rfl⟩
  exact (hμ U).image μ |>.subset hsubset

/-- Convergence to `1` is preserved by a continuous homomorphism. -/
theorem comp
    {H : Type*} [TopologicalSpace H] [Group H]
    {μ : X → G}
    (hμ : FamilyConvergesToOneAlongOpenSubgroups (G := G) μ) (f : G →ₜ* H) :
    FamilyConvergesToOneAlongOpenSubgroups (G := H) (fun x => f (μ x)) := by
  intro U
  have hfinite := hμ (U.comap f.toMonoidHom f.continuous)
  have hset :
      {x : X | μ x ∉ (U.comap f.toMonoidHom f.continuous : Set G)} =
        {x : X | f (μ x) ∉ (U : Set H)} := by
    ext x
    exact not_congr
      (OpenSubgroup.mem_comap (H := U) (f := f.toMonoidHom)
        (hf := f.continuous) (x := μ x))
  exact hset ▸ hfinite

/-- Range convergence implies family convergence for injectively indexed families. -/
theorem of_set_of_injective {μ : X → G}
    (hμ : Generation.ConvergesToOneAlongOpenSubgroups (G := G) (Set.range μ))
    (hinj : Function.Injective μ) :
    FamilyConvergesToOneAlongOpenSubgroups (G := G) μ := by
  intro U
  have himage :
      μ '' {x : X | μ x ∉ (U : Set G)} = Set.range μ \ (U : Set G) := by
    ext y
    constructor
    · rintro ⟨x, hxU, rfl⟩
      exact ⟨⟨x, rfl⟩, hxU⟩
    · rintro ⟨⟨x, rfl⟩, hxU⟩
      exact ⟨x, hxU, rfl⟩
  let : Finite (μ '' {x : X | μ x ∉ (U : Set G)}) := by
    rw [himage]
    exact (hμ U).to_subtype
  exact Finite.Set.finite_of_finite_image {x : X | μ x ∉ (U : Set G)} (by
    intro a _ b _ hab
    exact hinj hab)

/-- Families indexed by a finite type converge to `1`. -/
theorem of_finite_domain [Finite X] (μ : X → G) :
    FamilyConvergesToOneAlongOpenSubgroups (G := G) μ := by
  intro U
  exact Set.finite_univ.subset (by intro x _; trivial)

/-- In a nonarchimedean group, open subgroups detect genuine family convergence. -/
theorem to_familyConvergesToOne [NonarchimedeanGroup G] {μ : X → G}
    (hμ : FamilyConvergesToOneAlongOpenSubgroups (G := G) μ) :
    FamilyConvergesToOne (G := G) μ := by
  rw [FamilyConvergesToOne, Filter.tendsto_def]
  intro W hW
  obtain ⟨U, hUW⟩ := NonarchimedeanGroup.is_nonarchimedean W hW
  rw [Filter.mem_cofinite]
  change {x : X | μ x ∉ W}.Finite
  exact (hμ U).subset (by
    intro x hxW hxU
    exact hxW (hUW hxU))

end FamilyConvergesToOneAlongOpenSubgroups

/-- For nonarchimedean groups, genuine family convergence is equivalent to the
open-subgroup test. -/
theorem familyConvergesToOne_iff_alongOpenSubgroups
    {X : Type v} {G : Type u} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] {μ : X → G} :
    FamilyConvergesToOne (G := G) μ ↔
      FamilyConvergesToOneAlongOpenSubgroups (G := G) μ :=
  ⟨FamilyConvergesToOne.to_alongOpenSubgroups,
    FamilyConvergesToOneAlongOpenSubgroups.to_familyConvergesToOne⟩

/-- An open-subgroup-convergent family whose image topologically generates the target; here
convergence means finiteness outside every open subgroup. -/
structure ConvergingGeneratingMap
    (X : Type v)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] where
  /-- The family of elements of `G`, indexed by `X`. -/
  toFun : X → G
  /--
  Outside every open subgroup of `G`, the family has only finitely many terms; thus it converges
  to one in the open-subgroup sense.
  -/
  convergesToOneAlongOpenSubgroups : FamilyConvergesToOneAlongOpenSubgroups (G := G) toFun
  /-- The range of the family topologically generates `G`. -/
  generates : Generation.TopologicallyGenerates (G := G) (Set.range toFun)

namespace ConvergingGeneratingMap

variable {X Y : Type v}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A convergent generating map coerces to its underlying map into the group. -/
instance instCoeFunConvergingGeneratingMap :
    CoeFun (ConvergingGeneratingMap X G) (fun _ => X → G) where
  coe φ := φ.toFun

/-- The stored function of a convergent generating map agrees with its function coercion. -/
@[simp] theorem toFun_eq_coe (φ : ConvergingGeneratingMap X G) :
    φ.toFun = (φ : X → G) := rfl

/-- Reindexing along an equivalence preserves family convergence and generation. -/
def reindex (φ : ConvergingGeneratingMap X G) (e : Y ≃ X) :
    ConvergingGeneratingMap Y G where
  toFun := fun y => φ (e y)
  convergesToOneAlongOpenSubgroups := by
    intro U
    have hsubset :
        {y : Y | φ (e y) ∉ (U : Set G)} ⊆
          e.symm '' {x : X | φ x ∉ (U : Set G)} := by
      intro y hy
      exact ⟨e y, hy, by simp only [Equiv.symm_apply_apply]⟩
    exact (φ.convergesToOneAlongOpenSubgroups U).image e.symm |>.subset hsubset
  generates := by
    have hrange : Set.range (fun y : Y => φ (e y)) = Set.range (φ : X → G) := by
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨e y, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨e.symm x, by simp only [Equiv.apply_symm_apply]⟩
    simpa [hrange] using φ.generates

/-- The range of a convergent generating map generates the group and converges to one along open
subgroups. -/
theorem generatesAndConvergesToOneAlongOpenSubgroups (φ : ConvergingGeneratingMap X G) :
    Generation.GeneratesAndConvergesToOneAlongOpenSubgroups (G := G) (Set.range (φ : X → G)) :=
  ⟨φ.generates, φ.convergesToOneAlongOpenSubgroups.range⟩

end ConvergingGeneratingMap

/-- A pointed pro-`C` group with unique lifts only for pointed maps whose images topologically
generate their targets.

This is intentionally not the unrestricted pointed-free universal property. -/
structure IsEpimorphicallyPointedFreeProCGroupOn
    (X : Type u) [TopologicalSpace X] (x0 : X)
    (F : Type u) [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (ι : X → F) : Prop where
  /--
  Open normal subgroups with quotients in `C` form a neighborhood basis at one in `F`.
  -/
  hasOpenNormalBasisInClass : ProCGroups.ProC.HasOpenNormalBasisInClass C F
  /-- The canonical pointed map into `F` is continuous. -/
  continuous_ι : Continuous ι
  /-- The distinguished source point `x0` is sent to the identity of `F`. -/
  map_base : ι x0 = 1
  /-- The image of the canonical pointed map topologically generates `F`. -/
  generates_range : Generation.TopologicallyGenerates (G := F) (Set.range ι)
  /--
  Every continuous, basepoint-preserving map whose image generates a pro-`C` target extends to
  a unique continuous group homomorphism from `F`.
  -/
  existsUnique_lift :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G],
    ProCGroups.ProC.HasOpenNormalBasisInClass C (G) →
      ∀ (φ : X → G), Continuous φ → φ x0 = 1 →
        Generation.TopologicallyGenerates (G := G) (Set.range φ) →
          ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x

/-- A pro-`C` group with unique lifts only for open-subgroup-convergent families whose images
topologically generate their targets. The convergence hypothesis is
`FamilyConvergesToOneAlongOpenSubgroups`, not the unqualified filter predicate.

The `Epimorphically` qualifier records the missing unrestricted mapping property. -/
structure IsEpimorphicallyFreeProCGroupOnConvergingSet
    (X : Type v)
    (F : Type u) [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (ι : X → F) : Prop where
  /--
  Open normal subgroups with quotients in `C` form a neighborhood basis at one in `F`.
  -/
  hasOpenNormalBasisInClass : ProCGroups.ProC.HasOpenNormalBasisInClass C F
  /--
  The canonical generator family has only finitely many terms outside each open subgroup of
  `F`.
  -/
  convergesToOneAlongOpenSubgroups : FamilyConvergesToOneAlongOpenSubgroups (G := F) ι
  /-- The canonical converging family topologically generates `F`. -/
  generates_range : Generation.TopologicallyGenerates (G := F) (Set.range ι)
  /--
  Every converging family that topologically generates a pro-`C` target extends to a unique
  continuous group homomorphism from `F`.
  -/
  existsUnique_lift :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G],
    ProCGroups.ProC.HasOpenNormalBasisInClass C (G) →
      ∀ (φ : X → G), FamilyConvergesToOneAlongOpenSubgroups (G := G) φ →
        Generation.TopologicallyGenerates (G := G) (Set.range φ) →
          ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x

/-- The canonical map of a free pro-`C` group on a topological space is injective whenever the
predicate supplies enough separating pro-`C` targets. -/
theorem freeProCGroupOn_injective
    {X : Type u} [TopologicalSpace X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hι : IsFreeProCGroup (C := C) ι)
    (hsep :
      ∀ ⦃x y : X⦄, x ≠ y →
        ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A)
          (_ : CompactSpace A) (_ : T2Space A) (_ : TotallyDisconnectedSpace A),
    ProCGroups.ProC.HasOpenNormalBasisInClass C A ∧
            ∃ φ : X → A, Continuous φ ∧
              Generation.TopologicallyGenerates (G := A) (Set.range φ) ∧ φ x ≠ φ y) :
    Function.Injective ι := by
  intro x y hEq
  by_contra hxy
  rcases hsep hxy with
    ⟨A, _instGroupA, _instTopA, _instTopGroupA, _instCompactA, _instT2A, _instTDA,
      hA, φ, hφ, hgenφ, hφxy⟩
  rcases hι.existsUnique_lift hA φ hφ with ⟨f, hf, _huniq⟩
  have hcontr : φ x = φ y := by
    simpa [hf.2 x, hf.2 y] using congrArg f hEq
  exact hφxy hcontr

/-- Under an explicit nontrivial cyclic pro-`C` target hypothesis, the identity does not lie in
the image of the topological basis of a free pro-`C` group. -/
theorem one_not_mem_range_of_freeProCGroupOn
    {X : Type u} [TopologicalSpace X] [Nonempty X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hι : IsFreeProCGroup (C := C) ι)
    (hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A)
        (_ : CompactSpace A) (_ : T2Space A) (_ : TotallyDisconnectedSpace A),
    ProCGroups.ProC.HasOpenNormalBasisInClass C A ∧ ∃ a : A, a ≠ 1 ∧
          Generation.TopologicallyGenerates (G := A) ({a} : Set A)) :
    (1 : F) ∉ Set.range ι := by
  intro h1
  rcases h1 with ⟨x, hx⟩
  rcases hnontrivial with
    ⟨A, _instGroupA, _instTopA, _instTopGroupA, _instCompactA, _instT2A, _instTDA,
      hA, a, ha1, hgena⟩
  let φ : X → A := fun _ => a
  have hφ : Continuous φ := continuous_const
  have hrange : Set.range φ = ({a} : Set A) := by
    ext b
    constructor
    · rintro ⟨y, rfl⟩
      simp only [mem_singleton_iff, φ]
    · intro hb
      rw [Set.mem_singleton_iff] at hb
      subst b
      exact ⟨Classical.choice ‹Nonempty X›, rfl⟩
  have hgenφ : Generation.TopologicallyGenerates (G := A) (Set.range φ) := by
    simpa [hrange] using hgena
  rcases hι.existsUnique_lift hA φ hφ with ⟨f, hf, _huniq⟩
  have haeq : a = 1 := by
    simpa [φ, hx] using (hf.2 x).symm
  exact ha1 haeq

/-- Under an explicit nontrivial cyclic pro-`C` target hypothesis, the identity does not lie in a
basis converging to `1`. -/
theorem one_not_mem_range_of_epimorphicallyFreeProCGroupOnConvergingSet
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    (hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A)
        (_ : CompactSpace A) (_ : T2Space A) (_ : TotallyDisconnectedSpace A),
    ProCGroups.ProC.HasOpenNormalBasisInClass C A ∧ ∃ a : A, a ≠ 1 ∧
          Generation.TopologicallyGenerates (G := A) ({a} : Set A)) :
    (1 : F) ∉ Set.range ι := by
  classical
  intro h1
  rcases h1 with ⟨x, hx⟩
  rcases hnontrivial with
    ⟨A, _instGroupA, _instTopA, _instTopGroupA, _instCompactA, _instT2A, _instTDA,
      hA, a, ha1, hgena⟩
  let φ : X → A := fun z => if z = x then a else 1
  have hφconv : FamilyConvergesToOneAlongOpenSubgroups (G := A) φ := by
    intro U
    have hsubset : {z : X | φ z ∉ (U : Set A)} ⊆ ({x} : Set X) := by
      intro z hz
      by_cases hzx : z = x
      · simp only [hzx, mem_singleton_iff]
      · exfalso
        exact hz (by simp only [hzx, ↓reduceIte, SetLike.mem_coe, one_mem, φ])
    exact (Set.finite_singleton x).subset hsubset
  have hφgen : Generation.TopologicallyGenerates (G := A) (Set.range φ) := by
    have hsub : ({a} : Set A) ⊆ Set.range φ := by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨x, by simp only [↓reduceIte, φ]⟩
    exact Generation.topologicallyGenerates_mono (G := A) hgena hsub
  rcases hι.existsUnique_lift hA φ hφconv hφgen with ⟨f, hf, _⟩
  have haeq : a = 1 := by
    simpa [φ, hx] using (hf.2 x).symm
  exact ha1 haeq

/-- Under the same nontrivial cyclic-target hypothesis, the basis map for a free pro-`C` group on
a set converging to `1` is injective. -/
theorem epimorphicallyFreeProCGroupOnConvergingSet_injective
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    (hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A)
        (_ : CompactSpace A) (_ : T2Space A) (_ : TotallyDisconnectedSpace A),
    ProCGroups.ProC.HasOpenNormalBasisInClass C A ∧ ∃ a : A, a ≠ 1 ∧
          Generation.TopologicallyGenerates (G := A) ({a} : Set A)) :
    Function.Injective ι := by
  classical
  intro x y hEq
  by_contra hxy
  rcases hnontrivial with
    ⟨A, _instGroupA, _instTopA, _instTopGroupA, _instCompactA, _instT2A, _instTDA,
      hA, a, ha1, hgena⟩
  have hyx : y ≠ x := by
    intro hyx'
    exact hxy hyx'.symm
  let φ : X → A := fun z => if z = x then a else 1
  have hφconv : FamilyConvergesToOneAlongOpenSubgroups (G := A) φ := by
    intro U
    have hsubset : {z : X | φ z ∉ (U : Set A)} ⊆ ({x} : Set X) := by
      intro z hz
      by_cases hzx : z = x
      · simp only [hzx, mem_singleton_iff]
      · exfalso
        exact hz (by simp only [hzx, ↓reduceIte, SetLike.mem_coe, one_mem, φ])
    exact (Set.finite_singleton x).subset hsubset
  have hφgen : Generation.TopologicallyGenerates (G := A) (Set.range φ) := by
    have hsub : ({a} : Set A) ⊆ Set.range φ := by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨x, by simp only [↓reduceIte, φ]⟩
    exact Generation.topologicallyGenerates_mono (G := A) hgena hsub
  rcases hι.existsUnique_lift hA φ hφconv hφgen with ⟨f, hf, _⟩
  have hfa : f (ι x) = a := by
    simpa [φ] using hf.2 x
  have hf1 : f (ι y) = 1 := by
    simpa [φ, hyx] using hf.2 y
  have haeq : a = 1 := by
    rw [← hfa, ← hf1]
    exact congrArg f hEq
  exact ha1 haeq

/-- A nontrivial cyclic topological group has a nontrivial singleton topological generator. -/
theorem exists_nontrivial_singleton_topologicalGenerator
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [IsCyclic A] [Nontrivial A] :
    ∃ a : A, a ≠ 1 ∧ Generation.TopologicallyGenerates (G := A) ({a} : Set A) := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := A)
  have ha1 : a ≠ 1 := by
    intro hEq
    have hallOne : ∀ x : A, x = 1 := by
      intro x
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (ha x)
      simpa [hEq] using hn.symm
    exact not_subsingleton A ⟨fun x y => by rw [hallOne x, hallOne y]⟩
  refine ⟨a, ha1, ?_⟩
  rw [Generation.TopologicallyGenerates]
  apply top_unique
  intro x _
  exact Subgroup.le_topologicalClosure _ <| by
    simpa [Subgroup.zpowers_eq_closure] using ha x

/-- A concrete finite-group class containing a nontrivial finite cyclic group admits a
nontrivial topologically cyclic pro-`C` model. -/
theorem exists_nontrivial_topologicallyCyclic_proC_of_finiteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (hquot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A) :
    ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A)
      (_ : CompactSpace A) (_ : T2Space A) (_ : TotallyDisconnectedSpace A),
      ProCGroups.ProC.HasOpenNormalBasisInClass C A ∧
        ∃ a : A, a ≠ 1 ∧ Generation.TopologicallyGenerates (G := A) ({a} : Set A) := by
  rcases hcyc with ⟨A, _instGroupA, _instFiniteA, hCA, hAcyc, hAnontriv⟩
  let _ : TopologicalSpace A := ⊥
  let _ : DiscreteTopology A := ⟨rfl⟩
  have hAProC : ProCGroups.ProC.HasOpenNormalBasisInClass C A := by
    exact ProCGroups.ProC.HasOpenNormalBasisInClass.of_finite_discrete
      (C := C) (G := A) hquot hCA
  rcases exists_nontrivial_singleton_topologicalGenerator (A := A) with ⟨a, ha1, hgena⟩
  exact
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      hAProC, a, ha1, hgena⟩

/-- For a finite-rank free pro-`C` group, any generating family with the same finite cardinality
is again a converging-set basis. -/
theorem finite_generatingFamily_is_basis
    {X : Type u} {Y : Type u}
    [Finite X] [Finite Y]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F} {μ : Y → F}
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    (hcard : Cardinal.mk X = Cardinal.mk Y)
    (hgen : Generation.TopologicallyGenerates (G := F) (Set.range μ)) :
    IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) Y F μ := by
  classical
  have hXY : Nonempty (X ≃ Y) := by
    simpa [← Cardinal.eq] using hcard
  let eXY : X ≃ Y := Classical.choice hXY
  let ψ : X → F := fun x => μ (eXY x)
  have hψconv : FamilyConvergesToOneAlongOpenSubgroups (G := F) ψ := by
    exact FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain (G := F) ψ
  have hψgen : Generation.TopologicallyGenerates (G := F) (Set.range ψ) := by
    have hrange : Set.range ψ = Set.range μ := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨eXY x, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨eXY.symm y, by simp only [Equiv.apply_symm_apply, ψ]⟩
    simpa [hrange] using hgen
  rcases hι.existsUnique_lift hι.hasOpenNormalBasisInClass ψ hψconv hψgen with ⟨σ, hσ, hσuniq⟩
  have hrangeμ : Set.range μ ⊆ (σ.range : Set F) := by
    rintro z ⟨y, rfl⟩
    exact ⟨ι (eXY.symm y), by simpa [ψ] using hσ.2 (eXY.symm y)⟩
  have hσgen : Generation.TopologicallyGenerates (G := F) ((σ.range : Set F)) :=
    Generation.topologicallyGenerates_mono (G := F) hgen hrangeμ
  have hσclosed : IsClosed ((σ.range : Set F)) := by
    simpa using (isCompact_range hσ.1).isClosed
  have hσclosure_le : (σ.range : Subgroup F).topologicalClosure ≤ σ.range :=
    Subgroup.topologicalClosure_minimal _ le_rfl hσclosed
  have hσclosure_top : (σ.range : Subgroup F).topologicalClosure = ⊤ := by
    have htop :
        (Subgroup.closure (σ.range : Set F)).topologicalClosure = (⊤ : Subgroup F) := by
      simpa [Generation.TopologicallyGenerates] using hσgen
    have hclosure_eq : (σ.range : Subgroup F) = Subgroup.closure (σ.range : Set F) := by
      simpa using (Subgroup.closure_eq (σ.range)).symm
    rw [hclosure_eq]
    exact htop
  have hσrange_top : σ.range = ⊤ := by
    apply top_unique
    intro z hz
    have hz' : z ∈ ((σ.range : Subgroup F).topologicalClosure : Set F) := by
      rw [hσclosure_top]
      simp only [Subgroup.coe_top, mem_univ]
    exact hσclosure_le hz'
  have hσsurj : Function.Surjective σ := by
    intro z
    have hz : z ∈ (σ.range : Set F) := by
      simp only [hσrange_top, Subgroup.coe_top, mem_univ]
    simpa using hz
  let σc : ContinuousMonoidHom F F :=
    { toMonoidHom := σ
      continuous_toFun := hσ.1 }
  have hFG : _root_.ProCGroups.FiniteGeneration.TopologicallyFinitelyGenerated F := by
    let : Fintype Y := Fintype.ofFinite Y
    refine ⟨Finset.univ.image μ, ?_⟩
    simpa [Finset.coe_image] using hgen
  rcases
      (surjContinuousEndomorphismsAreAutomorphisms_of_topologicallyFinitelyGenerated
        (G := F)) hFG σc hσsurj with
    ⟨e, he⟩
  refine ⟨hι.hasOpenNormalBasisInClass, ?_, hgen, ?_⟩
  · exact FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain (G := F) μ
  · intro G _ _ _ _ _ _ hG φ hφ hgenφ
    let φX : X → G := fun x => φ (eXY x)
    have hφXconv : FamilyConvergesToOneAlongOpenSubgroups (G := G) φX := by
      exact FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain (G := G) φX
    have hφXgen : Generation.TopologicallyGenerates (G := G) (Set.range φX) := by
      have hrange : Set.range φX = Set.range φ := by
        ext z
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨eXY x, rfl⟩
        · rintro ⟨y, rfl⟩
          exact ⟨eXY.symm y, by simp only [Equiv.apply_symm_apply, φX]⟩
      simpa [hrange] using hgenφ
    rcases hι.existsUnique_lift hG φX hφXconv hφXgen with ⟨fX, hfX, hfXuniq⟩
    let fY : F →* G := fX.comp e.symm.toMonoidHom
    refine ⟨fY, ⟨hfX.1.comp e.symm.continuous, ?_⟩, ?_⟩
    · intro y
      have hpre : e.symm (μ y) = ι (eXY.symm y) := by
        apply e.injective
        calc
          e (e.symm (μ y)) = μ y := by simp only [ContinuousMulEquiv.apply_symm_apply]
          _ = σ (ι (eXY.symm y)) := by
              symm
              simpa [ψ] using hσ.2 (eXY.symm y)
          _ = e (ι (eXY.symm y)) := by
              have h := (he (ι (eXY.symm y))).symm
              change σ (ι (eXY.symm y)) = e (ι (eXY.symm y)) at h
              exact h
      calc
        fY (μ y) = fX (e.symm (μ y)) := rfl
        _ = fX (ι (eXY.symm y)) := by rw [hpre]
        _ = φX (eXY.symm y) := hfX.2 (eXY.symm y)
        _ = φ y := by simp only [Equiv.apply_symm_apply, φX]
    · intro g hg
      have hcomp : g.comp e.toMonoidHom = fX := by
        apply hfXuniq
        refine ⟨hg.1.comp e.continuous, ?_⟩
        intro x
        calc
          (g.comp e.toMonoidHom) (ι x) = g (e (ι x)) := rfl
          _ = g (σ (ι x)) := by
              have h := he (ι x)
              change e (ι x) = σ (ι x) at h
              exact congrArg g h
          _ = g (μ (eXY x)) := by
              exact congrArg g (by simpa [ψ] using hσ.2 x)
          _ = φ (eXY x) := hg.2 (eXY x)
          _ = φX x := rfl
      ext z
      have hz := congrArg (fun k : F →* G => k (e.symm z)) hcomp
      have hz' : g (e (e.symm z)) = fX (e.symm z) := by
        change (g.comp e.toMonoidHom) (e.symm z) = fX (e.symm z)
        exact hz
      calc
        g z = g (e (e.symm z)) := by
          exact congrArg g (e.apply_symm_apply z).symm
        _ = fX (e.symm z) := hz'
        _ = fY z := rfl

/-- Concrete finite-group-class specialization of `finite_generatingFamily_is_basis`. -/
theorem finite_generatingFamily_is_basis_of_finiteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u})
    {X : Type u} {Y : Type u}
    [Finite X] [Finite Y]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F} {μ : Y → F}
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (hcard : Cardinal.mk X = Cardinal.mk Y)
    (hgen : Generation.TopologicallyGenerates (G := F) (Set.range μ)) :
    IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) Y F μ := by
  exact finite_generatingFamily_is_basis
    (C := C)
    hι hcard hgen

/-- Concrete finite-group-class specialization when a nontrivial cyclic target is available. -/
theorem finite_generatingFamily_is_basis_of_finiteGroupClass_cyclic
    (C : ProCGroups.FiniteGroupClass.{u})
    (hquot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} {Y : Type u}
    [Finite X] [Finite Y]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F} {μ : Y → F}
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (hcard : Cardinal.mk X = Cardinal.mk Y)
    (hgen : Generation.TopologicallyGenerates (G := F) (Set.range μ)) :
    IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) Y F μ := by
  rcases exists_nontrivial_topologicallyCyclic_proC_of_finiteGroupClass C hquot hcyc with
    ⟨A, _instGroupA, _instTopA, _instTopGroupA, _instCompactA, _instT2A, _instTDA,
      hA, a, ha1, hgena⟩
  exact finite_generatingFamily_is_basis
    (C := C)
    hι hcard hgen

/--
If a continuous homomorphism has range containing a topological generating set, then it is
surjective between profinite groups.
-/
theorem surjective_hom_of_rangeContainsGeneratingSet
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [CompactSpace F]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {ι : X → G}
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range ι))
    {σ : F →* G} (hσ : Continuous σ)
    (hsub : Set.range ι ⊆ (σ.range : Set G)) :
    Function.Surjective σ := by
  have hσgen : Generation.TopologicallyGenerates (G := G) ((σ.range : Set G)) :=
    Generation.topologicallyGenerates_mono (G := G) hgen hsub
  have hσclosed : IsClosed ((σ.range : Set G)) := by
    simpa using (isCompact_range hσ).isClosed
  have hσclosure_le : (σ.range : Subgroup G).topologicalClosure ≤ σ.range :=
    Subgroup.topologicalClosure_minimal _ le_rfl hσclosed
  have hσclosure_top : (σ.range : Subgroup G).topologicalClosure = ⊤ := by
    have htop :
        (Subgroup.closure (σ.range : Set G)).topologicalClosure = (⊤ : Subgroup G) := by
      simpa [Generation.TopologicallyGenerates] using hσgen
    have hclosure_eq : (σ.range : Subgroup G) = Subgroup.closure (σ.range : Set G) := by
      simpa using (Subgroup.closure_eq (σ.range)).symm
    rw [hclosure_eq]
    exact htop
  have hσrange_top : σ.range = ⊤ := by
    apply top_unique
    intro z hz
    have hz' : z ∈ ((σ.range : Subgroup G).topologicalClosure : Set G) := by
      rw [hσclosure_top]
      simp only [Subgroup.coe_top, mem_univ]
    exact hσclosure_le hz'
  intro z
  have hz : z ∈ (σ.range : Set G) := by
    simp only [hσrange_top, Subgroup.coe_top, mem_univ]
  simpa using hz

/-- A topologically finitely generated free pro-`C` group on a converging set has finite basis,
provided `C` admits a nontrivial cyclic pro-`C` target. -/
theorem finite_of_topologicallyFinitelyGenerated_epimorphicallyFreeProCGroupOnConvergingSet
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hfg : FiniteGeneration.TopologicallyFinitelyGenerated F)
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    (hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A)
        (_ : CompactSpace A) (_ : T2Space A) (_ : TotallyDisconnectedSpace A),
    ProCGroups.ProC.HasOpenNormalBasisInClass C A ∧ ∃ a : A, a ≠ 1 ∧
          Generation.TopologicallyGenerates (G := A) ({a} : Set A)) :
    Finite X := by
  classical
  by_cases hXfin : Finite X
  · exact hXfin
  · have hXinf : Infinite X := by
      by_contra hXnotinf
      exact hXfin (not_infinite_iff_finite.mp hXnotinf)
    rcases
        (FiniteGeneration.topologicallyFinitelyGenerated_iff_exists_topologicallyGeneratedByAtMost
          (G := F)).mp hfg with
      ⟨_n, s, _hsle, hgen⟩
    have hsle : Cardinal.mk ↥s ≤ Cardinal.mk X := by
      exact (show Cardinal.mk ↥s < Cardinal.mk X from calc
        Cardinal.mk ↥s < Cardinal.aleph0 := by
          exact (Cardinal.mk_lt_aleph0_iff).2 (Finite.of_fintype ↥s)
        _ ≤ Cardinal.mk X := Cardinal.aleph0_le_mk X).le
    have hsle' : Cardinal.mk ↥s ≤ Cardinal.mk (Set.univ : Set X) := by
      simpa using hsle
    obtain ⟨p, _hpSub, hpCard⟩ := (Cardinal.le_mk_iff_exists_subset
      (c := Cardinal.mk ↥s) (s := (Set.univ : Set X))).1 hsle'
    have hpEquiv : Nonempty (p ≃ ↥s) := by
      simpa [← Cardinal.eq] using hpCard
    let e : p ≃ ↥s := Classical.choice hpEquiv
    have hpfinite : p.Finite :=
      Set.finite_coe_iff.mp (Finite.of_equiv (↥s) e.symm)
    let φ : X → F := fun x => if hx : x ∈ p then (e ⟨x, hx⟩ : F) else 1
    have hφconv : FamilyConvergesToOneAlongOpenSubgroups (G := F) φ := by
      intro U
      have hsubset : {x : X | φ x ∉ (U : Set F)} ⊆ p := by
        intro x hx
        by_cases hxp : x ∈ p
        · exact hxp
        · exfalso
          exact hx (by simp only [hxp, ↓reduceDIte, SetLike.mem_coe, one_mem, φ])
      exact hpfinite.subset hsubset
    have hφgen : Generation.TopologicallyGenerates (G := F) (Set.range φ) := by
      have hsub : (s : Set F) ⊆ Set.range φ := by
        intro z hz
        let a : ↥s := ⟨z, hz⟩
        refine ⟨(e.symm a).1, ?_⟩
        have hp : (e.symm a).1 ∈ p := (e.symm a).2
        simp only [hp, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply, φ, a]
      exact Generation.topologicallyGenerates_mono (G := F) hgen hsub
    rcases hι.existsUnique_lift hι.hasOpenNormalBasisInClass φ hφconv hφgen with ⟨σ, hσ, _⟩
    have hφsubσ : Set.range φ ⊆ (σ.range : Set F) := by
      rintro z ⟨x, rfl⟩
      exact ⟨ι x, hσ.2 x⟩
    have hσsurj : Function.Surjective σ :=
      surjective_hom_of_rangeContainsGeneratingSet
        hφgen hσ.1 hφsubσ
    let σc : ContinuousMonoidHom F F := {
      toMonoidHom := σ
      continuous_toFun := hσ.1
    }
    rcases
        (surjContinuousEndomorphismsAreAutomorphisms_of_topologicallyFinitelyGenerated
          (G := F))
          hfg σc hσsurj with
      ⟨eσ, heσ⟩
    have hσinj : Function.Injective σ := by
      intro a b hab
      have h' : eσ a = eσ b := by
        calc
          eσ a = σ a := by
            have h := heσ a
            change eσ a = σ a at h
            exact h
          _ = σ b := hab
          _ = eσ b := by
            have h := (heσ b).symm
            change σ b = eσ b at h
            exact h
      exact eσ.injective h'
    have hιinj : Function.Injective ι :=
      epimorphicallyFreeProCGroupOnConvergingSet_injective (hι := hι) hnontrivial
    have hφinj : Function.Injective φ := by
      intro x y hxy
      apply hιinj
      apply hσinj
      calc
        σ (ι x) = φ x := hσ.2 x
        _ = φ y := hxy
        _ = σ (ι y) := (hσ.2 y).symm
    have hφsub : Set.range φ ⊆ (s : Set F) ∪ ({1} : Set F) := by
      rintro z ⟨x, rfl⟩
      by_cases hxp : x ∈ p
      · left
        simp only [hxp, ↓reduceDIte, Subtype.coe_prop, φ]
      · right
        simp only [hxp, ↓reduceDIte, mem_singleton_iff, φ]
    have hφfin : (Set.range φ).Finite :=
      (s.finite_toSet.union (Set.finite_singleton (1 : F))).subset hφsub
    have hXlt : Cardinal.mk X < Cardinal.aleph0 := by
      calc
        Cardinal.mk X = Cardinal.mk (Set.range φ) := by
          simpa using (Cardinal.mk_range_eq φ hφinj).symm
        _ < Cardinal.aleph0 := by
          exact (Cardinal.mk_lt_aleph0_iff).2 hφfin.to_subtype
    exact False.elim (hXfin ((Cardinal.mk_lt_aleph0_iff).1 hXlt))

/-- A fixed free pro-`C` group on a set converging to `1` admits a continuous epimorphism onto any
profinite pro-`C` target generated by the image of its basis. -/
theorem exists_epimorphicallyFreeProCGroupOnConvergingSet_surjecting
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    (φ : X → G)
    (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) :
    ∃ ψ : F →* G, Continuous ψ ∧ Function.Surjective ψ ∧ ∀ x, ψ (ι x) = φ x := by
  rcases hF.existsUnique_lift hG φ hφ hgen with ⟨ψ, hψ, _⟩
  have hsub : Set.range φ ⊆ (ψ.range : Set G) := by
    rintro z ⟨x, rfl⟩
    exact ⟨ι x, hψ.2 x⟩
  have hψsurj : Function.Surjective ψ :=
    surjective_hom_of_rangeContainsGeneratingSet
      hgen hψ.1 hsub
  exact ⟨ψ, hψ.1, hψsurj, hψ.2⟩

/-- The pro-`C` completion of the abstract free group on a finite basis is free pro-`C` on that
basis. -/
theorem proCCompletionOfAbstractFreeGroup_is_free
    {X : Type u} [Finite X]
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    {Fhat : Type u} [Group Fhat] [TopologicalSpace Fhat] [IsTopologicalGroup Fhat]
    [CompactSpace Fhat] [T2Space Fhat] [TotallyDisconnectedSpace Fhat]
    {ι : FreeGroup X →ₜ* Fhat}
    (hι : ProCGroups.Completion.IsProCCompletion C (FreeGroup X) Fhat ι) :
    IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X Fhat
      (fun x => ι (FreeGroup.of x)) := by
  refine ⟨hι.hasOpenNormalBasisInClass, ?_, ?_, ?_⟩
  · exact FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain (G := Fhat)
      (fun x : X => ι (FreeGroup.of x))
  · have himage :
        ι '' Set.range (FreeGroup.of : X → FreeGroup X) =
          Set.range (fun x : X => ι (FreeGroup.of x)) := by
      calc
        ι '' Set.range (FreeGroup.of : X → FreeGroup X) =
            Set.range ((⇑ι) ∘ (FreeGroup.of : X → FreeGroup X)) :=
          (Set.range_comp ι (FreeGroup.of : X → FreeGroup X)).symm
        _ = Set.range (fun x : X => ι (FreeGroup.of x)) := by rfl
    have hclosure :
        Subgroup.closure (Set.range fun x : X => ι (FreeGroup.of x)) =
          ι.toMonoidHom.range := by
      calc
        Subgroup.closure (Set.range fun x : X => ι (FreeGroup.of x))
            = Subgroup.map ι.toMonoidHom
                (Subgroup.closure (Set.range (FreeGroup.of : X → FreeGroup X))) := by
              simpa [himage] using
                (ι.toMonoidHom.map_closure (Set.range (FreeGroup.of : X → FreeGroup X))).symm
        _ = ι.toMonoidHom.range := by
          rw [FreeGroup.closure_range_of X, MonoidHom.range_eq_map]
    rw [Generation.TopologicallyGenerates, hclosure]
    rw [SetLike.ext'_iff, Subgroup.topologicalClosure_coe, Subgroup.coe_top]
    simpa [DenseRange, MonoidHom.coe_range, dense_iff_closure_eq] using hι.denseRange
  · intro G _ _ _ _ _ _ hG φ _hφ hgen
    let φfree : FreeGroup X →ₜ* G :=
      { toMonoidHom := FreeGroup.lift φ
        continuous_toFun := by
          simpa using (continuous_of_discreteTopology : Continuous (FreeGroup.lift φ)) }
    let φhat : Fhat →ₜ* G := hι.lift hG φfree
    refine ⟨φhat.toMonoidHom, ?_, ?_⟩
    · refine ⟨φhat.continuous_toFun, ?_⟩
      intro x
      have hfac := congrArg (fun ψ : FreeGroup X →ₜ* G => ψ (FreeGroup.of x))
        (hι.lift_spec hG φfree)
      have hfree : φfree (FreeGroup.of x) = φ x := by
        change FreeGroup.lift φ (FreeGroup.of x) = φ x
        simp only [FreeGroup.lift_apply_of]
      exact hfac.trans hfree
    · intro g hg
      let gCont : Fhat →ₜ* G := { toMonoidHom := g, continuous_toFun := hg.1 }
      have hfac' : gCont.comp ι = φfree := by
        apply ContinuousMonoidHom.toMonoidHom_injective
        ext x
        change g (ι (FreeGroup.of x)) = FreeGroup.lift φ (FreeGroup.of x)
        exact (hg.2 x).trans (by simp only [FreeGroup.lift_apply_of])
      exact congrArg ContinuousMonoidHom.toMonoidHom (hι.lift_unique hG φfree hfac')

namespace IsEpimorphicallyFreeProCGroupOnConvergingSet

variable {X : Type v}
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable [CompactSpace F'] [T2Space F'] [TotallyDisconnectedSpace F']
variable {ι : X → F}

/-- The lift supplied by the corresponding free pro-`C` universal property. -/
noncomputable def lift
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) :
    F →* G :=
  Classical.choose (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ hgen))

/-- The universal-property lift has the prescribed values on the chosen generators. -/
theorem lift_spec
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) :
    Continuous (hι.lift hG φ hφ hgen) ∧
      ∀ x, hι.lift hG φ hφ hgen (ι x) = φ x :=
  Classical.choose_spec (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ hgen))

/-- The universal-property lift is unique among continuous maps with the prescribed values. -/
theorem lift_unique
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ))
    {f : F →* G} (hf : Continuous f) (hfac : ∀ x, f (ι x) = φ x) :
    f = hι.lift hG φ hφ hgen := by
  exact
    (hι.existsUnique_lift hG φ hφ hgen).unique ⟨hf, hfac⟩
      (hι.lift_spec hG φ hφ hgen)

/-- For a concrete finite-group class, the generated-target universal property of a free
pro-`C` group on a converging set extends any target map that converges to `1`.  This formulation
supports retractions that collapse all but finitely many basis elements. -/
theorem existsUnique_lift_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C G)
    (φ : X → G) (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ) :
    ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x := by
  classical
  let K : ClosedSubgroup G := Generation.closedSubgroupGenerated (G := G) (Set.range φ)
  let : CompactSpace ↥(K : Subgroup G) := by
    exact
      (show IsClosed (((K : Subgroup G) : Set G)) from
          K.2).isClosedEmbedding_subtypeVal.compactSpace
  let φK : X → ↥(K : Subgroup G) := Generation.closedSubgroupGeneratedMap (G := G) φ
  have hφKconv : FamilyConvergesToOneAlongOpenSubgroups (G := ↥(K : Subgroup G)) φK := by
    intro U
    have hU_nhds : ((U : Subgroup ↥(K : Subgroup G)) : Set ↥(K : Subgroup G)) ∈
        𝓝 (1 : ↥(K : Subgroup G)) :=
      U.isOpen'.mem_nhds U.one_mem'
    rcases
        (mem_nhds_subtype ((K : Subgroup G) : Set G) (1 : ↥(K : Subgroup G))
          ((U : Subgroup ↥(K : Subgroup G)) : Set ↥(K : Subgroup G))).1 hU_nhds with
      ⟨W₀, hW₀_nhds, hW₀U⟩
    rcases mem_nhds_iff.mp hW₀_nhds with ⟨W, hWU₀, hWopen, h1W⟩
    rcases hG W hWopen h1W with ⟨V, hVW, _hCV⟩
    have hsub :
        {x : X | φK x ∉ (U : Set ↥(K : Subgroup G))} ⊆
          {x : X | φ x ∉ ((V.toOpenSubgroup : OpenSubgroup G) : Set G)} := by
      intro x hx hxV
      exact hx (hW₀U (by
        change φ x ∈ W₀
        exact hWU₀ (hVW hxV)))
    exact (hφ V.toOpenSubgroup).subset hsub
  have hφKgen :
      Generation.TopologicallyGenerates (G := ↥(K : Subgroup G)) (Set.range φK) := by
    simpa [φK] using
      (Generation.closedSubgroupGeneratedMap_topologicallyGenerates (G := G) φ)
  have hK : ProCGroups.ProC.HasOpenNormalBasisInClass C ↥(K : Subgroup G) :=
    ProCGroups.ProC.HasOpenNormalBasisInClass.of_closedSubgroup hIso hSub hG K
  rcases hι.existsUnique_lift hK φK hφKconv hφKgen with ⟨fK, hfK, huniqK⟩
  let incl : ↥(K : Subgroup G) →* G := (K : Subgroup G).subtype
  let f : F →* G := incl.comp fK
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · exact continuous_subtype_val.comp hfK.1
  · intro x
    exact congrArg Subtype.val (hfK.2 x)
  · intro g hg
    have hgK_mem : ∀ y : F, g y ∈ (K : Subgroup G) := by
      intro y
      have hy :
          y ∈ (Generation.closedSubgroupGenerated (G := F) (Set.range ι) : Subgroup F) := by
        change y ∈ ((Subgroup.closure (Set.range ι)).topologicalClosure : Subgroup F)
        rw [hι.generates_range]
        simp only [Subgroup.mem_top]
      have hgy :=
        Generation.map_mem_closedSubgroupGenerated_image
          (G := F) (H := G)
          ({ toMonoidHom := g, continuous_toFun := hg.1 } : F →ₜ* G)
          (X := Set.range ι) hy
      have himage :
          (({ toMonoidHom := g, continuous_toFun := hg.1 } : F →ₜ* G) ''
              Set.range ι) = Set.range φ := by
        ext z
        constructor
        · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
          exact ⟨x, (hg.2 x).symm⟩
        · rintro ⟨x, rfl⟩
          exact ⟨ι x, ⟨x, rfl⟩, hg.2 x⟩
      change
        g y ∈ Generation.closedSubgroupGenerated
          (({ toMonoidHom := g, continuous_toFun := hg.1 } : F →ₜ* G) ''
            Set.range ι) at hgy
      rw [himage] at hgy
      exact hgy
    let gK : F →* ↥(K : Subgroup G) :=
      { toFun := fun y => ⟨g y, hgK_mem y⟩
        map_one' := by
          apply Subtype.ext
          simp only [map_one, OneMemClass.coe_one]
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp only [map_mul, MulMemClass.mk_mul_mk]}
    have hgKcont : Continuous gK := by
      exact Continuous.subtype_mk hg.1 (fun y => (gK y).2)
    have hgKfac : ∀ x, gK (ι x) = φK x := by
      intro x
      apply Subtype.ext
      exact hg.2 x
    have hgK_eq : gK = fK := huniqK gK ⟨hgKcont, hgKfac⟩
    ext y
    exact congrArg Subtype.val (congrArg (fun f : F →* ↥(K : Subgroup G) => f y) hgK_eq)

/-- Continuous-homomorphism form of
`existsUnique_lift_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass`. -/
theorem existsUnique_liftHom_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C G)
    (φ : X → G) (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ) :
    ∃! f : F →ₜ* G, ∀ x, f (ι x) = φ x := by
  rcases existsUnique_lift_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass
      C hIso hSub hι hG φ hφ with
    ⟨f, hf, huniq⟩
  let fc : F →ₜ* G :=
    { toMonoidHom := f
      continuous_toFun := hf.1 }
  refine ⟨fc, hf.2, ?_⟩
  intro g hg
  apply ContinuousMonoidHom.toMonoidHom_injective
  exact huniq g.toMonoidHom ⟨g.continuous, hg⟩

/-- In a free pro-`Σ` group with nonempty `Σ`, a free generator has no positive torsion. -/
theorem generator_pow_ne_one_of_sigma
    {σ : Set ℕ} (hσ : ∃ p, p ∈ σ ∧ Nat.Prime p)
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := (ProCGroups.FiniteGroupClass.sigmaGroup σ)) X F ι)
    (i : X) (N : ℕ) (hN : 0 < N) :
    (ι i) ^ N ≠ 1 := by
  classical
  rcases hσ with ⟨p, hpσ, hp⟩
  let M := p ^ (N + 1)
  have hMpos : 0 < M := pow_pos hp.pos (N + 1)
  have hsigmaM : ProCGroups.FiniteGroupClass.IsSigmaNumber σ M :=
    ProCGroups.FiniteGroupClass.IsSigmaNumber.prime_pow_of_mem
      (sigma := σ) (p := p) (k := N + 1) hpσ hp
  let T := ULift.{u} (Multiplicative (ZMod M))
  let : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  let φ : X → T :=
    fun j => if j = i then ULift.up (Multiplicative.ofAdd (1 : ZMod M)) else 1
  have hφconv : FamilyConvergesToOneAlongOpenSubgroups (G := T) φ := by
    intro U
    refine (Set.finite_singleton i).subset ?_
    intro j hj
    by_cases hji : j = i
    · simp only [hji, Set.mem_singleton_iff]
    · have hφj : φ j = 1 := by simp only [hji, ↓reduceIte, φ]
      have hmem : φ j ∈ (U : Set T) := by simp only [hφj, SetLike.mem_coe, one_mem]
      exact False.elim (hj hmem)
  have hTclass : ProCGroups.FiniteGroupClass.sigmaGroup σ T :=
    ProCGroups.FiniteGroupClass.sigmaGroup_cyclicZMod (sigma := σ) hMpos hsigmaM
  have hT :
      ProCGroups.ProC.HasOpenNormalBasisInClass
        (ProCGroups.FiniteGroupClass.sigmaGroup σ) T :=
    ProCGroups.ProC.HasOpenNormalBasisInClass.of_finite_discrete
      (C := ProCGroups.FiniteGroupClass.sigmaGroup σ)
      (G := T)
      (ProCGroups.FiniteGroupClass.sigmaGroup_quotientClosed σ)
      hTclass
  rcases hι.existsUnique_liftHom_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass
      (ProCGroups.FiniteGroupClass.sigmaGroup σ)
      (ProCGroups.FiniteGroupClass.sigmaGroup_isomClosed σ)
      (ProCGroups.FiniteGroupClass.sigmaGroup_subgroupClosed σ)
      hT φ hφconv with
    ⟨f, hf, _⟩
  intro hpow
  have hf_pow : f ((ι i) ^ N) = 1 := by simp only [hpow, map_one]
  have hcalc : f ((ι i) ^ N) = ULift.up (Multiplicative.ofAdd (N : ZMod M)) := by
    calc
      f ((ι i) ^ N) = (f (ι i)) ^ N := by simp only [map_pow]
      _ = (φ i) ^ N := by rw [hf i]
      _ = (ULift.up (Multiplicative.ofAdd (1 : ZMod M))) ^ N := by simp only [↓reduceIte, φ]
      _ = ULift.up (Multiplicative.ofAdd (N : ZMod M)) := by
        apply ULift.ext
        change (Multiplicative.ofAdd (1 : ZMod M)) ^ N =
          Multiplicative.ofAdd (N : ZMod M)
        change Multiplicative.ofAdd ((N : ℕ) • (1 : ZMod M)) =
          Multiplicative.ofAdd (N : ZMod M)
        simp only [nsmul_eq_mul, mul_one]
  have hlt_pow : N < p ^ (N + 1) :=
    lt_of_lt_of_le
      (Nat.lt_pow_self (n := N) (a := p) hp.one_lt)
      (Nat.pow_le_pow_right hp.pos (Nat.le_succ N))
  have hNmod : (N : ZMod M) ≠ 0 := by
    intro hzero
    have hdiv : M ∣ N := (ZMod.natCast_eq_zero_iff N M).mp hzero
    exact (Nat.not_dvd_of_pos_of_lt hN hlt_pow) hdiv
  have hofAdd_ne : ULift.up (Multiplicative.ofAdd (N : ZMod M)) ≠ (1 : T) := by
    intro h
    have hdown : Multiplicative.ofAdd (N : ZMod M) = 1 := congrArg ULift.down h
    have hz : (N : ZMod M) = 0 := by
      change Multiplicative.ofAdd (N : ZMod M) =
        Multiplicative.ofAdd (0 : ZMod M) at hdown
      exact Multiplicative.ofAdd.injective hdown
    exact hNmod hz
  exact hofAdd_ne (hcalc.symm.trans hf_pow)

/-- Integer-power form of `generator_pow_ne_one_of_sigma`. -/
theorem generator_zpow_ne_one_of_sigma
    {σ : Set ℕ} (hσ : ∃ p, p ∈ σ ∧ Nat.Prime p)
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := (ProCGroups.FiniteGroupClass.sigmaGroup σ)) X F ι)
    (i : X) (n : ℤ) (hn : n ≠ 0) :
    (ι i) ^ n ≠ 1 := by
  intro hzn
  have hnat_pos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  have hnat_ne :
      (ι i) ^ n.natAbs ≠ 1 :=
    hι.generator_pow_ne_one_of_sigma hσ i n.natAbs hnat_pos
  apply hnat_ne
  by_cases hnonneg : 0 ≤ n
  · have hnat : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hnonneg
    simpa [zpow_natCast, hnat] using hzn
  · have hneg : n < 0 := lt_of_not_ge hnonneg
    have hnat : (n.natAbs : ℤ) = -n := Int.ofNat_natAbs_of_nonpos hneg.le
    have hzn' : (ι i) ^ (-n) = 1 := by
      calc
        (ι i) ^ (-n) = ((ι i) ^ n)⁻¹ := by rw [zpow_neg]
        _ = 1 := by simp only [hzn, inv_one]
    simpa [zpow_natCast, hnat] using hzn'

/-- The continuous homomorphism supplied by the free pro-`C` universal property. -/
noncomputable def liftHom
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) :
    F →ₜ* G where
  toMonoidHom := hι.lift hG φ hφ hgen
  continuous_toFun := (hι.lift_spec hG φ hφ hgen).1

/-- Bundled version of `liftHom`, taking a converging generating map as a single argument. -/
noncomputable def liftConvergingGeneratingMap
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : ConvergingGeneratingMap X G) :
    F →ₜ* G :=
  hι.liftHom hG φ φ.convergesToOneAlongOpenSubgroups φ.generates

/-- The bundled lift has the prescribed value on each generator. -/
@[simp] theorem liftConvergingGeneratingMap_apply
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : ConvergingGeneratingMap X G) (x
        : X) :
    hι.liftConvergingGeneratingMap hG φ (ι x) = φ x := by
  change hι.lift hG φ φ.convergesToOneAlongOpenSubgroups φ.generates (ι x) = φ x
  exact (hι.lift_spec hG φ φ.convergesToOneAlongOpenSubgroups φ.generates).2 x

/-- `liftHom` has the prescribed value on each generator. -/
@[simp] theorem liftHom_apply
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) (x : X) :
    hι.liftHom hG φ hφ hgen (ι x) = φ x :=
  (hι.lift_spec hG φ hφ hgen).2 x

section FiniteSupportRetracts

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable [hVar : Fact (ProCGroups.FiniteGroupClass.Variety C)]
variable {X : Type v} [DecidableEq X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable {ι : X → F}

/-- The unique continuous endomorphism of a free pro-`C` group that keeps the finite set `S`
of basis elements and sends the remaining basis elements to `1`. -/
theorem existsUnique_collapseToFinset_of_finiteGroupClass
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    ∃! φ : F →ₜ* F, ∀ x, φ (ι x) = if x ∈ S then ι x else 1 := by
  have hconv :
      FamilyConvergesToOneAlongOpenSubgroups (G := F) (fun x => if x ∈ S then ι x else 1) := by
    intro U
    classical
    refine S.finite_toSet.subset ?_
    intro x hx
    by_cases hxS : x ∈ S
    · exact hxS
    · exfalso
      exact hx (by simp only [hxS, ↓reduceIte, SetLike.mem_coe, one_mem])
  exact
    hι.existsUnique_liftHom_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass
      C C.isomClosed hVar.out.subgroupClosed
      hι.hasOpenNormalBasisInClass (fun x => if x ∈ S then ι x else 1) hconv

/-- The finite-support retraction of a free pro-`C` group onto the closed subgroup generated by a
finite set of basis elements. -/
noncomputable def collapseToFinset
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    F →ₜ* F :=
  Classical.choose (ExistsUnique.exists (hι.existsUnique_collapseToFinset_of_finiteGroupClass S))

/-- Collapsing to a finite set fixes the selected generators. -/
@[simp] theorem collapseToFinset_apply_mem
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {S : Finset X} {x : X} (hx : x ∈ S) :
    hι.collapseToFinset S (ι x) = ι x := by
  simpa [hx, collapseToFinset] using
    (Classical.choose_spec
      (ExistsUnique.exists (hι.existsUnique_collapseToFinset_of_finiteGroupClass S)) x)

/-- Collapsing to a finite set sends every unselected generator to the identity. -/
@[simp] theorem collapseToFinset_apply_not_mem
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {S : Finset X} {x : X} (hx : x ∉ S) :
    hι.collapseToFinset S (ι x) = 1 := by
  simpa [hx, collapseToFinset] using
    (Classical.choose_spec
      (ExistsUnique.exists (hι.existsUnique_collapseToFinset_of_finiteGroupClass S)) x)

/-- Collapsing twice to the same finite set is the same as collapsing once. -/
@[simp] theorem collapseToFinset_idempotent
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    (hι.collapseToFinset S).comp (hι.collapseToFinset S) =
      hι.collapseToFinset S := by
  apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ S
  · simp only [ContinuousMonoidHom.comp_toFun, hx, collapseToFinset_apply_mem]
  · simp only [ContinuousMonoidHom.comp_toFun, hx, not_false_eq_true,
      collapseToFinset_apply_not_mem, map_one]

/-- A homomorphism that kills every basis element outside `S` is unchanged after precomposition
with the finite-support retraction. -/
theorem comp_collapseToFinset_eq_of_eq_one_outside
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {G : Type w} [Group G] [TopologicalSpace G] [T2Space G]
    (φ : F →ₜ* G) (S : Finset X)
    (hφ : ∀ x, x ∉ S → φ (ι x) = 1) :
    φ.comp (hι.collapseToFinset S) = φ := by
  apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ S
  · simp only [ContinuousMonoidHom.comp_toFun, hx, collapseToFinset_apply_mem]
  · simp only [ContinuousMonoidHom.comp_toFun, hx, not_false_eq_true,
      collapseToFinset_apply_not_mem, map_one,
  hφ x hx]

/-- The map from the free pro-`C` group onto the range of its finite-support retraction. -/
noncomputable def collapseToFinsetRange
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    F →ₜ* ↥((hι.collapseToFinset S : F →* F).range) :=
  { toMonoidHom := (hι.collapseToFinset S : F →* F).rangeRestrict
    continuous_toFun :=
      (hι.collapseToFinset S).continuous.subtype_mk (fun x => ⟨x, rfl⟩) }

/-- The inclusion of the range of a finite-support retraction back into the ambient free group. -/
noncomputable def collapseToFinsetInclusion
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    ↥((hι.collapseToFinset S : F →* F).range) →ₜ* F :=
  { toMonoidHom := ((hι.collapseToFinset S : F →* F).range).subtype
    continuous_toFun := continuous_subtype_val }

/-- The range of the finite-support retraction, viewed as the finite-basis retract. -/
abbrev FinsetSupportRetract
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) : Type u :=
  ↥((hι.collapseToFinset S : F →* F).range)

/-- The finite basis of the finite-support retract. -/
noncomputable def finsetSupportBasis
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    S → hι.FinsetSupportRetract S := by
  intro x
  refine ⟨ι x.1, ?_⟩
  exact ⟨ι x.1, hι.collapseToFinset_apply_mem x.2⟩

/-- The range of the finite-support retraction is closed. -/
theorem isClosed_range_collapseToFinset
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    IsClosed (((hι.collapseToFinset S : F →* F).range : Set F)) := by
  let r : F →ₜ* F := hι.collapseToFinset S
  let Fix : Subgroup F := (r : F →* F).eqLocus (MonoidHom.id F)
  have hFixClosed : IsClosed (Fix : Set F) := by
    change IsClosed {x : F | r x = x}
    exact isClosed_eq r.continuous continuous_id
  have hFixEq : Fix = (r : F →* F).range := by
    ext x
    constructor
    · intro hx
      refine ⟨x, ?_⟩
      change (r : F →* F) x = x at hx
      exact hx
    · rintro ⟨y, rfl⟩
      change r (r y) = r y
      exact congrArg (fun ψ : F →ₜ* F => ψ y) (hι.collapseToFinset_idempotent S)
  simpa [r, Fix, hFixEq] using hFixClosed

/-- The closed finite-support retract carries its canonical compact topology. -/
noncomputable instance instCompactSpaceFinsetSupportRetract
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    CompactSpace (hι.FinsetSupportRetract S) :=
  (hι.isClosed_range_collapseToFinset S).isClosedEmbedding_subtypeVal.compactSpace

/-- The finite-support retract again has an open-normal \(C\)-basis. -/
theorem hasOpenNormalBasisInClass_finsetSupportRetract
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (hι.FinsetSupportRetract S) := by
  exact
    ProCGroups.ProC.HasOpenNormalBasisInClass.of_isClosed_subgroup
      C.isomClosed hVar.out.subgroupClosed
      hι.hasOpenNormalBasisInClass ((hι.collapseToFinset S : F →* F).range)
      (hι.isClosed_range_collapseToFinset S)

/-- The finite-support retract is free pro-`C` on its retained finite basis. -/
theorem isFreeProCGroupOnConvergingSet_finsetSupportBasis
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C)
      S (hι.FinsetSupportRetract S) (hι.finsetSupportBasis S) := by
  let R : Type u := hι.FinsetSupportRetract S
  let B : S → R := hι.finsetSupportBasis S
  let rRange : F →ₜ* R := hι.collapseToFinsetRange S
  let rIncl : R →ₜ* F := hι.collapseToFinsetInclusion S
  refine ⟨hι.hasOpenNormalBasisInClass_finsetSupportRetract S, ?_, ?_, ?_⟩
  · simpa [B] using FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain (G := R) B
  · have hgen :
        Generation.TopologicallyGenerates (G := R) (Set.range B) := by
      let Img : Set R := rRange '' Set.range ι
      have hsurj : Function.Surjective rRange := by
        exact MonoidHom.rangeRestrict_surjective (hι.collapseToFinset S : F →* F)
      have hImgGen : Generation.TopologicallyGenerates (G := R) Img := by
        exact
          Generation.topologicallyGenerates_image_of_continuousSurjective
            (f := rRange.toMonoidHom) rRange.continuous hsurj hι.generates_range
      have hBsub : Set.range B ⊆ Img := by
        intro y hy
        rcases hy with ⟨x, rfl⟩
        refine ⟨ι x.1, ⟨x.1, rfl⟩, ?_⟩
        apply Subtype.ext
        change (hι.collapseToFinset S (ι x.1) : F) = ι x.1
        exact hι.collapseToFinset_apply_mem x.2
      have hImgSub : Img ⊆ ((Subgroup.closure (Set.range B) : Subgroup R) : Set R) := by
        intro y hy
        rcases hy with ⟨x, ⟨j, rfl⟩, rfl⟩
        by_cases hj : j ∈ S
        · exact
            Subgroup.subset_closure ⟨⟨j, hj⟩, by
              apply Subtype.ext
              change ι j = (hι.collapseToFinset S (ι j) : F)
              exact (hι.collapseToFinset_apply_mem hj).symm⟩
        · have hy1 : rRange (ι j) = 1 := by
            apply Subtype.ext
            change (hι.collapseToFinset S (ι j) : F) = 1
            exact hι.collapseToFinset_apply_not_mem hj
          rw [hy1]
          exact (Subgroup.closure (Set.range B)).one_mem
      have hclosureEq :
          Subgroup.closure Img = Subgroup.closure (Set.range B) := by
        apply le_antisymm
        · exact (Subgroup.closure_le (K := Subgroup.closure (Set.range B))).2 hImgSub
        · exact Subgroup.closure_mono hBsub
      change (Subgroup.closure (Set.range B)).topologicalClosure = ⊤
      change (Subgroup.closure Img).topologicalClosure = ⊤ at hImgGen
      rw [← hclosureEq]
      exact hImgGen
    simpa [B] using hgen
  · intro G _ _ _ _ _ _ hG φ hφ hgen
    let φext : X → G := fun x => if hx : x ∈ S then φ ⟨x, hx⟩ else 1
    have hφext : FamilyConvergesToOneAlongOpenSubgroups (G := G) φext := by
      intro U
      refine S.finite_toSet.subset ?_
      intro x hx
      by_cases hxS : x ∈ S
      · exact hxS
      · exfalso
        exact hx (by simp only [hxS, ↓reduceDIte, SetLike.mem_coe, one_mem, φext])
    have hφextgen : Generation.TopologicallyGenerates (G := G) (Set.range φext) := by
      have hsub : Set.range φ ⊆ Set.range φext := by
        intro y hy
        rcases hy with ⟨x, rfl⟩
        exact ⟨x.1, by simp only [x.2, ↓reduceDIte, Subtype.coe_eta, φext]⟩
      exact Generation.topologicallyGenerates_mono (G := G) hgen hsub
    let Φ : F →ₜ* G := hι.liftHom hG φext hφext hφextgen
    have hΦspec : ∀ x, Φ (ι x) = φext x := by
      intro x
      exact hι.liftHom_apply hG φext hφext hφextgen x
    let Φbar : R →ₜ* G :=
      { toMonoidHom := Φ.toMonoidHom.comp rIncl.toMonoidHom
        continuous_toFun := Φ.continuous.comp rIncl.continuous }
    have hΦbar : ∀ x : S, Φbar (B x) = φ x := by
      intro x
      change Φ (ι x.1) = φ x
      simpa [φext, B, Φbar, rIncl, collapseToFinsetInclusion, finsetSupportBasis] using
        hΦspec x.1
    refine ⟨Φbar.toMonoidHom, ⟨Φbar.continuous, hΦbar⟩, ?_⟩
    intro ψ hψ
    let ψc : R →ₜ* G :=
      { toMonoidHom := ψ
        continuous_toFun := hψ.1 }
    have hψcomp : ψc.comp rRange = Φ := by
      apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
      rintro _ ⟨x, rfl⟩
      by_cases hx : x ∈ S
      · have hψx : ψc (rRange (ι x)) = φ ⟨x, hx⟩ := by
          have hBasis : rRange (ι x) = B ⟨x, hx⟩ := by
            apply Subtype.ext
            change (hι.collapseToFinset S (ι x) : F) = ι x
            exact hι.collapseToFinset_apply_mem hx
          exact hBasis ▸ hψ.2 ⟨x, hx⟩
        have hΦx : Φ (ι x) = φ ⟨x, hx⟩ := by
          simpa [φext, hx] using hΦspec x
        exact hψx.trans hΦx.symm
      · have hrx : rRange (ι x) = 1 := by
          apply Subtype.ext
          change (hι.collapseToFinset S (ι x) : F) = 1
          exact hι.collapseToFinset_apply_not_mem hx
        have hΦx : Φ (ι x) = 1 := by
          simpa [φext, hx] using hΦspec x
        calc
          ψc (rRange (ι x)) = ψc 1 := by rw [hrx]
          _ = 1 := by simp only [map_one]
          _ = Φ (ι x) := hΦx.symm
    have hΦbarcomp : Φbar.comp rRange = Φ := by
      ext y
      change Φ (hι.collapseToFinset S y) = Φ y
      have hfix :
          Φ.comp (hι.collapseToFinset S) = Φ := by
        exact hι.comp_collapseToFinset_eq_of_eq_one_outside Φ S (by
          intro x hx
          simpa [φext, hx] using hΦspec x)
      exact congrArg (fun f : F →ₜ* G => f y) hfix
    have hsurj : Function.Surjective rRange := by
      exact MonoidHom.rangeRestrict_surjective (hι.collapseToFinset S : F →* F)
    ext z
    rcases hsurj z with ⟨y, rfl⟩
    have hEq : ψc.comp rRange = Φbar.comp rRange := hψcomp.trans hΦbarcomp.symm
    exact congrArg (fun f : F →ₜ* G => f y) hEq

/-- If `S ⊆ T`, then collapsing first to `T` and then to `S` is the same as
collapsing directly to `S`. This is the basic compatibility relation for the finite-basis
projections. -/
theorem collapseToFinset_small_comp_large_of_subset
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {S T : Finset X} (hST : S ⊆ T) :
    (hι.collapseToFinset S).comp (hι.collapseToFinset T) =
      hι.collapseToFinset S := by
  apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
  rintro _ ⟨x, rfl⟩
  by_cases hxS : x ∈ S
  · have hxT : x ∈ T := hST hxS
    simp only [ContinuousMonoidHom.comp_toFun, hxT, collapseToFinset_apply_mem, hxS]
  · by_cases hxT : x ∈ T
    · simp only [ContinuousMonoidHom.comp_toFun, hxT, collapseToFinset_apply_mem, hxS,
        not_false_eq_true,
collapseToFinset_apply_not_mem]
    · simp only [ContinuousMonoidHom.comp_toFun, hxT, not_false_eq_true,
        collapseToFinset_apply_not_mem, map_one,
hxS]

/-- If `S ⊆ T`, then collapsing to `S` and then to `T` is again the collapse to `S`.
Equivalently, the finite-support image for `S` is fixed by every larger finite-support
projection. -/
theorem collapseToFinset_large_comp_small_of_subset
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {S T : Finset X} (hST : S ⊆ T) :
    (hι.collapseToFinset T).comp (hι.collapseToFinset S) =
      hι.collapseToFinset S := by
  apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
  rintro _ ⟨x, rfl⟩
  by_cases hxS : x ∈ S
  · have hxT : x ∈ T := hST hxS
    simp only [ContinuousMonoidHom.comp_toFun, hxS, collapseToFinset_apply_mem, hxT]
  · simp only [ContinuousMonoidHom.comp_toFun, hxS, not_false_eq_true,
      collapseToFinset_apply_not_mem, map_one]

/-- The transition map from the finite-support retract for `T` to the one for `S`, for
`S ⊆ T`. It is the projection obtained by including the `T`-retract into the ambient free
pro-`C` group and then collapsing to `S`. -/
noncomputable def finsetSupportTransition
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {S T : Finset X} :
    hι.FinsetSupportRetract T →ₜ* hι.FinsetSupportRetract S :=
  { toMonoidHom := (hι.collapseToFinsetRange S).toMonoidHom.comp
      (hι.collapseToFinsetInclusion T).toMonoidHom
    continuous_toFun :=
      (hι.collapseToFinsetRange S).continuous.comp
        (hι.collapseToFinsetInclusion T).continuous }

/-- The transition from a larger finite support to a smaller one preserves the basis elements
indexed by the smaller support. -/
@[simp] theorem finsetSupportTransition_apply_basis
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {S T : Finset X} (hST : S ⊆ T) (x : S) :
    hι.finsetSupportTransition (S := S) (T := T)
        (hι.finsetSupportBasis T ⟨x.1, hST x.2⟩) =
      hι.finsetSupportBasis S x := by
  apply Subtype.ext
  change hι.collapseToFinset S (ι x.1) = ι x.1
  exact hι.collapseToFinset_apply_mem x.2

/-- Compatibility of the ambient projection `F → R_T` with the transition
`R_T → R_S`. -/
theorem finsetSupportTransition_comp_collapseToFinsetRange
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {S T : Finset X} (hST : S ⊆ T) :
    (hι.finsetSupportTransition (S := S) (T := T)).comp (hι.collapseToFinsetRange T) =
      hι.collapseToFinsetRange S := by
  ext x
  change hι.collapseToFinset S (hι.collapseToFinset T x) =
    hι.collapseToFinset S x
  exact congrArg (fun f : F →ₜ* F => f x)
    (hι.collapseToFinset_small_comp_large_of_subset hST)

end FiniteSupportRetracts

/-- Continuous homomorphisms out of a free pro-`C` group on a converging generating set are
determined by their values on the chosen generators. -/
theorem hom_ext
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
    {f g : F →ₜ* G} (hfg : ∀ x, f (ι x) = g (ι x)) :
    f = g := by
  exact Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
    (by
      intro y hy
      rcases hy with ⟨x, rfl⟩
      exact hfg x)

/-- The lift of the canonical generator map to the same free pro-`C` group is the identity. -/
@[simp 900] theorem lift_id
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι) :
    hι.lift hι.hasOpenNormalBasisInClass ι hι.convergesToOneAlongOpenSubgroups
        hι.generates_range = MonoidHom.id F := by
  symm
  exact hι.lift_unique hι.hasOpenNormalBasisInClass ι hι.convergesToOneAlongOpenSubgroups
      hι.generates_range continuous_id
    (by intro x; rfl)

end IsEpimorphicallyFreeProCGroupOnConvergingSet

/-- Packaged carrier with the epimorphic convergent-family lifting property. -/
structure EpimorphicallyFreeProCGroupOnConvergingSetData
    (C : ProCGroups.FiniteGroupClass) where
  /-- The index type of the distinguished converging generating family. -/
  basis : Type u
  /-- The bundled pro-`C` group generated by the distinguished family. -/
  carrier : ProCGrp C
  /-- The distinguished family of elements of the bundled carrier. -/
  inclusion : basis → carrier
  /--
  The inclusion is convergent and generating, and satisfies the epimorphic free pro-`C`
  universal property.
  -/
  isEpimorphicallyFree :
    IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) basis carrier inclusion

/--
The cardinality of a finite converging-set basis is the topological rank of the free pro-\(C\)
group, provided the finite class has a nontrivial cyclic quotient witness.
-/
theorem basisCard_eq_topologicalRank_of_finiteBasis
    (C : ProCGroups.FiniteGroupClass.{u})
    (hquot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    (Fdata : EpimorphicallyFreeProCGroupOnConvergingSetData
      (C := C))
    [Finite Fdata.basis] :
    Cardinal.mk Fdata.basis = Generation.topologicalRank Fdata.carrier := by
  classical
  let : Fintype Fdata.basis := Fintype.ofFinite Fdata.basis
  rcases exists_nontrivial_topologicallyCyclic_proC_of_finiteGroupClass C hquot hcyc with
    ⟨A, _instGroupA, _instTopA, _instTopGroupA, _instCompactA, _instT2A, _instTDA,
      hA, a, ha1, hgena⟩
  have hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A)
        (_ : CompactSpace A) (_ : T2Space A) (_ : TotallyDisconnectedSpace A),
        ProCGroups.ProC.HasOpenNormalBasisInClass C A ∧
          ∃ a : A, a ≠ 1 ∧ Generation.TopologicallyGenerates (G := A) ({a} : Set A) :=
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      hA, a, ha1, hgena⟩
  have hιinj : Function.Injective Fdata.inclusion :=
    epimorphicallyFreeProCGroupOnConvergingSet_injective
      Fdata.isEpimorphicallyFree hnontrivial
  have hfg : _root_.ProCGroups.FiniteGeneration.TopologicallyFinitelyGenerated Fdata.carrier := by
    refine ⟨Finset.univ.image Fdata.inclusion, ?_⟩
    simpa [Finset.coe_image] using Fdata.isEpimorphicallyFree.generates_range
  have hdle :
      Generation.topologicalRank Fdata.carrier ≤ (Fintype.card Fdata.basis : Cardinal) := by
    calc
      Generation.topologicalRank Fdata.carrier ≤ Cardinal.mk (Set.range Fdata.inclusion) := by
        exact Generation.topologicalRank_le_mk_of_topologicallyGenerates
          Fdata.isEpimorphicallyFree.generates_range
      _ = Cardinal.mk Fdata.basis := by
        simpa using (Cardinal.mk_range_eq Fdata.inclusion hιinj)
      _ = (Fintype.card Fdata.basis : Cardinal) := by simp only [Cardinal.mk_fintype]
  have hdlt : Generation.topologicalRank Fdata.carrier < Cardinal.aleph0 := by
    exact lt_of_le_of_lt hdle (Cardinal.natCast_lt_aleph0 (n := Fintype.card Fdata.basis))
  let d : ℕ := Cardinal.toNat (Generation.topologicalRank Fdata.carrier)
  have hdEq : Generation.topologicalRank Fdata.carrier = d := by
    symm
    exact Cardinal.cast_toNat_of_lt_aleph0 hdlt
  have hdleNat : d ≤ Fintype.card Fdata.basis := by
    simpa [d, Nat.card_eq_fintype_card] using
      Cardinal.toNat_le_toNat hdle
        (Cardinal.natCast_lt_aleph0 (n := Fintype.card Fdata.basis))
  by_cases hd0 : d = 0
  · have hdEq0 : Generation.topologicalRank Fdata.carrier = 0 := by simpa [d, hd0] using hdEq
    have hgen0 :
        _root_.ProCGroups.FiniteGeneration.TopologicallyGeneratedByAtMost
          (G := Fdata.carrier) 0 :=
      _root_.ProCGroups.FiniteGeneration.topologicallyGeneratedByAtMost_of_topologicalRank_eq_nat
        (G := Fdata.carrier) hdEq0
    rcases hgen0 with ⟨s, hs, hsgen⟩
    have hs0 : s.card = 0 := Nat.eq_zero_of_le_zero hs
    have hsempty : s = ∅ := Finset.card_eq_zero.mp hs0
    have htriv : ∀ x : Fdata.carrier, x = 1 := by
      intro x
      have hxmem :
            x ∈
              ((Subgroup.closure
                  (((s : Finset Fdata.carrier) : Set Fdata.carrier))).topologicalClosure :
                Set Fdata.carrier) := by
        rw [Generation.TopologicallyGenerates] at hsgen
        rw [hsgen]
        simp only [Subgroup.coe_top, mem_univ]
      simpa [hsempty, Subgroup.coe_topologicalClosure_bot, closure_singleton] using hxmem
    have hEmpty : IsEmpty Fdata.basis := by
      refine ⟨fun b => ?_⟩
      have hb1 : Fdata.inclusion b = 1 := htriv (Fdata.inclusion b)
      exact
        (one_not_mem_range_of_epimorphicallyFreeProCGroupOnConvergingSet
          (hι := Fdata.isEpimorphicallyFree) hnontrivial) ⟨b, hb1⟩
    have hcard0 : Cardinal.mk Fdata.basis = 0 := by simp only [Cardinal.mk_eq_zero]
    rw [hdEq0]
    exact hcard0
  · have hdPos : 0 < d := Nat.pos_of_ne_zero hd0
    rcases _root_.ProCGroups.FiniteGeneration.exists_generatingTuple_of_topologicalRank_le_of_finite
        (G := Fdata.carrier) hfg
        (show Generation.topologicalRank Fdata.carrier ≤ d by simp only [hdEq, le_refl]) with
      ⟨φ, hφgen⟩
    let i0 : Fin d := ⟨0, hdPos⟩
    have hdleNat' : Fintype.card (Fin d) ≤ Fintype.card Fdata.basis := by
      simpa using hdleNat
    have hEmb : Nonempty (Fin d ↪ Fdata.basis) := by
      exact Function.Embedding.nonempty_of_card_le (α := Fin d) (β := Fdata.basis) hdleNat'
    have hConst : Nonempty (Fdata.basis → Fin d) := ⟨fun _ => i0⟩
    rcases (Function.exists_surjective_iff).2 ⟨hConst, hEmb⟩ with ⟨q, hqsurj⟩
    let ψ : Fdata.basis → Fdata.carrier := fun b => φ (q b)
    have hψconv : FamilyConvergesToOneAlongOpenSubgroups (G := Fdata.carrier) ψ := by
      exact FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain (G := Fdata.carrier) ψ
    have hψrange : Set.range ψ = Set.range φ := by
      ext x
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨q b, rfl⟩
      · rintro ⟨i, rfl⟩
        rcases hqsurj i with ⟨b, rfl⟩
        exact ⟨b, rfl⟩
    have hψgen : Generation.TopologicallyGenerates (G := Fdata.carrier) (Set.range ψ) := by
      simpa [hψrange] using hφgen
    rcases Fdata.isEpimorphicallyFree.existsUnique_lift
      Fdata.isEpimorphicallyFree.hasOpenNormalBasisInClass ψ hψconv hψgen with
      ⟨σ, hσ, _⟩
    have hσsub : Set.range φ ⊆ (σ.range : Set Fdata.carrier) := by
      rintro z ⟨i, rfl⟩
      rcases hqsurj i with ⟨b, hb⟩
      refine ⟨Fdata.inclusion b, ?_⟩
      simpa [ψ, hb] using hσ.2 b
    have hσsurj : Function.Surjective σ := by
      have hσgen :
          Generation.TopologicallyGenerates (G := Fdata.carrier)
            ((σ.range : Set Fdata.carrier)) :=
        Generation.topologicallyGenerates_mono (G := Fdata.carrier) hφgen hσsub
      have hσclosed : IsClosed ((σ.range : Set Fdata.carrier)) := by
        simpa using (isCompact_range hσ.1).isClosed
      have hσclosure_le : (σ.range : Subgroup Fdata.carrier).topologicalClosure ≤ σ.range :=
        Subgroup.topologicalClosure_minimal _ le_rfl hσclosed
      have hσclosure_top : (σ.range : Subgroup Fdata.carrier).topologicalClosure = ⊤ := by
        have htop :
            (Subgroup.closure (σ.range : Set Fdata.carrier)).topologicalClosure =
              (⊤ : Subgroup Fdata.carrier) := by
          simpa [Generation.TopologicallyGenerates] using hσgen
        have hclosure_eq :
            (σ.range : Subgroup Fdata.carrier) =
              Subgroup.closure (σ.range : Set Fdata.carrier) := by
          simpa using (Subgroup.closure_eq (σ.range)).symm
        rw [hclosure_eq]
        exact htop
      have hσrange_top : σ.range = ⊤ := by
        apply top_unique
        intro z hz
        have hz' :
            z ∈
              ((σ.range : Subgroup Fdata.carrier).topologicalClosure :
                Set Fdata.carrier) := by
          rw [hσclosure_top]
          simp only [Subgroup.coe_top, mem_univ]
        exact hσclosure_le hz'
      intro z
      have hz : z ∈ (σ.range : Set Fdata.carrier) := by
        simp only [hσrange_top, Subgroup.coe_top, mem_univ]
      simpa using hz
    let σc : ContinuousMonoidHom Fdata.carrier Fdata.carrier :=
      { toMonoidHom := σ
        continuous_toFun := hσ.1 }
    rcases
        (surjContinuousEndomorphismsAreAutomorphisms_of_topologicallyFinitelyGenerated
          (G := Fdata.carrier) hfg σc hσsurj) with
      ⟨eσ, heσ⟩
    have hσinj : Function.Injective σ := by
      intro a b hab
      have h' : eσ a = eσ b := by
        calc
          eσ a = σ a := by
            have h := heσ a
            change eσ a = σ a at h
            exact h
          _ = σ b := hab
          _ = eσ b := by
            have h := (heσ b).symm
            change σ b = eσ b at h
            exact h
      exact eσ.injective h'
    have hqinj : Function.Injective q := by
      intro b₁ b₂ hb
      apply hιinj
      apply hσinj
      calc
        σ (Fdata.inclusion b₁) = ψ b₁ := hσ.2 b₁
        _ = φ (q b₁) := rfl
        _ = φ (q b₂) := by simp only [hb]
        _ = ψ b₂ := rfl
        _ = σ (Fdata.inclusion b₂) := (hσ.2 b₂).symm
    have hcardEq : Fintype.card Fdata.basis = d := by
      have hcardLe : Fintype.card Fdata.basis ≤ d := by
        simpa using Fintype.card_le_of_injective q hqinj
      exact le_antisymm hcardLe hdleNat
    calc
      Cardinal.mk Fdata.basis = (Fintype.card Fdata.basis : Cardinal) := by simp only
          [Cardinal.mk_fintype]
      _ = d := by exact_mod_cast hcardEq
      _ = Generation.topologicalRank Fdata.carrier := hdEq.symm


/--
For a finite discrete pointed space, removing the basepoint from the pointed generating family
gives a converging-set basis.
-/
theorem freeOnFinitePointedDiscreteSpace_has_convergingSetBasis
    {X : Type u} [TopologicalSpace X] [DiscreteTopology X] [Finite X] {x0 : X}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hι : IsEpimorphicallyPointedFreeProCGroupOn (C := C) X x0 F ι) :
    IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) {x : X // x ≠ x0} F (fun x => ι x) := by
  classical
  let μ : {x : X // x ≠ x0} → F := fun x => ι x
  refine ⟨hι.hasOpenNormalBasisInClass, ?_, ?_, ?_⟩
  · exact FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain (G := F) μ
  · have hrange : Set.range ι = Set.range μ ∪ ({1} : Set F) := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        by_cases hx : x = x0
        · right
          simpa [hx] using hι.map_base
        · left
          exact ⟨⟨x, hx⟩, rfl⟩
      · intro hz
        rcases hz with hz | hz
        · rcases hz with ⟨x, rfl⟩
          exact ⟨x, rfl⟩
        · exact ⟨x0, hι.map_base.trans (by simpa using hz.symm)⟩
    have hgen' :
        Generation.TopologicallyGenerates (G := F) (Set.range μ ∪ ({1} : Set F)) := by
      simpa [μ, hrange] using hι.generates_range
    exact (Generation.topologicallyGenerates_union_one_iff (G := F) (X := Set.range μ)).1 hgen'
  · intro G _ _ _ _ _ _ hG φ _hφconv hgenφ
    let φhat : X → G := fun x => if h : x = x0 then 1 else φ ⟨x, h⟩
    have hφhat : Continuous φhat := continuous_of_discreteTopology
    have hφhat0 : φhat x0 = 1 := by
      simp only [ne_eq, ↓reduceDIte, φhat]
    have hrange : Set.range φhat = Set.range φ ∪ ({1} : Set G) := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        by_cases hx : x = x0
        · right
          simp only [ne_eq, hx, ↓reduceDIte, mem_singleton_iff, φhat]
        · left
          exact ⟨⟨x, hx⟩, by simp only [ne_eq, hx, ↓reduceDIte, φhat]⟩
      · intro hz
        rcases hz with hz | hz
        · rcases hz with ⟨x, rfl⟩
          exact ⟨x, by simp only [ne_eq, x.2, ↓reduceDIte, Subtype.coe_eta, φhat]⟩
        · exact ⟨x0, by simpa [φhat] using hz.symm⟩
    have hφhatgen :
        Generation.TopologicallyGenerates (G := G) (Set.range φhat) := by
      have hgen' :
          Generation.TopologicallyGenerates (G := G) (Set.range φ ∪ ({1} : Set G)) := by
        exact (Generation.topologicallyGenerates_union_one_iff (G := G) (X := Set.range φ)).2 hgenφ
      simpa [φhat, hrange] using hgen'
    rcases hι.existsUnique_lift hG φhat hφhat hφhat0 hφhatgen with ⟨f, hf, huniq⟩
    refine ⟨f, ⟨hf.1, ?_⟩, ?_⟩
    · intro x
      simpa [μ, φhat, x.2] using hf.2 (x : X)
    · intro g hg
      apply huniq g
      refine ⟨hg.1, ?_⟩
      intro x
      by_cases hx : x = x0
      · calc
          g (ι x) = g (ι x0) := by rw [hx]
          _ = g 1 := by rw [hι.map_base]
          _ = 1 := map_one g
          _ = φhat x := by simp only [ne_eq, hx, ↓reduceDIte, φhat]
      · simpa [μ, φhat, hx] using hg.2 ⟨x, hx⟩

/-- For a finite discrete pointed space, the resulting converging-set basis is finite. -/
theorem freeOnFinitePointedDiscreteSpace_has_finiteConvergingSetBasis
    {X : Type u} [TopologicalSpace X] [DiscreteTopology X] [Finite X] {x0 : X}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hι : IsEpimorphicallyPointedFreeProCGroupOn (C := C) X x0 F ι) :
    ∃ Fdata : EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} (C := C),
      Nonempty (Fdata.carrier ≃ₜ* F) ∧ Finite Fdata.basis := by
  let B : Type u := {x : X // x ≠ x0}
  let Fdata : EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} (C := C) :=
    { basis := B
      carrier := ProCGrp.of C (ProfiniteGrp.of F) hι.hasOpenNormalBasisInClass
      inclusion := fun x => ι x
      isEpimorphicallyFree :=
        freeOnFinitePointedDiscreteSpace_has_convergingSetBasis
          (C := C) (X := X) (x0 := x0) (F := F) (ι := ι) hι }
  refine ⟨Fdata, ⟨ContinuousMulEquiv.refl F⟩, ?_⟩
  dsimp [Fdata, B]
  infer_instance

end

end ProCGroups.FreeProC
