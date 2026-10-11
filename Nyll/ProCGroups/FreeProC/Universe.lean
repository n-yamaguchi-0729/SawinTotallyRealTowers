/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FreeProC.Basic

/-!
# Universe-polymorphic targets for free pro-\(C\) groups

The original IsFreeProCGroup API keeps the source, free group, finite-group class, and target in
one universe. This module factors the universal property for one fixed target into
HasFreeLiftTo, then supplies an explicit extension whose target lives in an independent
universe. Cross-universe membership is expressed by FiniteGroupClass.MemAcrossUniverses, so no
ULift appears in the public universal property.

An ordinary IsFreeProCGroup yields this extension only in its native target universe. There is
deliberately no theorem promoting it to every target universe: such a promotion is not a
consequence of the same-universe universal property.
-/

open Set
open scoped Topology

namespace ProCGroups.FreeProC

universe u v

open ProCGroups

variable {C : FiniteGroupClass.{u}}

/-- The universal extension property from F to one fixed pro-\(C\) target G.

Keeping this target-specific property separate lets constructions prove exactly the
cross-universe lifting statement they support, without claiming a nonexistent automatic
promotion from the native universal property. -/
def HasFreeLiftTo
    {X : Type u} [TopologicalSpace X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (ι : X → F)
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : Prop :=
  ProC.HasOpenNormalBasisInClassAcrossUniverses C G →
    ∀ (φ : X → G), Continuous φ →
      ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x

namespace HasFreeLiftTo

variable {X : Type u} [TopologicalSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {ι : X → F}
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Extend a continuous generator map to the fixed target. -/
noncomputable def lift (h : HasFreeLiftTo (C := C) ι G)
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ) : F →* G :=
  Classical.choose (ExistsUnique.exists (h hG φ hφ))

/-- The fixed-target lift is continuous and has the prescribed generator values. -/
theorem lift_spec (h : HasFreeLiftTo (C := C) ι G)
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ) :
    Continuous (h.lift hG φ hφ) ∧ ∀ x, h.lift hG φ hφ (ι x) = φ x :=
  Classical.choose_spec (ExistsUnique.exists (h hG φ hφ))

/-- The fixed-target lift is unique among continuous homomorphisms with the prescribed values. -/
theorem lift_unique (h : HasFreeLiftTo (C := C) ι G)
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ)
    {f : F →* G} (hf : Continuous f) (hfac : ∀ x, f (ι x) = φ x) :
    f = h.lift hG φ hφ :=
  (h hG φ hφ).unique ⟨hf, hfac⟩ (h.lift_spec hG φ hφ)

/-- Bundle the fixed-target lift as a continuous monoid homomorphism. -/
noncomputable def liftHom (h : HasFreeLiftTo (C := C) ι G)
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ) : F →ₜ* G where
  toMonoidHom := h.lift hG φ hφ
  continuous_toFun := (h.lift_spec hG φ hφ).1

end HasFreeLiftTo

/-- The free pro-\(C\) universal property for targets in an explicitly independent universe.

Lean cannot quantify over universe levels inside a proposition, so the target universe v is a
universe parameter of this structure. The native universal property is retained as a parent, so
this stronger witness is directly usable anywhere an IsFreeProCGroup is expected. -/
structure IsFreeProCGroupForTargetUniverse
    {X : Type u} [TopologicalSpace X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (ι : X → F) : Prop extends IsFreeProCGroup (C := C) ι where
  /--
  For every pro-`C` target in universe `v`, continuous maps from `X` extend uniquely to
  continuous homomorphisms from `F`.
  -/
  hasFreeLiftTo :
    ∀ {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G],
      HasFreeLiftTo (C := C) ι G

namespace IsFreeProCGroupForTargetUniverse

variable {X : Type u} [TopologicalSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable {ι : X → F}

/-- Extend a continuous generator map to a homomorphism into a target in the chosen target
universe. -/
noncomputable def lift (hι : IsFreeProCGroupForTargetUniverse.{u, v} (C := C) ι)
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ) : F →* G :=
  (hι.hasFreeLiftTo (G := G)).lift hG φ hφ

/-- The cross-universe lift is continuous and has the prescribed generator values. -/
theorem lift_spec (hι : IsFreeProCGroupForTargetUniverse.{u, v} (C := C) ι)
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ) :
    Continuous (hι.lift hG φ hφ) ∧
      ∀ x, hι.lift hG φ hφ (ι x) = φ x :=
  (hι.hasFreeLiftTo (G := G)).lift_spec hG φ hφ

/-- The cross-universe lift is unique among continuous homomorphisms with the prescribed values. -/
theorem lift_unique (hι : IsFreeProCGroupForTargetUniverse.{u, v} (C := C) ι)
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ)
    {f : F →* G} (hf : Continuous f) (hfac : ∀ x, f (ι x) = φ x) :
    f = hι.lift hG φ hφ := by
  exact (hι.hasFreeLiftTo (G := G)).lift_unique hG φ hφ hf hfac

/-- Bundle the cross-universe lift as a continuous monoid homomorphism. -/
noncomputable def liftHom (hι : IsFreeProCGroupForTargetUniverse.{u, v} (C := C) ι)
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProC.HasOpenNormalBasisInClassAcrossUniverses C G)
    (φ : X → G) (hφ : Continuous φ) : F →ₜ* G where
  toMonoidHom := hι.lift hG φ hφ
  continuous_toFun := (hι.lift_spec hG φ hφ).1

end IsFreeProCGroupForTargetUniverse

namespace IsFreeProCGroup

variable {X : Type u} [TopologicalSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable {ι : X → F}

/-- The ordinary universal property, viewed as a fixed-target property in its native universe. -/
theorem hasFreeLiftTo (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    HasFreeLiftTo (C := C) ι G := by
  intro hG φ hφ
  exact hι.existsUnique_lift
    (ProC.hasOpenNormalBasisInClassAcrossUniverses_iff.1 hG) φ hφ

/-- In the native target universe, the original property yields the explicit
target-universe property. -/
theorem toForTargetUniverse (hι : IsFreeProCGroup (C := C) ι) :
    IsFreeProCGroupForTargetUniverse.{u, u} (C := C) ι where
  toIsFreeProCGroup := hι
  hasFreeLiftTo := hι.hasFreeLiftTo

end IsFreeProCGroup

end ProCGroups.FreeProC
