/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.DifferentialModule.Universal

/-!
# Fox differential: discrete — differential module — boundary

The principal declarations in this module are:

- `groupRingBoundary`
  The standard map \(G \to \mathbb{Z}[H]\), \(g \mapsto \psi(g)-1\) is viewed as a differential map.
- `groupRingBoundaryHom`
  The Fox boundary is itself a crossed differential.
- `groupRingBoundary_one`
  The Fox boundary vanishes at the identity.
- `groupRingBoundary_eq_zero_of_mem_ker`
  The Fox boundary is zero on elements in the kernel of \(\psi\).
-/

namespace FoxDifferential

noncomputable section

variable {H G : Type*} [Group H] [Group G]

/--
The standard map \(G \to \mathbb{Z}[H]\), \(g \mapsto \psi(g)-1\) is viewed as a differential
map.
-/
def groupRingBoundary (ψ : G →* H) (g : G) : GroupRing H :=
  MonoidAlgebra.of ℤ H (ψ g) - 1

/-- The Fox boundary vanishes at the identity. -/
@[simp]
theorem groupRingBoundary_one (ψ : G →* H) :
    groupRingBoundary ψ (1 : G) = 0 := by
  simp only [groupRingBoundary, map_one, groupRing_of_one (H := H), sub_self]

/-- The Fox boundary is zero on elements in the kernel of \(\psi\). -/
@[simp]
theorem groupRingBoundary_eq_zero_of_mem_ker (ψ : G →* H) {g : G} (hg : ψ g = 1) :
    groupRingBoundary ψ g = 0 := by
  rw [groupRingBoundary, hg, groupRing_of_one (H := H)]
  simp only [sub_self]

/-- The Fox boundary vanishes on the kernel subgroup of \(\psi\). -/
@[simp]
theorem groupRingBoundary_subtype_ker (ψ : G →* H) (g : ψ.ker) :
    groupRingBoundary ψ g = 0 :=
  groupRingBoundary_eq_zero_of_mem_ker (ψ := ψ) g.2

/-- The Fox boundary is itself a crossed differential. -/
def groupRingBoundaryHom (ψ : G →* H) : DifferentialHom ψ (GroupRing H) where
  toFun := groupRingBoundary ψ
  map_mul' := by
    intro g₁ g₂
    simp only [scalarCrossedAction_apply, groupRingBoundary, map_mul,
      MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one, sub_eq_add_neg,
      add_comm, groupRingScalar_apply, smul_eq_mul, mul_add, mul_neg, add_assoc,
      add_neg_cancel_comm_assoc]

/-- The bundled group-ring boundary homomorphism evaluates to the usual Fox boundary. -/
@[simp]
theorem groupRingBoundaryHom_apply (ψ : G →* H) (g : G) :
    groupRingBoundaryHom ψ g = groupRingBoundary ψ g :=
  rfl

/-- Group-ring functoriality carries Fox boundaries to Fox boundaries. -/
@[simp]
theorem groupRingMap_groupRingBoundary {K : Type*} [Group K]
    (φ : H →* K) (ψ : G →* H) (g : G) :
    groupRingMap φ (groupRingBoundary ψ g) = groupRingBoundary (φ.comp ψ) g := by
  simp only [groupRingBoundary, MonoidAlgebra.of_apply, map_sub, groupRingMap_single, map_one,
  MonoidHom.coe_comp, Function.comp_apply]

/--
The universal boundary map \(A_{\psi}\ \to \mathbb{Z}[H]\), \(universalDifferential(g) \mapsto
\psi(g) - 1\).
-/
def toGroupRing (ψ : G →* H) : DifferentialModule ψ →ₗ[GroupRing H] GroupRing H :=
  differentialModuleLift (A := GroupRing H) ψ (groupRingBoundaryHom ψ)

/-- The universal boundary sends universalDifferential g to \([\psi(g)] - 1\). -/
theorem toGroupRing_d (ψ : G →* H) (g : G) :
    toGroupRing ψ (universalDifferential ψ g) = groupRingBoundary ψ g := by
  simpa only [toGroupRing, groupRingBoundaryHom_apply] using
    differentialModuleLift_d (A := GroupRing H) ψ (groupRingBoundaryHom ψ) g


/-- The standard group-ring generator \(h-1\) appearing in Fox boundary formulas. -/
def augmentationGenerator (H : Type*) [Group H] (h : H) : GroupRing H :=
  MonoidAlgebra.of Int H h - 1

/-- The standard augmentation generator at the identity is zero. -/
@[simp]
theorem augmentationGenerator_one (H : Type*) [Group H] :
    augmentationGenerator H (1 : H) = 0 := by
  simp only [augmentationGenerator, groupRing_of_one (H := H), sub_self]

/-- The augmentation generator is the identity-coefficient Fox boundary. -/
@[simp]
theorem augmentationGenerator_eq_groupRingBoundary (H : Type*) [Group H] (h : H) :
    augmentationGenerator H h = groupRingBoundary (MonoidHom.id H) h :=
  rfl

/-- Group-ring functoriality carries augmentation generators to augmentation generators. -/
@[simp]
theorem groupRingMap_augmentationGenerator {K : Type*} [Group K]
    (φ : H →* K) (h : H) :
    groupRingMap φ (augmentationGenerator H h) = augmentationGenerator K (φ h) := by
  simp only [augmentationGenerator, MonoidAlgebra.of_apply, map_sub, groupRingMap_single, map_one]


end

end FoxDifferential
