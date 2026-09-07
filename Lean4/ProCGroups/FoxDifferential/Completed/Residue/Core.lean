import ProCGroups.FoxDifferential.Common.CrossedDifferentialModule
import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.System.CompletionMap

set_option autoImplicit false

/-!
# Fox differential: completed — residue — core

The principal declarations in this module are:

- `ResidueGroupRing`
  The residue group ring \((\mathbb{Z}/n\mathbb{Z})[H]\).
- `residueGroupRingScalar`
  The coefficient homomorphism \(G \to (\mathbb{Z}/n\mathbb{Z})[H]\) induced by a group homomorphism
  \(\psi: G \to H\).
- `residueGroupRingScalar_apply`
  The residue coefficient homomorphism sends a group element to the residue group-ring basis element
  of its image.
- `residueGroupRingBoundary_one`
  The residue Fox boundary vanishes at the identity.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v

/-- The residue group ring \((\mathbb{Z}/n\mathbb{Z})[H]\). -/
abbrev ResidueGroupRing (n : ℕ) (H : Type*) : Type _ :=
  ModNCompletedGroupRing n H

section Basic

variable {G : Type u} {H : Type v} [Group G] [Group H]

/--
The coefficient homomorphism \(G \to (\mathbb{Z}/n\mathbb{Z})[H]\) induced by a group
homomorphism \(\psi: G \to H\).
-/
def residueGroupRingScalar (n : ℕ) (ψ : G →* H) : G →* ResidueGroupRing n H :=
  (MonoidAlgebra.of (ModNCompletedCoeff n) H).comp ψ

/--
The residue coefficient homomorphism sends a group element to the residue group-ring basis
element of its image.
-/
@[simp]
theorem residueGroupRingScalar_apply (n : ℕ) (ψ : G →* H) (g : G) :
    residueGroupRingScalar n ψ g =
      (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ g) : ResidueGroupRing n H) :=
  rfl

/-- The residue universal differential module attached to \(\psi : G \to H\). -/
abbrev ResidueDifferentialModule (n : ℕ) (ψ : G →* H) : Type _ :=
  CrossedDifferentialModule (residueGroupRingScalar n ψ)

/-- The universal residue crossed homomorphism. -/
def residueUniversalDifferential (n : ℕ) (ψ : G →* H) :
    ScalarCrossedHom (residueGroupRingScalar n ψ) (ResidueDifferentialModule n ψ) :=
  universalCrossedHom (residueGroupRingScalar n ψ)

/-- The residue Fox boundary \(g \mapsto [\psi(g)] - 1\), bundled as a crossed homomorphism. -/
def residueGroupRingBoundary (n : ℕ) (ψ : G →* H) :
    ScalarCrossedHom (residueGroupRingScalar n ψ) (ResidueGroupRing n H) where
  toFun g := MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ g) - 1
  map_mul' := by
    intro g h
    simp only [scalarCrossedAction_apply, map_mul, MonoidAlgebra.of_apply,
      MonoidAlgebra.single_mul_single, mul_one, sub_eq_add_neg, add_comm,
      residueGroupRingScalar_apply, smul_eq_mul, mul_add, mul_neg, add_assoc,
      add_neg_cancel_comm_assoc]

/-- The residue Fox boundary vanishes at the identity. -/
@[simp]
theorem residueGroupRingBoundary_one (n : ℕ) (ψ : G →* H) :
    residueGroupRingBoundary n ψ (1 : G) = 0 := by
  exact ScalarCrossedHom.map_one (residueGroupRingBoundary n ψ)

section UniversalProperty

variable (n : ℕ)
variable {A : Type*} [AddCommGroup A] [Module (ResidueGroupRing n H) A]

/-- The universal linear map induced by a residue crossed differential. -/
def residueDifferentialModuleLift
    (ψ : G →* H)
    (delta : ScalarCrossedHom (residueGroupRingScalar n ψ) A) :
    ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H] A :=
  crossedHomModuleLift (A := A) (residueGroupRingScalar n ψ) delta

/--
The residue universal lift evaluates on the universal differential as the original crossed
differential.
-/
@[simp]
theorem residueDifferentialModuleLift_universal
    (ψ : G →* H) (delta : ScalarCrossedHom (residueGroupRingScalar n ψ) A)
    (g : G) :
    residueDifferentialModuleLift (A := A) n ψ delta
        (residueUniversalDifferential n ψ g) =
      delta g := by
  exact crossedHomModuleLift_universal
    (A := A) (residueGroupRingScalar n ψ) delta g

/--
Linear maps out of the residue universal module are equal when they agree on universal residue
differentials.
-/
@[ext]
theorem residueDifferentialModuleHom_ext
    (ψ : G →* H)
    {f h : ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H] A}
    (hfh : ∀ g, f (residueUniversalDifferential n ψ g) =
      h (residueUniversalDifferential n ψ g)) :
    f = h := by
  exact crossedDifferentialModuleHom_ext (A := A) (residueGroupRingScalar n ψ) hfh

/-- Existence and uniqueness of the linear map representing a residue crossed differential. -/
theorem existsUnique_residueDifferentialModuleLift
    (ψ : G →* H) (delta : ScalarCrossedHom (residueGroupRingScalar n ψ) A) :
    ∃! f : ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H] A,
      ∀ g, f (residueUniversalDifferential n ψ g) = delta g := by
  exact existsUnique_crossedHomModuleLift
    (A := A) (residueGroupRingScalar n ψ) delta

/-- Residue crossed homomorphisms are represented by the corresponding universal residue module. -/
def residueCrossedHomEquivLinearMap (ψ : G →* H) :
    ScalarCrossedHom (residueGroupRingScalar n ψ) A ≃
      (ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H] A) :=
  crossedHomModuleEquivLinearMap (A := A) (residueGroupRingScalar n ψ)

/--
The universal residue Fox boundary map from the residue differential module to the residue group
ring.
-/
def residueToGroupRing (ψ : G →* H) :
    ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H] ResidueGroupRing n H :=
  residueDifferentialModuleLift (A := ResidueGroupRing n H) n ψ
    (residueGroupRingBoundary n ψ)

/-- The universal residue Fox boundary sends \(d g\) to \([\psi(g)] - 1\). -/
@[simp]
theorem residueToGroupRing_universal (ψ : G →* H) (g : G) :
    residueToGroupRing n ψ (residueUniversalDifferential n ψ g) =
      residueGroupRingBoundary n ψ g := by
  exact residueDifferentialModuleLift_universal
    (A := ResidueGroupRing n H) n ψ
    (residueGroupRingBoundary n ψ) g

/-- Existence and uniqueness of the universal residue Fox boundary map. -/
theorem existsUnique_residueToGroupRing (ψ : G →* H) :
    ∃! f : ResidueDifferentialModule n ψ →ₗ[ResidueGroupRing n H] ResidueGroupRing n H,
      ∀ g, f (residueUniversalDifferential n ψ g) =
        residueGroupRingBoundary n ψ g := by
  exact existsUnique_residueDifferentialModuleLift
    (A := ResidueGroupRing n H) n ψ
    (residueGroupRingBoundary n ψ)

end UniversalProperty

end Basic

end

end FoxDifferential
