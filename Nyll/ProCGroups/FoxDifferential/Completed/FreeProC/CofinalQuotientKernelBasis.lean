/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.QuotientKernelBasis

/-!
# Fox differential: completed — free pro-\(C\) — cofinal quotient kernel basis

The principal declarations in this module are:

- `HasIdentityQuotientKernelNeighbourhoodBasis.reindex_of_ker_le`
  Reindex an identity-neighborhood quotient-kernel basis along a cofinal refinement of kernels. The
  hypothesis says that every kernel in the original quotient family contains the kernel of some
  refined quotient. This is the topological input used to pass from all finite quotients to
  prime-power or otherwise cofinal stages.
- `HasLeftQuotientKernelNeighbourhoodBasis.reindex_of_ker_le`
  Reindex a left-neighborhood quotient-kernel basis along a cofinal refinement of kernels. Every
  kernel in the original family is required to contain a kernel from the refined family.
- `HasIdentityQuotientKernelNeighbourhoodBasis.reindex_of_factor`
  A factorization of the refined quotient through an original quotient gives the required kernel
  inclusion for identity-neighborhood reindexing.
- `HasLeftQuotientKernelNeighbourhoodBasis.reindex_of_factor`
  A factorization of each refined quotient through an original quotient gives the kernel inclusion
  needed to reindex a left-neighborhood quotient-kernel basis.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology

universe u v w

section CofinalReindexing

variable {Y : Type u} [Group Y] [TopologicalSpace Y]
variable {J : Type v} {K : Type w}
variable {Q : J → Type*} [∀ j, Group (Q j)]
variable {Q' : K → Type*} [∀ k, Group (Q' k)]
variable (π : ∀ j : J, Y →* Q j)
variable (π' : ∀ k : K, Y →* Q' k)

/--
Reindex an identity-neighborhood quotient-kernel basis along a cofinal refinement of kernels.
The hypothesis says that every kernel in the original quotient family contains the kernel of
some refined quotient. This is the topological input used to pass from all finite quotients to
prime-power or otherwise cofinal stages.
-/
theorem HasIdentityQuotientKernelNeighbourhoodBasis.reindex_of_ker_le
    (hbasis : HasIdentityQuotientKernelNeighbourhoodBasis (Y := Y) π)
    (hcofinal : ∀ j : J, ∃ k : K, (π' k).ker ≤ (π j).ker) :
    HasIdentityQuotientKernelNeighbourhoodBasis (Y := Y) π' := by
  intro U hU hUone
  rcases hbasis U hU hUone with ⟨j, hj⟩
  rcases hcofinal j with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro z hz
  exact hj z (hk hz)

/--
Reindex a left-neighborhood quotient-kernel basis along a cofinal refinement of kernels. Every
kernel in the original family is required to contain a kernel from the refined family.
-/
theorem HasLeftQuotientKernelNeighbourhoodBasis.reindex_of_ker_le
    (hbasis : HasLeftQuotientKernelNeighbourhoodBasis (Y := Y) π)
    (hcofinal : ∀ j : J, ∃ k : K, (π' k).ker ≤ (π j).ker) :
    HasLeftQuotientKernelNeighbourhoodBasis (Y := Y) π' := by
  intro y U hU hyU
  rcases hbasis y U hU hyU with ⟨j, hj⟩
  rcases hcofinal j with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro z hz
  exact hj z (hk hz)

/--
A factorization of the refined quotient through an original quotient gives the required kernel
inclusion for identity-neighborhood reindexing.
-/
theorem HasIdentityQuotientKernelNeighbourhoodBasis.reindex_of_factor
    (hbasis : HasIdentityQuotientKernelNeighbourhoodBasis (Y := Y) π)
    (hrefine : ∀ j : J, ∃ k : K, ∃ τ : Q' k →* Q j, τ.comp (π' k) = π j) :
    HasIdentityQuotientKernelNeighbourhoodBasis (Y := Y) π' := by
  refine
    HasIdentityQuotientKernelNeighbourhoodBasis.reindex_of_ker_le
      (Y := Y) (π := π) (π' := π') hbasis ?_
  intro j
  rcases hrefine j with ⟨k, τ, hτ⟩
  refine ⟨k, ?_⟩
  intro z hz
  change π j z = 1
  have hz' : τ (π' k z) = 1 := by
    rw [hz]
    exact map_one τ
  simpa [← hτ, MonoidHom.comp_apply] using hz'

/--
A factorization of each refined quotient through an original quotient gives the kernel inclusion
needed to reindex a left-neighborhood quotient-kernel basis.
-/
theorem HasLeftQuotientKernelNeighbourhoodBasis.reindex_of_factor
    (hbasis : HasLeftQuotientKernelNeighbourhoodBasis (Y := Y) π)
    (hrefine : ∀ j : J, ∃ k : K, ∃ τ : Q' k →* Q j, τ.comp (π' k) = π j) :
    HasLeftQuotientKernelNeighbourhoodBasis (Y := Y) π' := by
  refine
    HasLeftQuotientKernelNeighbourhoodBasis.reindex_of_ker_le
      (Y := Y) (π := π) (π' := π') hbasis ?_
  intro j
  rcases hrefine j with ⟨k, τ, hτ⟩
  refine ⟨k, ?_⟩
  intro z hz
  change π j z = 1
  have hz' : τ (π' k z) = 1 := by
    rw [hz]
    exact map_one τ
  simpa [← hτ, MonoidHom.comp_apply] using hz'

/-- Closure approximation can be checked on any cofinal refinement of quotient kernels. -/
theorem subset_closure_of_identityQuotientKernel_approximation_reindex
    [IsTopologicalGroup Y]
    {S T : Set Y}
    (hbasis : HasIdentityQuotientKernelNeighbourhoodBasis (Y := Y) π)
    (hcofinal : ∀ j : J, ∃ k : K, (π' k).ker ≤ (π j).ker)
    (happrox :
      ∀ y : Y, y ∈ T → ∀ k : K,
        ∃ s : Y, s ∈ S ∧ π' k s = π' k y) :
    T ⊆ closure S :=
  subset_closure_of_identityQuotientKernel_approximation
    (Y := Y) (S := S) (T := T) π'
    (HasIdentityQuotientKernelNeighbourhoodBasis.reindex_of_ker_le
      (Y := Y) (π := π) (π' := π') hbasis hcofinal)
    happrox

/-- The finite-stage closure approximation can be checked on a cofinal refined quotient family. -/
theorem subset_closure_of_identityQuotientKernel_stage_exact_reindex
    [IsTopologicalGroup Y]
    {S T : Set Y}
    (hbasis : HasIdentityQuotientKernelNeighbourhoodBasis (Y := Y) π)
    (hcofinal : ∀ j : J, ∃ k : K, (π' k).ker ≤ (π j).ker)
    (Sstage Tstage : ∀ k : K, Set (Q' k))
    (hTstage : ∀ y : Y, y ∈ T → ∀ k : K, π' k y ∈ Tstage k)
    (hstage_exact : ∀ k : K, Tstage k ⊆ Sstage k)
    (hlift_stage : ∀ k : K, ∀ q : Q' k, q ∈ Sstage k →
      ∃ s : Y, s ∈ S ∧ π' k s = q) :
    T ⊆ closure S :=
  subset_closure_of_identityQuotientKernel_stage_exact
    (Y := Y) (S := S) (T := T) π'
    (HasIdentityQuotientKernelNeighbourhoodBasis.reindex_of_ker_le
      (Y := Y) (π := π) (π' := π') hbasis hcofinal)
    Sstage Tstage hTstage hstage_exact hlift_stage

end CofinalReindexing

end

end FoxDifferential
