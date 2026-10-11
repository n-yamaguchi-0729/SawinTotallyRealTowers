/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale

/-!
# Horizontal boundary components after finite etale pullback

Every irreducible component of the pullback of a horizontal boundary maps
onto an irreducible component downstairs.  Consequently its composite with
the structural morphism has dense range.  The statement is made directly
for the pulled-back ideal sheaf, before packaging it as an effective Cartier
divisor.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme.EffectiveCartierDivisor

variable {X Y S : Scheme.{u}}

/-- Horizontal irreducible components remain horizontal after finite etale
pullback. -/
theorem comap_components_denseRange_of_isHorizontalOver
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (f : Y ⟶ X) [IsFiniteEtale f] (hD : D.IsHorizontalOver p) :
    ∀ (Z : Set (D.1.comap f).subscheme)
      (hZ : Z ∈ irreducibleComponents (D.1.comap f).subscheme),
      DenseRange ((D.1.comap f).componentToBase (f ≫ p) Z hZ) := by
  intro Z hZ
  obtain ⟨W, hW, himage⟩ :=
    D.1.exists_irreducibleComponent_image_comapSubschemeTo_eq f Z hZ
  apply Dense.mono (s₁ := Set.range (D.1.componentToBase p W hW))
  · rintro _ ⟨w, rfl⟩
    have hwW : w.1 ∈ W := by
      have hwSupport := w.2
      change w.1 ∈ (IdealSheafData.vanishingIdeal
        ⟨W, isClosed_of_mem_irreducibleComponents W hW⟩).support at hwSupport
      change w.1 ∈ W at hwSupport
      exact hwSupport
    have hwImage : w.1 ∈ D.1.comapSubschemeTo f '' Z := by
      rw [himage]
      exact hwW
    obtain ⟨y, hyZ, hgy⟩ := hwImage
    let z : (D.1.comap f).subscheme.reducedIrreducibleComponent Z hZ :=
      ⟨y, by
        change y ∈ (IdealSheafData.vanishingIdeal
          ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).support
        change y ∈ Z
        exact hyZ⟩
    refine ⟨z, ?_⟩
    change p (f ((D.1.comap f).subschemeι y)) = p (D.1.subschemeι w.1)
    have hpoint : f ((D.1.comap f).subschemeι y) = D.1.subschemeι w.1 := by
      rw [← Scheme.Hom.comp_apply,
        ← D.1.comapSubschemeTo_subschemeι]
      simpa only [Scheme.Hom.comp_apply] using
        congrArg D.1.subschemeι hgy
    rw [hpoint]
  · exact hD W hW

end Scheme.EffectiveCartierDivisor

end AlgebraicGeometry

end
