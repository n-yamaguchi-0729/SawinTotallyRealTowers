/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Algebra.HenselianEtaleSection
import Nyll.SchemeTheory.FiniteEtale.Algebra.JacobsonRigidity
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Basic


/-!
# Lifting pointed étale maps into a Henselian target

An étale algebra over A need not be an algebra over the target S. Base change
to S and the native `AlgHom.liftEquiv` reduce existence to the existing
Henselian section theorem. The existing Jacobson rigidity theorem supplies
uniqueness over A directly. No module-finiteness or comparison map is assumed.

This is the affine pointed-lifting supplier for maps from the constructed
geometric stalk into an actual strictly henselian local target.
-/

noncomputable section

open scoped TensorProduct

namespace Algebra.Etale

universe u v

/-- Reduction modulo a Henselian ideal in the target gives a bijection on
maps out of every étale A-algebra. The source and target rings share the
ambient universe used by the native Henselian section theorem; the base
algebra A may have an independent universe. -/
theorem bijective_comp_quotient_of_henselian_target
    {A : Type u} {B S : Type v}
    [CommRing A] [CommRing B] [CommRing S] [Algebra A B] [Algebra A S]
    [Algebra.Etale A B] (I : Ideal S) [HenselianRing S I] :
    Function.Bijective
      ((Ideal.Quotient.mkₐ A I).comp : (B →ₐ[A] S) → B →ₐ[A] S ⧸ I) := by
  refine ⟨Algebra.FormallyUnramified.comp_injective_of_le_jacobson
    (R := A) (A := B) (B := S) I (HenselianRing.jac (R := S) (I := I)), ?_⟩
  intro q
  let T := S ⊗[A] B
  have : Algebra.Etale S T := inferInstance
  let q' : T →ₐ[S] S ⧸ I := (AlgHom.liftEquiv A S B (S ⧸ I)) q
  obtain ⟨g, hg⟩ :=
    (bijective_comp_quotient_of_henselian (R := S) (B := T) I).surjective q'
  refine ⟨(AlgHom.liftEquiv A S B S).symm g, ?_⟩
  apply AlgHom.ext
  intro b
  have hpoint := AlgHom.congr_fun hg ((1 : S) ⊗ₜ[A] b)
  change Ideal.Quotient.mk I (g ((1 : S) ⊗ₜ[A] b)) = q' ((1 : S) ⊗ₜ[A] b) at hpoint
  change Ideal.Quotient.mk I ((AlgHom.liftEquiv A S B S).symm g b) = q b
  rw [AlgHom.liftEquiv_symm_apply]
  refine hpoint.trans ?_
  change (AlgHom.liftEquiv A S B (S ⧸ I) q) ((1 : S) ⊗ₜ[A] b) = q b
  rw [AlgHom.liftEquiv_tmul, one_smul]

end Algebra.Etale
