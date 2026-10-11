/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Transporting the Henselian property along a ring equivalence

Coefficient pullback and the induced quotient equivalence transport simple
roots. The Jacobson-radical condition transports along the same ring map.
-/

namespace ValuationTheory.Henselian

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Ring equivalences transport a Henselian pair to the image ideal. -/
theorem henselianRing_map_of_ringEquiv
    (e : R ≃+* S) (I : Ideal R) [HenselianRing R I] :
    HenselianRing S (I.map (e : R →+* S)) where
  jac := by
    have hmap := Ideal.map_mono (f := (e : R →+* S))
      (show I ≤ Ideal.jacobson (⊥ : Ideal R) from HenselianRing.jac)
    rw [Ideal.map_jacobson_of_bijective e.bijective, Ideal.map_bot] at hmap
    exact hmap
  is_henselian := by
    intro f hf a₀ hroot hsimple
    have heval (p : Polynomial S) (x : S) :
        (p.map (e.symm : S →+* R)).eval (e.symm x) = e.symm (p.eval x) :=
      Polynomial.eval_map_apply (f := (e.symm : S →+* R)) (p := p) x
    have hrootR : (f.map (e.symm : S →+* R)).eval (e.symm a₀) ∈ I := by
      rw [heval]
      exact Ideal.symm_apply_mem_of_equiv_iff.mpr hroot
    have hsimpleR : IsUnit (Ideal.Quotient.mk I
        ((f.map (e.symm : S →+* R)).derivative.eval (e.symm a₀))) := by
      rw [Polynomial.derivative_map, heval]
      exact hsimple.map
        (Ideal.quotientEquiv I (I.map (e : R →+* S)) e rfl).symm.toRingHom
    obtain ⟨a, ha, hamem⟩ := HenselianRing.is_henselian
      (f.map (e.symm : S →+* R)) (hf.map (e.symm : S →+* R))
      (e.symm a₀) hrootR hsimpleR
    refine ⟨e a, ?_, ?_⟩
    · change f.eval (e a) = 0
      apply e.symm.injective
      rw [map_zero, ← heval, e.symm_apply_apply]
      exact ha
    · have hmem : e (a - e.symm a₀) ∈ I.map (e : R →+* S) :=
        Ideal.mem_map_of_mem (e : R →+* S) hamem
      rwa [map_sub, e.apply_symm_apply] at hmem

/-- A ring equivalence transports the Henselian property at the maximal
ideal between local rings. Locality of the target can be supplied by `e.isLocalRing`. -/
theorem henselianRing_maximalIdeal_of_ringEquiv
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S)
    [HenselianRing R (IsLocalRing.maximalIdeal R)] :
    HenselianRing S (IsLocalRing.maximalIdeal S) := by
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
  exact henselianRing_map_of_ringEquiv e (IsLocalRing.maximalIdeal R)

end ValuationTheory.Henselian
