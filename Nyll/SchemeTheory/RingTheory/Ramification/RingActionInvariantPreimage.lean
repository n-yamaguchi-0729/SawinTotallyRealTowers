/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.ProfiniteRingActionRestriction
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Actual inertia-fixed preimages in a ring-action restriction

An injective equivariant ring map and the proved full inertia image give
the equality between the actual upper-fixed preimage and the actual lower
fixed ring. The proof stays in the existing ring-action restriction owner;
no field, coefficient algebra, or localization is introduced.
-/

noncomputable section

namespace SchemeTheory.RingActionRestriction

universe u v w x

/-- The actual upper inertia-fixed subring for the prescribed action. -/
def upperInertiaFixedSubring (D : RingActionRestriction.{u, v, w, x})
    (q : Ideal D.upperRing.carrier) : Subring D.upperRing.carrier :=
  let : MulSemiringAction D.upperGroup.carrier D.upperRing.carrier := D.upperAction
  FixedPoints.subring D.upperRing.carrier (D.upperInertia q)

/-- The actual lower inertia-fixed subring for the prescribed action. -/
def lowerInertiaFixedSubring (D : RingActionRestriction.{u, v, w, x})
    (p : Ideal D.lowerRing.carrier) : Subring D.lowerRing.carrier :=
  let : MulSemiringAction D.lowerGroup.carrier D.lowerRing.carrier := D.lowerAction
  FixedPoints.subring D.lowerRing.carrier (D.lowerInertia p)

/-- The literal preimage of upper inertia invariants under the given ring map. -/
def inertiaFixedPreimageSubring (D : RingActionRestriction.{u, v, w, x})
    (q : Ideal D.upperRing.carrier) : Subring D.lowerRing.carrier :=
  (D.upperInertiaFixedSubring q).comap D.ringMap

/-- The existing equivariant square and the full inertia image prove the
actual fixed-ring comparison. No comparison is part of the data owner. -/
theorem inertiaFixedPreimageSubring_eq (D : RingActionRestriction.{u, v, w, x})
    (p : Ideal D.lowerRing.carrier) (q : Ideal D.upperRing.carrier)
    (hinj : Function.Injective D.ringMap.toFun) (hequiv : D.IsEquivariant)
    (himage : (D.upperInertia q).map D.groupMap = D.lowerInertia p) :
    D.inertiaFixedPreimageSubring q = D.lowerInertiaFixedSubring p := by
  let : MulSemiringAction D.upperGroup.carrier D.upperRing.carrier := D.upperAction
  let : MulSemiringAction D.lowerGroup.carrier D.lowerRing.carrier := D.lowerAction
  ext a
  change
    (∀ g : {g : D.upperGroup.carrier // (D.upperInertia q).carrier g},
      g.val • D.ringMap.toFun a = D.ringMap.toFun a) ↔
    ∀ g : {g : D.lowerGroup.carrier // (D.lowerInertia p).carrier g}, g.val • a = a
  constructor
  · intro ha τ
    have hτ : ((D.upperInertia q).map D.groupMap).carrier τ.val := by
      rw [himage]
      exact τ.property
    obtain ⟨σ, hσ, hστ⟩ := hτ
    apply hinj
    have hcoeff := congrArg
      (fun f : D.lowerRing.carrier →+* D.upperRing.carrier => f.toFun a)
      (hequiv σ)
    change D.ringMap.toFun (D.groupMap.toFun σ • a) =
      σ • D.ringMap.toFun a at hcoeff
    rw [← hστ]
    exact hcoeff.trans (ha ⟨σ, hσ⟩)
  · intro ha σ
    have hσ : (D.lowerInertia p).carrier (D.groupMap.toFun σ.val) := by
      rw [← himage]
      exact ⟨σ.val, σ.property, rfl⟩
    have hfixed := ha ⟨D.groupMap.toFun σ.val, hσ⟩
    have hcoeff := congrArg
      (fun f : D.lowerRing.carrier →+* D.upperRing.carrier => f.toFun a)
      (hequiv σ.val)
    exact hcoeff.symm.trans (congrArg D.ringMap.toFun hfixed)

/-- The native upper inertia-fixed ring object. -/
def upperInertiaFixedRing (D : RingActionRestriction.{u, v, w, x})
    (q : Ideal D.upperRing.carrier) : CommRingCat.{v} :=
  CommRingCat.of (D.upperInertiaFixedSubring q)

/-- The native lower inertia-fixed ring object. -/
def lowerInertiaFixedRing (D : RingActionRestriction.{u, v, w, x})
    (p : Ideal D.lowerRing.carrier) : CommRingCat.{u} :=
  CommRingCat.of (D.lowerInertiaFixedSubring p)

/-- The native actual preimage ring object. -/
def inertiaFixedPreimageRing (D : RingActionRestriction.{u, v, w, x})
    (q : Ideal D.upperRing.carrier) : CommRingCat.{u} :=
  CommRingCat.of (D.inertiaFixedPreimageSubring q)

/-- The literal preimage inclusion into the upper fixed ring. -/
def inertiaFixedPreimageInclusion (D : RingActionRestriction.{u, v, w, x})
    (q : Ideal D.upperRing.carrier) :
    (D.inertiaFixedPreimageRing q).carrier →+* (D.upperInertiaFixedRing q).carrier :=
  D.ringMap.restrict (D.inertiaFixedPreimageSubring q) (D.upperInertiaFixedSubring q)
    (fun _ hb => hb)

/-- The preimage inclusion retains the actual original coefficient map. -/
theorem inertiaFixedPreimageInclusion_comp_subtype
    (D : RingActionRestriction.{u, v, w, x}) (q : Ideal D.upperRing.carrier) :
    (D.upperInertiaFixedSubring q).subtype.comp (D.inertiaFixedPreimageInclusion q) =
      D.ringMap.comp (D.inertiaFixedPreimageSubring q).subtype :=
  RingHom.comp_restrict D.ringMap (D.inertiaFixedPreimageSubring q)
    (D.upperInertiaFixedSubring q) (fun _ hb => hb)

/-- The proved actual comparison, with no new coefficient action. -/
def inertiaFixedPreimageEquiv (D : RingActionRestriction.{u, v, w, x})
    (p : Ideal D.lowerRing.carrier) (q : Ideal D.upperRing.carrier)
    (hinj : Function.Injective D.ringMap.toFun) (hequiv : D.IsEquivariant)
    (himage : (D.upperInertia q).map D.groupMap = D.lowerInertia p) :
    (D.inertiaFixedPreimageRing q).carrier ≃+* (D.lowerInertiaFixedRing p).carrier :=
  RingEquiv.subringCongr (D.inertiaFixedPreimageSubring_eq p q hinj hequiv himage)

/-- The comparison is exactly the identity on lower normalization elements. -/
theorem inertiaFixedPreimageEquiv_comp_subtype
    (D : RingActionRestriction.{u, v, w, x})
    (p : Ideal D.lowerRing.carrier) (q : Ideal D.upperRing.carrier)
    (hinj : Function.Injective D.ringMap.toFun) (hequiv : D.IsEquivariant)
    (himage : (D.upperInertia q).map D.groupMap = D.lowerInertia p) :
    (D.lowerInertiaFixedSubring p).subtype.comp
        (D.inertiaFixedPreimageEquiv p q hinj hequiv himage).toRingHom =
      (D.inertiaFixedPreimageSubring q).subtype := by
  apply RingHom.ext
  intro a
  exact RingEquiv.coe_subringCongr_apply
    (D.inertiaFixedPreimageSubring_eq p q hinj hequiv himage) a

end SchemeTheory.RingActionRestriction
