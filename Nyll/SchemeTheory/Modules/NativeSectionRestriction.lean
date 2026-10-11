/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic

/-!
# Native section restriction maps

Uses the existing section rings and modules to represent their actual restriction maps.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules.NativeSections

/-- The actual ring of sections at an open. -/
def sectionRing (X : Scheme.{u}) (U : X.Opens) : CommRingCat.{u} := Γ(X, U)

/-- The actual module object, with its existing section-ring action. -/
def sectionModule {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    ModuleCat.{u} (sectionRing X U) :=
  M.val.obj (op U)

/-- The actual abelian section-group object. -/
def sectionGroup {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) : AddCommGrpCat.{u} :=
  M.presheaf.obj (op U)

/-- The actual section-ring restriction homomorphism. -/
def ringRestriction {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) :
    sectionRing X U →+* sectionRing X V :=
  (X.presheaf.map (homOfLE h).op).hom

/-- The actual local module viewed through the prescribed section restriction. -/
def restrictedModule {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    ModuleCat.{u} (sectionRing X U) :=
  (ModuleCat.restrictScalars (ringRestriction h)).obj (sectionModule M V)

/-- The native presheaf restriction morphism, without projecting its carrier. -/
def restriction {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    sectionModule M U ⟶ restrictedModule M h :=
  M.val.map (homOfLE h).op

/-- The function underlying that same native restriction. -/
def restrictionFn {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    sectionGroup M U → sectionGroup M V :=
  fun x => (restriction M h).hom (show sectionModule M U from x)

/-- The existing source action, exposed only as its actual power function. -/
def sourcePowFn {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (f : sectionRing X U) (n : ℕ) : sectionGroup M U → sectionGroup M U :=
  fun x => f ^ n • (show sectionModule M U from x)

/-- The existing restricted action, exposed only as its actual power function. -/
def restrictedPowFn {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (f : sectionRing X U) (n : ℕ) : sectionGroup M V → sectionGroup M V :=
  fun x => f ^ n • (show restrictedModule M h from x)

/-- Literal computation against the original abelian restriction map. -/
theorem restrictionFn_apply {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (x : Γ(M, U)) :
    restrictionFn M h x = M.presheaf.map (homOfLE h).op x := rfl

/-- Literal computation against the original source action. -/
theorem sourcePowFn_apply {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (f : Γ(X, U)) (n : ℕ) (x : Γ(M, U)) :
    sourcePowFn M U f n x = f ^ n • x := rfl

/-- Literal computation of the prescribed restriction-of-scalars action. -/
theorem restrictedPowFn_apply {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (f : Γ(X, U)) (n : ℕ) (x : Γ(M, V)) :
    restrictedPowFn M h f n x = X.presheaf.map (homOfLE h).op (f ^ n) • x := rfl

end AlgebraicGeometry.Scheme.Modules.NativeSections
