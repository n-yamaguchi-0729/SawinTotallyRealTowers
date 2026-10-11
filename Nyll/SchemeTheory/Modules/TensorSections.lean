/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesSectionsTensor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.Frames
import Nyll.SchemeTheory.Modules.PresheafInternalHom
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.TensorPowers

/-!
# Tensor products and frames of module sections

Local tensor sections and their iterated powers are compatible with restrictions and
module operations; frames characterize sections freely generating smaller opens.
-/

universe u

open CategoryTheory MonoidalCategory Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

local instance tensorSectionsPresheafModule (P : X.PresheafOfModules) (U : X.Opens) :
    Module Γ(X, U) (P.obj (op U)) := (P.obj (op U)).isModule

section Hom

variable (L M : X.Modules)

/-- The canonical map from the tensor product of underlying presheaves to the sheaf tensor product.
-/
def tensorSectionsHom : L.val ⊗ M.val ⟶
    (SheafOfModules.toPMod (J := _root_.Opens.grothendieckTopology X)
      X.sheaf.obj X.ringCatSheaf.property : X.Modules ⥤ X.PresheafOfModules).obj (show X.Modules
          from L ⊗ M) :=
  (SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (L.val ⊗ M.val) ≫
    (SheafOfModules.toPMod (J := _root_.Opens.grothendieckTopology X)
      X.sheaf.obj X.ringCatSheaf.property : X.Modules ⥤ X.PresheafOfModules).map (tensorIsoSheafify
          L M).hom

end Hom

section Sections

variable {L M : X.Modules} {U : X.Opens}

/-- The tensor product of two module sections over the same open subset. -/
def tensorSections (s : Γ(L, U)) (t : Γ(M, U)) : Γ(L ⊗ M, U) :=
  DFunLike.coe (α := ((L.val ⊗ M.val).obj (op U) :)) (β := fun _ => Γ(L ⊗ M, U))
    ((tensorSectionsHom L M).app (op U)).hom
    ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))

lemma tensorSections_def (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections s t = DFunLike.coe (α := ((L.val ⊗ M.val).obj (op U) :)) (β := fun _ => Γ(L ⊗ M,
        U))
      ((tensorSectionsHom L M).app (op U)).hom
      ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))) := rfl

lemma tensorSections_add_left (s s' : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (s + s') t = tensorSections s t + tensorSections s' t := by
  rw [tensorSections_def, tensorSections_def, tensorSections_def]
  erw [TensorProduct.add_tmul, map_add]
  rfl

lemma tensorSections_add_right (s : Γ(L, U)) (t t' : Γ(M, U)) :
    tensorSections s (t + t') = tensorSections s t + tensorSections s t' := by
  rw [tensorSections_def, tensorSections_def, tensorSections_def]
  erw [TensorProduct.tmul_add, map_add]
  rfl

lemma tensorSections_smul_left (g : Γ(X, U)) (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (g • s) t = g • tensorSections s t := by
  rw [tensorSections_def, tensorSections_def]
  let : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
  erw [← TensorProduct.smul_tmul', LinearMap.map_smul]
  rfl

lemma tensorSections_smul_right (g : Γ(X, U)) (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections s (g • t) = g • tensorSections s t := by
  rw [tensorSections_def, tensorSections_def]
  let : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
  erw [TensorProduct.tmul_smul, LinearMap.map_smul]
  rfl

@[simp] lemma tensorSections_zero_left (t : Γ(M, U)) : tensorSections (0 : Γ(L, U)) t = 0 := by
  rw [tensorSections_def]
  erw [TensorProduct.zero_tmul, map_zero]
  rfl

@[simp] lemma tensorSections_zero_right (s : Γ(L, U)) : tensorSections s (0 : Γ(M, U)) = 0 := by
  rw [tensorSections_def]
  erw [TensorProduct.tmul_zero, map_zero]
  rfl

lemma tensorSections_neg_left (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (-s) t = -tensorSections s t := by
  rw [eq_neg_iff_add_eq_zero, ← tensorSections_add_left, neg_add_cancel, tensorSections_zero_left]

lemma tensorSections_neg_right (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections s (-t) = -tensorSections s t := by
  rw [eq_neg_iff_add_eq_zero, ← tensorSections_add_right, neg_add_cancel, tensorSections_zero_right]

lemma tensorSections_sum_left {ι : Type*} (S : Finset ι) (s : ι → Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (∑ i ∈ S, s i) t = ∑ i ∈ S, tensorSections (s i) t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, tensorSections_add_left, ih]

lemma tensorSections_sum_right {ι : Type*} (S : Finset ι) (s : Γ(L, U)) (t : ι → Γ(M, U)) :
    tensorSections s (∑ i ∈ S, t i) = ∑ i ∈ S, tensorSections s (t i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, tensorSections_add_right,
      ih]

variable (L M U) in
/-- The bilinear map on local sections induced by the sheaf tensor product. -/
def tensorSectionsBilin : Γ(L, U) →ₗ[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U) :=
  LinearMap.mk₂ Γ(X, U) tensorSections tensorSections_add_left tensorSections_smul_left
    tensorSections_add_right tensorSections_smul_right

@[simp] lemma tensorSectionsBilin_apply (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSectionsBilin L M U s t = tensorSections s t := rfl

lemma map_tensorSections {V : X.Opens} (i : V ⟶ U) (s : Γ(L, U)) (t : Γ(M, U)) :
    (L ⊗ M).presheaf.map i.op (tensorSections s t) =
      tensorSections (L.presheaf.map i.op s) (M.presheaf.map i.op t) := by
  rw [tensorSections_def, tensorSections_def]
  have h := PresheafOfModules.naturality_apply (tensorSectionsHom L M) i.op
    ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))
  erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul] at h
  exact h.symm

lemma map_homOfLE_tensorSections {V : X.Opens} (h : V ≤ U) (s : Γ(L, U)) (t : Γ(M, U)) :
    (L ⊗ M).presheaf.map (homOfLE h).op (tensorSections s t) =
      tensorSections (L.presheaf.map (homOfLE h).op s) (M.presheaf.map (homOfLE h).op t) :=
  map_tensorSections (homOfLE h) s t

end Sections

section Pow

variable {L : X.Modules} {U : X.Opens}

variable (U) in
/-- The section of the unit module represented by the constant function one. -/
def unitSection : Γ(𝟙_ X.Modules, U) := (1 : Γ(X, U))

lemma unitSection_def : (unitSection U : Γ(𝟙_ X.Modules, U)) = (1 : Γ(X, U)) := rfl

@[simp] lemma map_unitSection {V : X.Opens} (i : V ⟶ U) :
    (𝟙_ X.Modules).presheaf.map i.op (unitSection U) = unitSection V :=
  (X.presheaf.map i.op).hom.map_one

lemma smul_unitSection (g : Γ(X, U)) : g • unitSection U = (g : Γ(X, U)) :=
  mul_one g

lemma smul_unitSection_bijective : Function.Bijective fun g : Γ(X, U) => g • unitSection U := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun x => (x : Γ(X, U)), fun g => ?_, fun x => ?_⟩
  · exact mul_one g
  · exact mul_one (show Γ(X, U) from x)

/-- The iterated tensor power of a section, with the unit section in degree zero. -/
def tensorPowSection (s : Γ(L, U)) : (n : ℕ) → Γ(L.tensorPow n, U)
  | 0 => unitSection U
  | n + 1 => tensorSections (L := L.tensorPow n) (M := L) (tensorPowSection s n) s

@[simp] lemma tensorPowSection_zero (s : Γ(L, U)) : tensorPowSection s 0 = unitSection U := rfl

lemma tensorPowSection_succ (s : Γ(L, U)) (n : ℕ) :
    tensorPowSection s (n + 1) = tensorSections (L := L.tensorPow n) (M := L) (tensorPowSection s n)
        s := rfl

lemma tensorPowSection_one (s : Γ(L, U)) :
    tensorPowSection s 1 = tensorSections (L := 𝟙_ X.Modules) (M := L) (unitSection U) s := rfl

lemma map_tensorPowSection {V : X.Opens} (i : V ⟶ U) (s : Γ(L, U)) (n : ℕ) :
    (L.tensorPow n).presheaf.map i.op (tensorPowSection s n) =
      tensorPowSection (L.presheaf.map i.op s) n := by
  induction n with
  | zero => exact map_unitSection i
  | succ n ih =>
    rw [tensorPowSection_succ, tensorPowSection_succ, ← ih]
    exact map_tensorSections (L := L.tensorPow n) (M := L) i _ s

end Pow

section Frame

variable {M : X.Modules} {U : X.Opens}

lemma isFrameOn_unitSection (V : X.Opens) : IsFrameOn (unitSection U) V := by
  intro W hWU _
  have e : (𝟙_ X.Modules).presheaf.map (homOfLE hWU).op (unitSection U) = unitSection W :=
    map_unitSection _
  simp only [e]
  exact smul_unitSection_bijective

end Frame

end AlgebraicGeometry.Scheme.Modules

end
