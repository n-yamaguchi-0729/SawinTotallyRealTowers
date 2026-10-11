/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverOf.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom

/-!
# Ordered affine covers of an open subset

An ordered affine cover of an open has increasing-index Cech cochains, alternating
restriction differentials, and an augmentation from sections of the structure sheaf.
-/

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

/-- A finite linearly ordered family of affine opens covering the specified open subset. -/
structure Scheme.OrderedAffineCoverOf {V : Scheme.{u}} (W : V.Opens) where
  /-- The index type of the affine opens in the cover. -/
  ι : Type u
  /-- A finite enumeration of the cover indices. -/
  [instFintype : Fintype ι]
  /-- The linear order used to form increasing Cech indices. -/
  [instLinearOrder : LinearOrder ι]
  /-- The affine open associated with each cover index. -/
  U : ι → V.Opens
  /-- Each member of the cover is an affine open. -/
  isAffineOpen : ∀ i, IsAffineOpen (U i)
  /-- Each member of the cover lies in the specified open subset. -/
  le : ∀ i, U i ≤ W
  /-- The supremum of the cover members is the specified open subset. -/
  iSup_eq : ⨆ i, U i = W

attribute [instance]
  Scheme.OrderedAffineCoverOf.instFintype
  Scheme.OrderedAffineCoverOf.instLinearOrder

namespace Scheme.OrderedAffineCoverOf

variable {W : V.Opens} (K : V.OrderedAffineCoverOf W)

/-- Strictly increasing tuples of cover indices for intersections in the given Cech degree. -/
def Idx (i : ℕ) : Type u := {s : Fin (i + 1) → K.ι // StrictMono s}

instance (i : ℕ) : Fintype (K.Idx i) := Subtype.fintype _
instance (i : ℕ) : DecidableEq (K.Idx i) := Classical.decEq _

/-- The intersection of the cover members selected by an increasing tuple. -/
def inter {i : ℕ} (s : K.Idx i) : V.Opens := ⨅ j, K.U (s.1 j)

/-- The increasing tuple obtained by deleting the specified index. -/
def face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) : K.Idx i :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

theorem inter_le_inter_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    K.inter s ≤ K.inter (K.face s j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

theorem inter_le {i : ℕ} (s : K.Idx i) (j : Fin (i + 1)) : K.inter s ≤ K.U (s.1 j) := iInf_le _ j

theorem inter_le_base {i : ℕ} (s : K.Idx i) : K.inter s ≤ W := (iInf_le _ 0).trans (K.le _)

end Scheme.OrderedAffineCoverOf

namespace Scheme.OrderedAffineCover

/-- Regard an ordered affine cover of the scheme as a cover of its top open. -/
def toCoverOf (K : V.OrderedAffineCover) : V.OrderedAffineCoverOf ⊤ where
  ι := K.ι
  U := K.U
  isAffineOpen := K.isAffineOpen
  le _ := le_top
  iSup_eq := K.iSup_eq_top

@[simp] theorem toCoverOf_U (K : V.OrderedAffineCover) (i : K.ι) : K.toCoverOf.U i = K.U i := rfl

/-- Intersect an ordered affine cover with an affine open in a separated scheme over the base. -/
def restrict (π : V ⟶ Spec (.of R)) [IsSeparated π] (K : V.OrderedAffineCover) {W : V.Opens}
    (hW : IsAffineOpen W) : V.OrderedAffineCoverOf W where
  ι := K.ι
  U i := K.U i ⊓ W
  isAffineOpen i := isAffineOpen_inf_of_isSeparated π (K.isAffineOpen i) hW
  le _ := inf_le_right
  iSup_eq := by rw [← iSup_inf_eq, K.iSup_eq_top, top_inf_eq]

@[simp] theorem restrict_U (π : V ⟶ Spec (.of R)) [IsSeparated π] (K : V.OrderedAffineCover) {W
    : V.Opens}
    (hW : IsAffineOpen W) (i : K.ι) : (K.restrict π hW).U i = K.U i ⊓ W := rfl

end Scheme.OrderedAffineCover

namespace Scheme.OrderedAffineCoverOf

variable (π : V ⟶ Spec (.of R)) {W : V.Opens} (K : V.OrderedAffineCoverOf W)

/-- The base-ring module structure on sections supplied by the structural morphism. -/
@[reducible] def moduleSections : ∀ O : V.Opens, Module R Γ(V, O) :=
  fun O => (Scheme.TwoAffineOpenCover.algebraOfHom π O).toModule

/-- Cech cochains of the structure sheaf on the selected intersections of the cover. -/
abbrev cochain (i : ℕ) : Type u := ∀ s : K.Idx i, Γ(V, K.inter s)

/-- The base-linear restriction map on structure-sheaf sections. -/
def res {O O' : V.Opens} (h : O ≤ O') :
    letI := moduleSections π
    (Γ(V, O') : Type u) →ₗ[R] (Γ(V, O) : Type u) :=
  (OModulePresheaf.unit π).res h

theorem res_apply {O O' : V.Opens} (h : O ≤ O') (x : Γ(V, O')) :
    res π h x = (V.presheaf.map (homOfLE h).op).hom x := rfl

/-- The alternating sum of face restriction maps defining the Cech differential. -/
def d (i : ℕ) :
    letI := moduleSections π
    K.cochain i →ₗ[R] K.cochain (i + 1) :=
  letI := moduleSections π
  LinearMap.pi fun s => ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((res π (K.inter_le_inter_face s j)).comp (LinearMap.proj (K.face s j)))

theorem d_apply (i : ℕ) (f : K.cochain i) (s : K.Idx (i + 1)) :
    letI := moduleSections π
    K.d π i f s = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (V.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom (f (K.face s j)) := by
  simp only [d, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, res_apply]

/-- The augmentation sending a section on the covered open to its restrictions on the cover. -/
def aug :
    letI := moduleSections π
    (Γ(V, W) : Type u) →ₗ[R] K.cochain 0 :=
  letI := moduleSections π
  LinearMap.pi fun s => res π (K.inter_le_base s)

theorem aug_apply (w : Γ(V, W)) (s : K.Idx 0) :
    letI := moduleSections π
    K.aug π w s = (V.presheaf.map (homOfLE (K.inter_le_base s)).op).hom w := rfl

/-- The degree-zero Cech cohomology, represented by the kernel of the first differential. -/
abbrev H0 : Type u :=
  letI := moduleSections π
  LinearMap.ker (K.d π 0)

/-- Positive Cech cohomology as cocycles modulo the image of the preceding differential. -/
abbrev HSucc (i : ℕ) : Type u :=
  letI := moduleSections π
  LinearMap.ker (K.d π (i + 1)) ⧸ (LinearMap.range (K.d π i)).comap (LinearMap.ker (K.d π (i +
      1))).subtype

end Scheme.OrderedAffineCoverOf

theorem Scheme.OrderedAffineCover.d_toCoverOf (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover)
    (i : ℕ) :
    K.toCoverOf.d π i = (OModulePresheaf.unit π).d K i := rfl

end AlgebraicGeometry

end
