/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_DoubleComplex.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Ring.RingNF

/-!
Double complexes, their two spectral-sequence pages and bounded convergence data.
-/

noncomputable section

universe u

namespace DoubleComplex

/-- A first-quadrant double complex with commuting differentials and a common finite bound. -/
structure Bounded (R : Type u) [CommRing R] where
  /-- The module carrier in horizontal degree `p` and vertical degree `q`. -/
  C : ℕ → ℕ → Type u
  /-- The additive commutative group structure on each component. -/
  [abGrp : ∀ p q, AddCommGroup (C p q)]
  /-- The coefficient-ring module structure on each component. -/
  [modR : ∀ p q, Module R (C p q)]
  /-- The differential raising horizontal degree by one. -/
  dH : ∀ p q, C p q →ₗ[R] C (p + 1) q
  /-- The differential raising vertical degree by one. -/
  dV : ∀ p q, C p q →ₗ[R] C p (q + 1)
  /-- Consecutive horizontal differentials compose to zero. -/
  dH_sq : ∀ p q, dH (p + 1) q ∘ₗ dH p q = 0
  /-- Consecutive vertical differentials compose to zero. -/
  dV_sq : ∀ p q, dV p (q + 1) ∘ₗ dV p q = 0
  /-- The horizontal and vertical differentials commute. -/
  dHV_comm : ∀ p q, dV (p + 1) q ∘ₗ dH p q = dH p (q + 1) ∘ₗ dV p q
  /-- The common upper bound for both component degrees. -/
  N : ℕ
  /-- Components with either degree at least `N` are subsingletons. -/
  hBound : ∀ p q, N ≤ p ∨ N ≤ q → Subsingleton (C p q)

attribute [instance] Bounded.abGrp Bounded.modR

section Tot

variable {R : Type u} [CommRing R] (D : Bounded R)

/-- The pairs of nonnegative bidegrees with total degree `n`. -/
abbrev Diag (n : ℕ) : Type := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

/-- The product of the components on the diagonal of total degree `n`. -/
abbrev Tot (n : ℕ) : Type u :=
  ∀ i : Diag n, D.C i.1.1 i.1.2

/-- The horizontal contribution to the total differential at the target bidegree. -/
def dTotH {n : ℕ} (i : Diag (n + 1)) :
    Tot D n →ₗ[R] D.C i.1.1 i.1.2 :=
  match i with
  | ⟨(0, _), _⟩ => 0
  | ⟨(p' + 1, q), h⟩ => (D.dH p' q).comp
      (LinearMap.proj (R := R)
        (φ := fun j : Diag n => D.C j.1.1 j.1.2) ⟨(p', q), by omega⟩)

/-- The vertical contribution to the total differential at the target bidegree. -/
def dTotV {n : ℕ} (i : Diag (n + 1)) :
    Tot D n →ₗ[R] D.C i.1.1 i.1.2 :=
  match i with
  | ⟨(_, 0), _⟩ => 0
  | ⟨(p, q' + 1), h⟩ => (D.dV p q').comp
      (LinearMap.proj (R := R)
        (φ := fun j : Diag n => D.C j.1.1 j.1.2) ⟨(p, q'), by omega⟩)

/-- The total differential, with vertical contribution signed by the horizontal degree. -/
def dTot (n : ℕ) :
    Tot D n →ₗ[R] Tot D (n + 1) :=
  LinearMap.pi fun i =>
    dTotH D i + ((-1 : ℤ) ^ i.1.1) • dTotV D i

/-- The total boundaries as a submodule of total cocycles, with no boundaries in degree zero. -/
def HTotB : (n : ℕ) → Submodule R (LinearMap.ker (dTot D n))
  | 0 => ⊥
  | n' + 1 => (LinearMap.range (dTot D n')).comap
      (LinearMap.ker (dTot D (n' + 1))).subtype

/-- The cohomology of the total complex in degree `n`. -/
abbrev HTot (n : ℕ) : Type u :=
  LinearMap.ker (dTot D n) ⧸ HTotB D n

end Tot

section DTotGeneric

variable {R : Type u} [CommRing R] {D : Bounded R}

theorem dTot_apply_zero_succ {n q' : ℕ} (h : 0 + (q' + 1) = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(0, q' + 1), h⟩ = D.dV 0 q' (c ⟨(0, q'), by omega⟩) := by
  simp only [dTot, LinearMap.pi_apply,
    dTotH, dTotV,
    LinearMap.comp_apply, LinearMap.proj_apply, pow_zero, one_smul, zero_add]

theorem dTot_apply_succ_zero {n p' : ℕ} (h : p' + 1 + 0 = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(p' + 1, 0), h⟩ = D.dH p' 0 (c ⟨(p', 0), by omega⟩) := by
  simp only [dTot, LinearMap.pi_apply,
    dTotH, dTotV,
    LinearMap.comp_apply, LinearMap.proj_apply, smul_zero, add_zero]

theorem dTot_apply_succ_succ {n p' q' : ℕ} (h : p' + 1 + (q' + 1) = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(p' + 1, q' + 1), h⟩
      = D.dH p' (q' + 1) (c ⟨(p', q' + 1), by omega⟩)
        + ((-1 : ℤ) ^ (p' + 1)) • D.dV (p' + 1) q' (c ⟨(p' + 1, q'), by omega⟩) := by
  rfl

theorem dTot_comp_dTot (D : Bounded R) (n : ℕ) :
    dTot D (n + 1) ∘ₗ dTot D n = 0 := by
  refine LinearMap.ext fun c => funext fun ⟨⟨pp, q⟩, h⟩ => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  match pp, q, h with
  | 0, 0, h => omega
  | 0, q' + 1, h =>
    obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
    rw [dTot_apply_zero_succ, dTot_apply_zero_succ,
      ← LinearMap.comp_apply, D.dV_sq, LinearMap.zero_apply]
  | p' + 1, 0, h =>
    obtain ⟨p'', rfl⟩ : ∃ p'', p' = p'' + 1 := ⟨p' - 1, by omega⟩
    rw [dTot_apply_succ_zero, dTot_apply_succ_zero,
      ← LinearMap.comp_apply, D.dH_sq, LinearMap.zero_apply]
  | p' + 1, q' + 1, h =>
    rw [dTot_apply_succ_succ]
    have hH : D.dH p' (q' + 1) (dTot D n c ⟨(p', q' + 1), by omega⟩)
        = ((-1 : ℤ) ^ p') • D.dH p' (q' + 1) (D.dV p' q' (c ⟨(p', q'), by omega⟩)) := by
      rcases p' with _ | p''
      · rw [dTot_apply_zero_succ, pow_zero, one_smul]
      · rw [dTot_apply_succ_succ, map_add, map_zsmul,
          ← LinearMap.comp_apply, D.dH_sq, LinearMap.zero_apply, zero_add]
    have hV : D.dV (p' + 1) q' (dTot D n c ⟨(p' + 1, q'), by omega⟩)
        = D.dV (p' + 1) q' (D.dH p' q' (c ⟨(p', q'), by omega⟩)) := by
      rcases q' with _ | q''
      · rw [dTot_apply_succ_zero]
      · rw [dTot_apply_succ_succ, map_add, map_zsmul,
          show D.dV (p' + 1) (q'' + 1) (D.dV (p' + 1) q'' (c ⟨(p' + 1, q''), by omega⟩)) = 0 from
            LinearMap.congr_fun (D.dV_sq (p' + 1) q'') _, smul_zero, add_zero]
    rw [hH, hV,
      show D.dV (p' + 1) q' (D.dH p' q' (c ⟨(p', q'), by omega⟩))
        = D.dH p' (q' + 1) (D.dV p' q' (c ⟨(p', q'), by omega⟩)) from
        LinearMap.congr_fun (D.dHV_comm p' q') _,
      ← add_smul, show ((-1:ℤ)^p' + (-1)^(p'+1)) = 0 from by ring, zero_smul]

end DTotGeneric

section E2

variable {R : Type u} [CommRing R] (D : Bounded R)

/-- The vertical boundaries as a submodule of vertical cocycles in column `p`. -/
def colB (p : ℕ) : (q : ℕ) → Submodule R (LinearMap.ker (D.dV p q))
  | 0 => ⊥
  | q' + 1 => (LinearMap.range (D.dV p q')).comap (LinearMap.ker (D.dV p (q' + 1))).subtype

/-- The vertical cohomology of column `p` in degree `q`. -/
abbrev colH (p q : ℕ) : Type u :=
  LinearMap.ker (D.dV p q) ⧸ colB D p q

/-- The map on vertical cohomology induced by the horizontal differential. -/
def colHdH (p q : ℕ) :
    colH D p q →ₗ[R] colH D (p + 1) q :=
  Submodule.mapQ _ _
    ((D.dH p q).restrict fun x hx => LinearMap.mem_ker.mpr <| by
      rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply,
        LinearMap.mem_ker.mp hx, map_zero])
    (by
      rcases q with _ | q'
      · simp only [colB]; exact bot_le
      · rintro x ⟨y, hy⟩
        exact ⟨D.dH p q' y, by
          change D.dV (p + 1) q' (D.dH p q' y) = D.dH p (q' + 1) x.1
          rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply, hy]; rfl⟩)

/-- The horizontal boundaries within the cocycles of the induced column-cohomology differential. -/
def E₂IB :
    (p q : ℕ) → Submodule R (LinearMap.ker (colHdH D p q))
  | 0, _ => ⊥
  | p' + 1, q => (LinearMap.range (colHdH D p' q)).comap
      (LinearMap.ker (colHdH D (p' + 1) q)).subtype

/-- The first second-page term, computed as horizontal cohomology of vertical cohomology. -/
abbrev E₂I (p q : ℕ) : Type u :=
  LinearMap.ker (colHdH D p q) ⧸ E₂IB D p q

/--
The bounded double complex obtained by exchanging the two component degrees and differentials.
-/
def transpose : Bounded R where
  C a b := D.C b a
  dH a b := D.dV b a
  dV a b := D.dH b a
  dH_sq a b := D.dV_sq b a
  dV_sq a b := D.dH_sq b a
  dHV_comm a b := (D.dHV_comm b a).symm
  N := D.N
  hBound a b h := D.hBound b a h.symm

/-- The second second-page term, computed from the transposed double complex. -/
abbrev E₂II (p q : ℕ) : Type u :=
  E₂I (transpose D) q p

instance (p q : ℕ) : AddCommGroup (E₂I D p q) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))
instance (p q : ℕ) : Module R (E₂I D p q) :=
  inferInstanceAs (Module R (_ ⧸ _))
instance (p q : ℕ) : AddCommGroup (E₂II D p q) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))
instance (p q : ℕ) : Module R (E₂II D p q) :=
  inferInstanceAs (Module R (_ ⧸ _))

end E2

/-- A pair of nested submodules presenting a subquotient of a module. -/
structure SubQuot (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] where
  /-- The submodule whose elements represent the subquotient. -/
  Z : Submodule R M
  /-- The submodule of elements identified with zero in the subquotient. -/
  B : Submodule R M
  /-- The denominator submodule is contained in the numerator submodule. -/
  hBZ : B ≤ Z

/-- The quotient of the numerator by the denominator pulled back along its inclusion. -/
abbrev SubQuot.carrier {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (s : SubQuot R M) : Type u := s.Z ⧸ s.B.comap s.Z.subtype

/-- Subquotient and filtration data relating a second page to the graded modules `H`. -/
structure Convergence (R : Type u) [CommRing R]
    (E₂ : ℕ → ℕ → Type u) [∀ p q, AddCommGroup (E₂ p q)] [∀ p q, Module R (E₂ p q)]
    (H : ℕ → Type u) [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] (N : ℕ) where
  /-- The limiting subquotient selected from each second-page term. -/
  Einf : ∀ p q, SubQuot R (E₂ p q)
  /-- Every element of a zeroth-row term belongs to the limiting numerator. -/
  hZ0 : ∀ p, (Einf p 0).Z = ⊤
  /-- The finite filtration of each zeroth-row term leading to its limiting denominator. -/
  Bfilt : ∀ p, Fin (N + 1) → Submodule R (E₂ p 0)
  /-- The denominator filtrations are increasing. -/
  Bfilt_mono : ∀ p, Monotone (Bfilt p)
  /-- Each denominator filtration starts at the zero submodule. -/
  Bfilt_bot : ∀ p, Bfilt p 0 = ⊥
  /-- Each denominator filtration ends at the limiting denominator. -/
  Bfilt_top : ∀ p, Bfilt p (Fin.last N) = (Einf p 0).B
  /-- Each successive denominator-filtration quotient is a subquotient of a positive-row term. -/
  Bfilt_gr : ∀ p (i : Fin N), ∃ p' q', 1 ≤ q' ∧ ∃ (s : SubQuot R (E₂ p' q')),
    Nonempty (((Bfilt p i.succ) ⧸ (Bfilt p i.castSucc).comap (Bfilt p i.succ).subtype)
      ≃ₗ[R] s.carrier)
  /-- The finite filtration on each module `H n`. -/
  Hfilt : ∀ n, Fin (N + 2) → Submodule R (H n)
  /-- The filtrations on `H` are increasing. -/
  Hfilt_mono : ∀ n, Monotone (Hfilt n)
  /-- Each filtration on `H` starts at the zero submodule. -/
  Hfilt_bot : ∀ n, Hfilt n 0 = ⊥
  /-- Each filtration on `H` ends at the whole module. -/
  Hfilt_top : ∀ n, Hfilt n (Fin.last (N + 1)) = ⊤
  /-- The designated quotient of the filtration on `H p` is the limiting zeroth-row subquotient. -/
  Hfilt_gr : ∀ (p : Fin (N + 1)),
    Nonempty (((Hfilt (↑p) p.succ) ⧸ (Hfilt (↑p) p.castSucc).comap (Hfilt (↑p) p.succ).subtype)
      ≃ₗ[R] (Einf p 0).carrier)

/-- The assertion that every bounded double complex admits the specified convergence data. -/
def BoundedSpectralSequence : Prop :=
  ∀ (R : Type u) [CommRing R] (D : Bounded R),
    Nonempty (Convergence R (E₂I D) (HTot D) D.N)

end DoubleComplex

end
