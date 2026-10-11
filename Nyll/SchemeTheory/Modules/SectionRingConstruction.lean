/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from the proof and definitions at pinned revision
aa2d8b34692b16c70f699536de0d8e75b9a3e9ef:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing.lean
Upstream NOTICE and per-file ATTRIBUTION (including earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
See SchemeTheory/ANTHROPIC_FLT_SOURCE.md for retained notices.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.SectionRing
import Nyll.SchemeTheory.Modules.FrameFromTrivialization
import Nyll.SchemeTheory.Modules.TensorPowerFrames
import Nyll.SchemeTheory.Modules.TensorPowerSectionProduct
import Nyll.SchemeTheory.Modules.SectionsGluing
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Constructing the graded section ring

The direct sum of tensor-power global sections is embedded into products of polynomial rings
using local frames. The injective coefficient map supplies the ring laws, and the natural summand
ranges supply the grading. No section-ring witness is assumed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GradedOAlgebra
namespace SectionRingConstruction

open Opposite DirectSum

variable {S : Type u} [CommRing S] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)

private theorem app_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    N.presheaf.map i.op (φ.app U s) = φ.app V (M.presheaf.map i.op s) := by
  have h := φ.mapPresheaf.naturality i.op
  exact (congrFun (congrArg (fun k => (ConcreteCategory.hom k : Γ(M, U) → Γ(N, V))) h) s).symm

private def baseHom : S →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom

/-- Global tensor-power sections with the base action pulled back through `f`. -/
private def Sec (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules) (n : ℕ) : ModuleCat S :=
  let : Module S Γ(L.tensorPow n, ⊤) := Module.compHom Γ(L.tensorPow n, ⊤) (baseHom f)
  ModuleCat.of S Γ(L.tensorPow n, ⊤)

scoped instance (n : ℕ) : Module Γ(X, ⊤) (Sec f L n) :=
  inferInstanceAs (Module Γ(X, ⊤) Γ(L.tensorPow n, ⊤))

private theorem baseHom_apply (s : S) : baseHom f s = GradedOAlgebra.baseScalar f s := rfl

private theorem smul_def (n : ℕ) (s : S) (a : Sec f L n) :
    s • a = (GradedOAlgebra.baseScalar f s • (a : Γ(L.tensorPow n, ⊤)) : Γ(L.tensorPow n, ⊤)) := rfl

private def mulSec {m n : ℕ} (a : Sec f L m) (b : Sec f L n) : Sec f L (m + n) :=
  ((tensorPowAdd L m n).hom.app ⊤ (tensorSections (L := L.tensorPow m) (M := L.tensorPow n) a b) :
    Γ(L.tensorPow (m + n), ⊤))

scoped instance : GradedMonoid.GMul (fun n => (Sec f L n : Type u)) where
  mul a b := mulSec f L a b

scoped instance : GradedMonoid.GOne (fun n => (Sec f L n : Type u)) where
  one := (unitSection ⊤ : Γ(𝟙_ X.Modules, ⊤))

private theorem gmul_def {m n : ℕ} (a : Sec f L m) (b : Sec f L n) :
    GradedMonoid.GMul.mul (A := fun n => (Sec f L n : Type u)) a b =
      ((tensorPowAdd L m n).hom.app ⊤
        (tensorSections (L := L.tensorPow m) (M := L.tensorPow n) a b) :
        Γ(L.tensorPow (m + n), ⊤)) := rfl

private theorem gone_def :
    GradedMonoid.GOne.one (A := fun n => (Sec f L n : Type u)) =
    (unitSection ⊤ : Γ(𝟙_ X.Modules, ⊤)) := rfl

scoped instance : DirectSum.GNonUnitalNonAssocSemiring (fun n => (Sec f L n : Type u)) where
  mul_zero a := by
    rw [gmul_def]
    erw [tensorSections_zero_right]
    exact ((tensorPowAdd L _ _).hom.app ⊤).hom.map_zero
  zero_mul b := by
    rw [gmul_def]
    erw [tensorSections_zero_left]
    exact ((tensorPowAdd L _ _).hom.app ⊤).hom.map_zero
  mul_add a b c := by
    rw [gmul_def, gmul_def, gmul_def]
    erw [tensorSections_add_right]
    exact ((tensorPowAdd L _ _).hom.app ⊤).hom.map_add _ _
  add_mul a b c := by
    rw [gmul_def, gmul_def, gmul_def]
    erw [tensorSections_add_left]
    exact ((tensorPowAdd L _ _).hom.app ⊤).hom.map_add _ _

section Frames

variable [Fact (Scheme.Modules.IsInvertible L)]

private theorem exists_frame (x : X) :
    ∃ (U : X.Opens) (g : Γ(L, U)), x ∈ U ∧ IsFrameOn g U := by
  obtain ⟨U, hx, ⟨eU⟩⟩ := (Fact.out : Scheme.Modules.IsInvertible L).1 x
  obtain ⟨g, hg⟩ := exists_isFrameOn_of_pullback_iso_unit U eU
  exact ⟨U, g, hx, hg⟩

private def frU (x : X) : X.Opens :=
  (exists_frame L x).choose

private def frG (x : X) : Γ(L, frU L x) :=
  (exists_frame L x).choose_spec.choose

private theorem mem_frU (x : X) : x ∈ frU L x :=
  (exists_frame L x).choose_spec.choose_spec.1

private theorem isFrameOn_frG (x : X) : IsFrameOn (frG L x) (frU L x) :=
  (exists_frame L x).choose_spec.choose_spec.2

private theorem iSup_frU : (⊤ : X.Opens) ≤ ⨆ x, frU L x :=
  fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, mem_frU L y⟩

private def frG' (x : X) : Γ(L, frU L x) :=
  L.presheaf.map (homOfLE (le_refl (frU L x))).op (frG L x)

private def frE (x : X) (n : ℕ) : Γ(L.tensorPow n, frU L x) := tensorPowSection (frG' L x) n

private theorem bijective_smul_frE (x : X) (n : ℕ) :
    Function.Bijective fun g : Γ(X, frU L x) => g • frE L x n := by
  have h := ((isFrameOn_frG L x).tensorPowSection_monoidalV2 n) (le_refl _) (le_refl _)
  have e : (L.tensorPow n).presheaf.map (homOfLE (le_refl (frU L x))).op
      (tensorPowSection (frG L x) n) =
      frE L x n := map_tensorPowSection _ _ _
  simpa only [e] using h

private def resU (x : X) (n : ℕ) (c : Γ(L.tensorPow n, ⊤)) : Γ(L.tensorPow n, frU L x) :=
  (L.tensorPow n).presheaf.map (homOfLE (le_top : frU L x ≤ ⊤)).op c

private def coef (x : X) (n : ℕ) (c : Γ(L.tensorPow n, ⊤)) : Γ(X, frU L x) :=
  (Equiv.ofBijective _ (bijective_smul_frE L x n)).symm (resU L x n c)

private theorem coef_smul_frE (x : X) (n : ℕ) (c : Γ(L.tensorPow n, ⊤)) :
    coef L x n c • frE L x n = resU L x n c :=
  (Equiv.ofBijective _ (bijective_smul_frE L x n)).apply_symm_apply (resU L x n c)

private theorem coef_eq_of_smul_eq (x : X) (n : ℕ) (c : Γ(L.tensorPow n, ⊤)) (a : Γ(X, frU L x))
    (h : a • frE L x n = resU L x n c) : coef L x n c = a :=
  (bijective_smul_frE L x n).1 ((coef_smul_frE L x n c).trans h.symm)

private theorem coef_zero (x : X) (n : ℕ) : coef L x n 0 = 0 :=
  coef_eq_of_smul_eq L x n 0 0 (by rw [zero_smul, resU, map_zero])

private theorem coef_add (x : X) (n : ℕ) (c d : Γ(L.tensorPow n, ⊤)) :
    coef L x n (c + d) = coef L x n c + coef L x n d :=
  coef_eq_of_smul_eq L x n _ _ (by
    rw [add_smul, coef_smul_frE, coef_smul_frE, resU, resU, resU, map_add])

private theorem coef_smul (x : X) (n : ℕ) (r : Γ(X, ⊤)) (c : Γ(L.tensorPow n, ⊤)) :
    coef L x n (r • c) = X.presheaf.map (homOfLE (le_top : frU L x ≤ ⊤)).op r * coef L x n c :=
  coef_eq_of_smul_eq L x n _ _ (by
    rw [mul_smul, coef_smul_frE, resU, resU, Scheme.Modules.map_smul])

private theorem coef_gmul (x : X) {m n : ℕ} (a : Sec f L m) (b : Sec f L n) :
    coef L x (m + n) (GradedMonoid.GMul.mul (A := fun n => (Sec f L n : Type u)) a b) =
      coef L x m a * coef L x n b := by
  apply coef_eq_of_smul_eq
  erw [resU, gmul_def, app_map, map_homOfLE_tensorSections]
  change (coef L x m a * coef L x n b) • frE L x (m + n) =
    (tensorPowAdd L m n).hom.app (frU L x) (tensorSections (resU L x m a) (resU L x n b))
  erw [← coef_smul_frE L x m a, ← coef_smul_frE L x n b, tensorSections_smul_left,
    tensorSections_smul_right, Hom.app_smul,
    Hom.app_smul, smul_smul]
  simp only [frE]
  erw [tensorPowAdd_hom_app_tensorSections_tensorPowSection]

private theorem coef_gone (x : X) :
    coef L x 0 (GradedMonoid.GOne.one (A := fun n => (Sec f L n : Type u))) = 1 :=
  coef_eq_of_smul_eq L x 0 _ _ (by
    rw [one_smul, gone_def]
    erw [resU]
    exact (map_unitSection (homOfLE (le_top : frU L x ≤ ⊤))).symm)

private theorem eq_zero_of_forall_coef_eq_zero {n : ℕ} (c : Γ(L.tensorPow n, ⊤))
    (h : ∀ x, coef L x n c = 0) : c = 0 := by
  refine (Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible (L.tensorPow n)
    (frU L) ⊤ (fun _ => le_top) (iSup_frU L)).1 c 0 fun x => ?_
  rw [map_zero]
  change resU L x n c = 0
  rw [← coef_smul_frE, h x, zero_smul]

private abbrev Tgt : Type u := ∀ x : X, Polynomial Γ(X, frU L x)

private def coefHom (n : ℕ) : Sec f L n →+ Tgt L where
  toFun c := fun x => Polynomial.monomial n (coef L x n c)
  map_zero' := by funext x; simp only [Pi.zero_apply]; erw [coef_zero]; exact map_zero _
  map_add' c d := by funext x; simp only [Pi.add_apply]; erw [coef_add]; exact map_add _ _ _

private theorem coefHom_apply (n : ℕ) (c : Sec f L n) (x : X) :
    coefHom f L n c x = Polynomial.monomial n (coef L x n c) := rfl

private def F : (⨁ n, Sec f L n) →+ Tgt L := DirectSum.toAddMonoid (coefHom f L)

private theorem F_of (n : ℕ) (c : Sec f L n) :
    F f L (DirectSum.of (fun n => (Sec f L n : Type u)) n c) = coefHom f L n c :=
  DirectSum.toAddMonoid_of _ _ _

private theorem F_mul (r s : ⨁ n, Sec f L n) : F f L (r * s) = F f L r * F f L s := by
  induction r using DirectSum.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add r₁ r₂ h₁ h₂ => rw [add_mul, map_add, map_add, add_mul, h₁, h₂]
  | of m a =>
    induction s using DirectSum.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add s₁ s₂ h₁ h₂ => rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
    | of n b =>
      rw [DirectSum.of_mul_of, F_of, F_of, F_of]
      funext x
      rw [Pi.mul_apply, coefHom_apply, coefHom_apply, coefHom_apply,
        Polynomial.monomial_mul_monomial,
        coef_gmul]

private theorem F_one : F f L 1 = 1 := by
  rw [DirectSum.one_def, F_of]
  funext x
  rw [coefHom_apply, Pi.one_apply, coef_gone, Polynomial.monomial_zero_one]

private theorem F_apply_coeff (r : ⨁ n, Sec f L n) (x : X) (n : ℕ) :
    (F f L r x).coeff n = coef L x n (r n) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of r]
  rw [map_sum, Finset.sum_apply, Polynomial.finsetSum_coeff]
  simp only [F_of, coefHom_apply, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' r.support n]
  split_ifs with h
  · rfl
  · rw [DFinsupp.notMem_support_iff.1 h]
    exact (coef_zero L x n).symm

private theorem F_injective : Function.Injective (F f L) := by
  intro r s h
  rw [← sub_eq_zero]
  have h0 : F f L (r - s) = 0 := by rw [map_sub, h, sub_self]
  ext n
  change ((r - s) n : Γ(L.tensorPow n, ⊤)) = 0
  apply eq_zero_of_forall_coef_eq_zero L
  intro x
  rw [← F_apply_coeff, h0, Pi.zero_apply, Polynomial.coeff_zero]

end Frames

variable [Fact (Scheme.Modules.IsInvertible L)]

private theorem one_mul' (a : ⨁ n, Sec f L n) : 1 * a = a :=
  F_injective f L (by rw [F_mul, F_one, one_mul])

private theorem mul_one' (a : ⨁ n, Sec f L n) : a * 1 = a :=
  F_injective f L (by rw [F_mul, F_one, mul_one])

private theorem mul_assoc' (a b c : ⨁ n, Sec f L n) : a * b * c = a * (b * c) :=
  F_injective f L (by rw [F_mul, F_mul, F_mul, F_mul, mul_assoc])

private theorem mul_comm' (a b : ⨁ n, Sec f L n) : a * b = b * a :=
  F_injective f L (by rw [F_mul, F_mul, mul_comm])

scoped instance instCommRing : CommRing (⨁ n, Sec f L n) :=
  { (inferInstance : NonUnitalNonAssocSemiring (⨁ n, Sec f L n)),
    (inferInstance : AddCommGroup (⨁ n, Sec f L n)),
    (inferInstance : One (⨁ n, Sec f L n)) with
    one_mul := one_mul' f L
    mul_one := mul_one' f L
    mul_assoc := mul_assoc' f L
    mul_comm := mul_comm' f L }

private def cS (s : S) : Tgt L := fun x =>
  Polynomial.C (X.presheaf.map (homOfLE (le_top : frU L x ≤ ⊤)).op (GradedOAlgebra.baseScalar f s))

private theorem F_smul (s : S) (r : ⨁ n, Sec f L n) : F f L (s • r) = cS f L s * F f L r := by
  induction r using DirectSum.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | add r₁ r₂ h₁ h₂ => rw [smul_add, map_add, map_add, mul_add, h₁, h₂]
  | of n a =>
    rw [← DirectSum.of_smul, F_of, F_of]
    funext x
    rw [Pi.mul_apply, coefHom_apply, coefHom_apply, cS, Polynomial.C_mul_monomial, smul_def]
    erw [coef_smul]

private theorem smul_mul' (s : S) (a b : ⨁ n, Sec f L n) : s • a * b = s • (a * b) :=
  F_injective f L (by rw [F_mul, F_smul, F_smul, F_mul, mul_assoc])

private theorem mul_smul' (s : S) (a b : ⨁ n, Sec f L n) : a * s • b = s • (a * b) :=
  F_injective f L (by rw [F_mul, F_smul, F_smul, F_mul, mul_left_comm])

scoped instance instAlgebra : Algebra S (⨁ n, Sec f L n) :=
  Algebra.ofModule (smul_mul' f L) (mul_smul' f L)

private def 𝓡 (n : ℕ) : Submodule S (⨁ n, Sec f L n) where
  carrier := Set.range (DirectSum.of (fun n => (Sec f L n : Type u)) n)
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ a b⟩
  smul_mem' := by
    rintro s _ ⟨a, rfl⟩
    exact ⟨s • a, DirectSum.of_smul _ _ _ _⟩

omit [Fact (Scheme.Modules.IsInvertible L)] in
private theorem mem_𝓡_iff {n : ℕ} (r : ⨁ n, Sec f L n) :
    r ∈ 𝓡 f L n ↔ ∃ a, DirectSum.of (fun n => (Sec f L n : Type u)) n a = r := Iff.rfl

scoped instance : SetLike.GradedMonoid (𝓡 f L) where
  one_mem := ⟨GradedMonoid.GOne.one (A := fun n => (Sec f L n : Type u)), rfl⟩
  mul_mem := by
    rintro i j _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨GradedMonoid.GMul.mul (A := fun n => (Sec f L n : Type u)) a b,
      (DirectSum.of_mul_of (A := fun n => (Sec f L n : Type u)) a b).symm⟩

private def toPiece (n : ℕ) : Sec f L n →+ 𝓡 f L n where
  toFun a := ⟨DirectSum.of (fun n => (Sec f L n : Type u)) n a, a, rfl⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

private def decomposeHom : (⨁ n, Sec f L n) →+ ⨁ n, 𝓡 f L n :=
  DirectSum.toAddMonoid fun n => (DirectSum.of (fun n => 𝓡 f L n) n).comp (toPiece f L n)

private theorem decomposeHom_of (n : ℕ) (a : Sec f L n) :
    decomposeHom f L (DirectSum.of (fun n => (Sec f L n : Type u)) n a) =
      DirectSum.of (fun n => 𝓡 f L n) n (toPiece f L n a) :=
  DirectSum.toAddMonoid_of _ _ _

private theorem coe_comp_decomposeHom :
    (DirectSum.coeAddMonoidHom (𝓡 f L)).comp (decomposeHom f L) = AddMonoidHom.id _ := by
  classical
  refine DirectSum.addHom_ext fun n a => ?_
  rw [AddMonoidHom.comp_apply, decomposeHom_of, DirectSum.coeAddMonoidHom_of,
    AddMonoidHom.id_apply]
  rfl

private theorem decomposeHom_comp_coe :
    (decomposeHom f L).comp (DirectSum.coeAddMonoidHom (𝓡 f L)) = AddMonoidHom.id _ := by
  classical
  refine DirectSum.addHom_ext fun n y => ?_
  obtain ⟨_, a, rfl⟩ := y
  rw [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
  exact decomposeHom_of f L n a

scoped instance : DirectSum.Decomposition (𝓡 f L) where
  decompose' := decomposeHom f L
  left_inv r := by
    have := congrArg (fun k => k r) (coe_comp_decomposeHom f L)
    exact this
  right_inv y := by
    have := congrArg (fun k => k y) (decomposeHom_comp_coe f L)
    exact this

scoped instance instGradedAlgebra : GradedAlgebra (𝓡 f L) :=
  { (inferInstance : SetLike.GradedMonoid (𝓡 f L)),
    (inferInstance : DirectSum.Decomposition (𝓡 f L)) with }

private def ι (n : ℕ) (x : 𝓡 f L n) : Γ(L.tensorPow n, ⊤) := ((x : ⨁ n, Sec f L n) n : Sec f L n)

omit [Fact (Scheme.Modules.IsInvertible L)] in
private theorem ι_of (n : ℕ) (a : Sec f L n)
    (h : DirectSum.of (fun n => (Sec f L n : Type u)) n a ∈ 𝓡 f L n) :
    ι f L n ⟨DirectSum.of (fun n => (Sec f L n : Type u)) n a, h⟩ = a :=
  DirectSum.of_eq_same (β := fun n => (Sec f L n : Type u)) n a

private theorem isSectionRing :
    GradedOAlgebra.IsSectionRing f L (⨁ n, Sec f L n) (𝓡 f L) (ι f L) where
  bijective n := by
    constructor
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ h
      erw [ι_of f L n a _, ι_of f L n b _] at h
      subst h
      rfl
    · intro c
      exact ⟨⟨DirectSum.of (fun n => (Sec f L n : Type u)) n c, c, rfl⟩, ι_of f L n c _⟩
  map_add n x y := DirectSum.add_apply _ _ _
  map_smul n s x := by
    change ((s • (x : ⨁ n, Sec f L n)) n : Sec f L n) = GradedOAlgebra.baseScalar f s • ι f L n x
    rw [DirectSum.smul_apply]
    rfl
  map_one := by
    change ((1 : ⨁ n, Sec f L n) 0 : Sec f L 0) = unitSection ⊤
    rw [DirectSum.one_def, DirectSum.of_eq_same]
    rfl
  map_mul m n x y := by
    obtain ⟨_, a, rfl⟩ := x
    obtain ⟨_, b, rfl⟩ := y
    change ((DirectSum.of (fun n => (Sec f L n : Type u)) m a *
        DirectSum.of (fun n => (Sec f L n : Type u)) n b) (m + n) : Sec f L (m + n)) =
      (tensorPowAdd L m n).hom.app ⊤
        (tensorSections (ι f L m ⟨_, a, rfl⟩) (ι f L n ⟨_, b, rfl⟩))
    rw [DirectSum.of_mul_of, DirectSum.of_eq_same]
    erw [ι_of f L m a _, ι_of f L n b _]
    rfl

end SectionRingConstruction

open scoped DirectSum SectionRingConstruction in
/-- An invertible module sheaf has its concrete graded ring of global tensor-power sections. -/
theorem exists_isSectionRing
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra S R) (𝓡 : ℕ → Submodule S R) (_ : GradedAlgebra 𝓡)
        (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)),
      AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι := by
  have : Fact (Scheme.Modules.IsInvertible L) := ⟨hL⟩
  exact ⟨⨁ n, SectionRingConstruction.Sec f L n, inferInstance, inferInstance,
    SectionRingConstruction.𝓡 f L, inferInstance,
    SectionRingConstruction.ι f L, SectionRingConstruction.isSectionRing f L⟩

end AlgebraicGeometry.GradedOAlgebra
