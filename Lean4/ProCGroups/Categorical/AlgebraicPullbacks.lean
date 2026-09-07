import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false

/-!
# Pro C Groups / Categorical / Algebraic Pullbacks

This module develops concrete fiber products of groups, identifies them with
the categorical pullback in `GrpCat`, and proves comparison and kernel
criteria for the associated lift maps.
-/

namespace ProCGroups.Categorical

open CategoryTheory Limits
open scoped Pointwise

universe u v

section

variable {A G H H₁ H₂ : Type u} {K : Type v}
variable [Group A] [Group G] [Group H] [Group H₁] [Group H₂] [Group K]

/-- Concrete pullback subgroup of \(\beta_1\) and \(\beta_2\). -/
def FiberProduct.subgroup (β₁ : H₁ →* H) (β₂ : H₂ →* H) : Subgroup (H₁ × H₂) where
  carrier := { x | β₁ x.1 = β₂ x.2 }
  one_mem' := by simp only [Set.mem_ofPred_eq, Prod.fst_one, map_one, Prod.snd_one]
  mul_mem' := by
    intro x y hx hy
    change β₁ x.1 = β₂ x.2 at hx
    change β₁ y.1 = β₂ y.2 at hy
    simpa [map_mul] using congrArg₂ (· * ·) hx hy
  inv_mem' := by
    intro x hx
    simpa [map_inv, hx]

/-- Concrete pullback attached to \(\beta_1\) and \(\beta_2\). -/
abbrev FiberProduct.carrier (β₁ : H₁ →* H) (β₂ : H₂ →* H) :=
  ↥(FiberProduct.subgroup β₁ β₂)

/-- Membership in the pullback subgroup is equivalent to the displayed coordinate condition. -/
@[simp] theorem mem_pullbackSubgroup_iff {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {x : H₁ × H₂} :
    x ∈ FiberProduct.subgroup β₁ β₂ ↔ β₁ x.1 = β₂ x.2 :=
  Iff.rfl

/-- The first projection from the concrete pullback. -/
def FiberProduct.fst (β₁ : H₁ →* H) (β₂ : H₂ →* H) : FiberProduct.carrier β₁ β₂ →* H₁ where
  toFun := fun x => x.1.1
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- The second projection from the concrete pullback. -/
def FiberProduct.snd (β₁ : H₁ →* H) (β₂ : H₂ →* H) : FiberProduct.carrier β₁ β₂ →* H₂ where
  toFun := fun x => x.1.2
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- The canonical homomorphism into the concrete pullback. -/
def FiberProduct.lift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) : K →* FiberProduct.carrier β₁ β₂ where
  toFun := fun k => ⟨(φ₁ k, φ₂ k), h k⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one, OneMemClass.coe_one, Prod.mk_eq_one, and_self]
  map_mul' := by
    intro x y
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, Prod.mk_mul_mk]

/-- The concrete group pullback as a categorical pullback cone in GrpCat. -/
def FiberProduct.cone (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    PullbackCone (GrpCat.ofHom β₁) (GrpCat.ofHom β₂) :=
  PullbackCone.mk
    (GrpCat.ofHom (FiberProduct.fst β₁ β₂))
    (GrpCat.ofHom (FiberProduct.snd β₁ β₂))
    (by
      apply GrpCat.hom_ext
      ext x
      exact x.2)

/-- The concrete group pullback cone is a limit cone in GrpCat. -/
def FiberProduct.isLimitCone (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    IsLimit (FiberProduct.cone β₁ β₂) := by
  refine PullbackCone.IsLimit.mk (by
    apply GrpCat.hom_ext
    ext x
    exact x.2) ?lift ?fac_left ?fac_right ?uniq
  · intro s
    exact GrpCat.ofHom <|
      FiberProduct.lift β₁ β₂ s.fst.hom s.snd.hom (fun x => by
        have hcondition :
            (s.fst ≫ GrpCat.ofHom β₁).hom =
              (s.snd ≫ GrpCat.ofHom β₂).hom :=
          congrArg (fun f : s.pt ⟶ GrpCat.of H => f.hom) s.condition
        exact DFunLike.congr_fun hcondition x)
  · intro s
    apply GrpCat.hom_ext
    rfl
  · intro s
    apply GrpCat.hom_ext
    rfl
  · intro s m hfst hsnd
    apply GrpCat.hom_ext
    ext x
    · have hfst' :
          (m ≫ GrpCat.ofHom (FiberProduct.fst β₁ β₂)).hom = s.fst.hom :=
        congrArg (fun f : s.pt ⟶ GrpCat.of H₁ => f.hom) hfst
      exact DFunLike.congr_fun hfst' x
    · have hsnd' :
          (m ≫ GrpCat.ofHom (FiberProduct.snd β₁ β₂)).hom = s.snd.hom :=
        congrArg (fun f : s.pt ⟶ GrpCat.of H₂ => f.hom) hsnd
      exact DFunLike.congr_fun hsnd' x

/-- The concrete group fiber product is a pullback in mathlib's bundled category of groups. -/
theorem FiberProduct.isPullback (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    CategoryTheory.IsPullback
      (GrpCat.ofHom (FiberProduct.fst β₁ β₂))
      (GrpCat.ofHom (FiberProduct.snd β₁ β₂))
      (GrpCat.ofHom β₁) (GrpCat.ofHom β₂) :=
  CategoryTheory.IsPullback.of_isLimit (FiberProduct.isLimitCone β₁ β₂)

/--
The kernel of the canonical map into a concrete pullback is the intersection of the two
coordinate kernels.
-/
@[simp] theorem ker_pullbackLift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (FiberProduct.lift β₁ β₂ φ₁ φ₂ h).ker = φ₁.ker ⊓ φ₂.ker := by
  ext k
  change FiberProduct.lift β₁ β₂ φ₁ φ₂ h k = 1 ↔ φ₁ k = 1 ∧ φ₂ k = 1
  constructor
  · intro hk
    exact ⟨congrArg (fun z => FiberProduct.fst β₁ β₂ z) hk,
      congrArg (fun z => FiberProduct.snd β₁ β₂ z) hk⟩
  · rintro ⟨h₁, h₂⟩
    apply Subtype.ext
    exact Prod.ext h₁ h₂

/--
The canonical map into a concrete pullback is injective iff the two coordinate kernels intersect
trivially.
-/
theorem pullbackLift_injective_iff (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    {φ₁ : K →* H₁} {φ₂ : K →* H₂}
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    Function.Injective (FiberProduct.lift β₁ β₂ φ₁ φ₂ h) ↔ φ₁.ker ⊓ φ₂.ker = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_pullbackLift]

/--
The supremum of the two kernels is contained in the kernel of the composite when the composites
agree.
-/
theorem ker_sup_le_ker_comp_of_comp_eq
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂) :
    φ₁.ker ⊔ φ₂.ker ≤ (β₁.comp φ₁).ker := by
  rw [sup_le_iff]
  constructor
  · intro k hk
    change β₁ (φ₁ k) = 1
    have hk' : φ₁ k = 1 := by simpa using hk
    simp only [hk', map_one]
  · intro k hk
    calc
      β₁ (φ₁ k) = β₂ (φ₂ k) := DFunLike.congr_fun hcomp k
      _ = 1 := by
        have hk' : φ₂ k = 1 := by simpa using hk
        simp only [hk', map_one]

/-- The algebraic pullback lift is surjective exactly when the composite kernel is contained in
the supremum of the two coordinate kernels. -/
theorem pullbackLift_surjective_iff_ker_comp_le_sup_ker
    {β₁ : H₁ →* H} (β₂ : H₂ →* H)
    {φ₁ : K →* H₁} {φ₂ : K →* H₂}
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂) :
    Function.Surjective (FiberProduct.lift β₁ β₂ φ₁ φ₂
        (fun k => DFunLike.congr_fun hcomp k)) ↔
      (β₁.comp φ₁).ker ≤ φ₁.ker ⊔ φ₂.ker := by
  constructor
  · intro hsurj k hk
    let z : FiberProduct.carrier β₁ β₂ :=
      ⟨(φ₁ k, 1), by
        change β₁ (φ₁ k) = β₂ 1
        simpa using hk⟩
    rcases hsurj z with ⟨a, ha⟩
    have hφ₁a : φ₁ a = φ₁ k := by
      exact congrArg (fun y => FiberProduct.fst β₁ β₂ y) ha
    have hφ₂a : φ₂ a = 1 := by
      exact congrArg (fun y => FiberProduct.snd β₁ β₂ y) ha
    have ha_ker₂ : a ∈ φ₂.ker := by
      simpa using hφ₂a
    have ha_inv_mul_ker₁ : a⁻¹ * k ∈ φ₁.ker := by
      change φ₁ (a⁻¹ * k) = 1
      simp only [map_mul, map_inv, hφ₁a, inv_mul_cancel]
    have hprod : a * (a⁻¹ * k) ∈ φ₁.ker ⊔ φ₂.ker :=
      (φ₁.ker ⊔ φ₂.ker).mul_mem
        ((le_sup_right : φ₂.ker ≤ φ₁.ker ⊔ φ₂.ker) ha_ker₂)
        ((le_sup_left : φ₁.ker ≤ φ₁.ker ⊔ φ₂.ker) ha_inv_mul_ker₁)
    simpa [mul_assoc] using hprod
  · intro hker_le z
    rcases hφ₁ z.1.1 with ⟨a₁, ha₁⟩
    rcases hφ₂ z.1.2 with ⟨a₂, ha₂⟩
    have hEq : β₁ (φ₁ a₁) = β₁ (φ₁ a₂) := by
      calc
        β₁ (φ₁ a₁) = β₁ z.1.1 := by simp only [ha₁]
        _ = β₂ z.1.2 := z.2
        _ = β₂ (φ₂ a₂) := by simp only [ha₂]
        _ = β₁ (φ₁ a₂) := by
          exact (DFunLike.congr_fun hcomp a₂).symm
    have hgker : a₁ * a₂⁻¹ ∈ (β₁.comp φ₁).ker := by
      change β₁ (φ₁ (a₁ * a₂⁻¹)) = 1
      simp only [map_mul, map_inv, hEq, mul_inv_cancel]
    have hgjoin : a₁ * a₂⁻¹ ∈ (φ₁.ker : Subgroup K) ⊔ (φ₂.ker : Subgroup K) :=
      hker_le hgker
    have hgjoin' : a₁ * a₂⁻¹ ∈ ((φ₁.ker : Set K) * (φ₂.ker : Set K)) := by
      rw [← Subgroup.mul_normal (φ₁.ker) (φ₂.ker)]
      simpa [SetLike.mem_coe] using hgjoin
    rcases (show ∃ y ∈ (φ₁.ker : Set K), ∃ z ∈ (φ₂.ker : Set K),
        y * z = a₁ * a₂⁻¹ from by
          simpa [Set.mem_mul] using hgjoin') with ⟨k₁, hk₁, k₂, hk₂, hkprod⟩
    have hk₁' : φ₁ k₁ = 1 := by simpa using hk₁
    have hk₂' : φ₂ k₂ = 1 := by simpa using hk₂
    have haeq : a₁ = k₁ * k₂ * a₂ := by
      calc
        a₁ = (a₁ * a₂⁻¹) * a₂ := by simp only [mul_assoc, inv_mul_cancel, mul_one]
        _ = (k₁ * k₂) * a₂ := by rw [hkprod]
        _ = k₁ * k₂ * a₂ := by simp only [mul_assoc]
    refine ⟨k₂ * a₂, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · calc
        φ₁ (k₂ * a₂) = φ₁ (k₁ * k₂ * a₂) := by
          simp only [map_mul, mul_assoc, hk₁', one_mul]
        _ = φ₁ a₁ := by rw [haeq]
        _ = z.1.1 := ha₁
    · calc
        φ₂ (k₂ * a₂) = φ₂ k₂ * φ₂ a₂ := by rw [map_mul]
        _ = 1 * φ₂ a₂ := by simp only [hk₂', one_mul]
        _ = z.1.2 := by simp only [ha₂, one_mul]

/-- Surjectivity of the algebraic pullback lift is equivalent to the required kernel equality. -/
theorem pullbackLift_surjective_iff_ker_eq
    {β₁ : H₁ →* H} (β₂ : H₂ →* H)
    {φ₁ : K →* H₁} {φ₂ : K →* H₂}
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂) :
    Function.Surjective (FiberProduct.lift β₁ β₂ φ₁ φ₂
        (fun k => DFunLike.congr_fun hcomp k)) ↔
      (β₁.comp φ₁).ker = φ₁.ker ⊔ φ₂.ker := by
  constructor
  · intro hsurj
    exact le_antisymm
      ((pullbackLift_surjective_iff_ker_comp_le_sup_ker
        (β₁ := β₁) (β₂ := β₂) (φ₁ := φ₁) (φ₂ := φ₂) hφ₁ hφ₂ hcomp).1 hsurj)
      (ker_sup_le_ker_comp_of_comp_eq β₁ β₂ φ₁ φ₂ hcomp)
  · intro hker
    exact (pullbackLift_surjective_iff_ker_comp_le_sup_ker
      (β₁ := β₁) (β₂ := β₂) (φ₁ := φ₁) (φ₂ := φ₂) hφ₁ hφ₂ hcomp).2 (by
        intro k hk
        rw [← hker]
        exact hk)

/-- Composing the first projection with the canonical pullback lift gives \(\varphi_1\). -/
@[simp] theorem pullbackFst_pullbackLift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (FiberProduct.fst β₁ β₂).comp (FiberProduct.lift β₁ β₂ φ₁ φ₂ h) = φ₁ := by
  ext k
  rfl

/-- Composing the second projection with the canonical pullback lift gives \(\varphi_2\). -/
@[simp] theorem pullbackSnd_pullbackLift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (FiberProduct.snd β₁ β₂).comp (FiberProduct.lift β₁ β₂ φ₁ φ₂ h) = φ₂ := by
  ext k
  rfl

/--
If \(\varphi_1\) is injective, then the canonical map into the concrete pullback is injective.
-/
theorem pullbackLift_injective_of_left_injective (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k))
    (hφ₁ : Function.Injective φ₁) :
    Function.Injective (FiberProduct.lift β₁ β₂ φ₁ φ₂ h) := by
  intro x y hxy
  apply hφ₁
  exact congrArg (fun z => FiberProduct.fst β₁ β₂ z) hxy

/--
If \(\varphi_2\) is injective, then the canonical map into the concrete pullback is injective.
-/
theorem pullbackLift_injective_of_right_injective (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k))
    (hφ₂ : Function.Injective φ₂) :
    Function.Injective (FiberProduct.lift β₁ β₂ φ₁ φ₂ h) := by
  intro x y hxy
  apply hφ₂
  exact congrArg (fun z => FiberProduct.snd β₁ β₂ z) hxy

/-- Two homomorphisms into the concrete pullback are equal once both coordinates agree. -/
theorem FiberProduct.hom_ext {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {K : Type v} [Group K]
    {ψ ψ' : K →* FiberProduct.carrier β₁ β₂}
    (h₁ : ∀ k, FiberProduct.fst β₁ β₂ (ψ k) = FiberProduct.fst β₁ β₂ (ψ' k))
    (h₂ : ∀ k, FiberProduct.snd β₁ β₂ (ψ k) = FiberProduct.snd β₁ β₂ (ψ' k)) :
    ψ = ψ' := by
  apply MonoidHom.ext
  intro k
  exact Subtype.ext <| Prod.ext (h₁ k) (h₂ k)

namespace FiberProduct

/-- Transport a concrete fiber product across equal cospan maps. -/
def congr {β₁ β₁' : H₁ →* H} {β₂ β₂' : H₂ →* H}
    (h₁ : β₁ = β₁') (h₂ : β₂ = β₂') :
    carrier β₁ β₂ ≃* carrier β₁' β₂' := by
  subst β₁'
  subst β₂'
  exact MulEquiv.refl _

end FiberProduct

/-- The concrete pullback is reconstructed from its two projections by the canonical lift. -/
@[simp 900] theorem pullbackLift_eta {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {K : Type v} [Group K]
    (ψ : K →* FiberProduct.carrier β₁ β₂) :
    FiberProduct.lift β₁ β₂
      ((FiberProduct.fst β₁ β₂).comp ψ)
      ((FiberProduct.snd β₁ β₂).comp ψ)
      (fun k => by exact (ψ k).2) = ψ := by
  apply FiberProduct.hom_ext
  · intro k
    rfl
  · intro k
    rfl

/-- Symmetry of the concrete pullback. -/
def pullbackSwap (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    FiberProduct.carrier β₁ β₂ ≃* FiberProduct.carrier β₂ β₁ where
  toFun := fun x => ⟨(x.1.2, x.1.1), x.2.symm⟩
  invFun := fun x => ⟨(x.1.2, x.1.1), x.2.symm⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl
  map_mul' := by
    intro x y
    apply Subtype.ext
    rfl

/-- The first projection after swapping equals the original second projection. -/
@[simp] theorem pullbackFst_pullbackSwap (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (x : FiberProduct.carrier β₁ β₂) :
    FiberProduct.fst β₂ β₁ (pullbackSwap β₁ β₂ x) = FiberProduct.snd β₁ β₂ x :=
  rfl

/-- The second projection after swapping equals the original first projection. -/
@[simp] theorem pullbackSnd_pullbackSwap (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (x : FiberProduct.carrier β₁ β₂) :
    FiberProduct.snd β₂ β₁ (pullbackSwap β₁ β₂ x) = FiberProduct.fst β₁ β₂ x :=
  rfl

/--
The symmetry map for the algebraic pullback is inverse to the corresponding swapped pullback
comparison.
-/
@[simp] theorem pullbackSwap_symm (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    (pullbackSwap β₁ β₂).symm = pullbackSwap β₂ β₁ :=
  rfl

/-- If the right cospan map is surjective, then the first projection from the fiber product is
surjective. -/
theorem pullbackFst_surjective_of_right_surjective
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hβ₂ : Function.Surjective β₂) :
    Function.Surjective (FiberProduct.fst β₁ β₂) := by
  intro x
  rcases hβ₂ (β₁ x) with ⟨y, hy⟩
  refine ⟨⟨(x, y), ?_⟩, rfl⟩
  simp only [mem_pullbackSubgroup_iff, hy]

/-- If the left cospan map is surjective, then the second projection from the fiber product is
surjective. -/
theorem pullbackSnd_surjective_of_left_surjective
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hβ₁ : Function.Surjective β₁) :
    Function.Surjective (FiberProduct.snd β₁ β₂) := by
  intro y
  rcases hβ₁ (β₂ y) with ⟨x, hx⟩
  refine ⟨⟨(x, y), ?_⟩, rfl⟩
  simp only [mem_pullbackSubgroup_iff, hx]

/-- If \(\beta_2\) is injective, then the first pullback projection is injective. -/
theorem pullbackFst_injective_of_right_injective
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hβ₂ : Function.Injective β₂) :
    Function.Injective (FiberProduct.fst β₁ β₂) := by
  intro x y hxy
  apply Subtype.ext
  exact Prod.ext hxy <| hβ₂ <| by
    calc
      β₂ x.1.2 = β₁ x.1.1 := x.2.symm
      _ = β₁ y.1.1 := by
        have h := congrArg β₁ hxy
        change β₁ x.1.1 = β₁ y.1.1 at h
        exact h
      _ = β₂ y.1.2 := y.2

/-- If \(\beta_1\) is injective, then the second pullback projection is injective. -/
theorem pullbackSnd_injective_of_left_injective
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (hβ₁ : Function.Injective β₁) :
    Function.Injective (FiberProduct.snd β₁ β₂) := by
  intro x y hxy
  apply Subtype.ext
  exact Prod.ext (hβ₁ <| by
      calc
        β₁ x.1.1 = β₂ x.1.2 := x.2
        _ = β₂ y.1.2 := by
          have h := congrArg β₂ hxy
          change β₂ x.1.2 = β₂ y.1.2 at h
          exact h
        _ = β₁ y.1.1 := y.2.symm) hxy

/-- Surjective coordinate maps whose composite kernel is the supremum of their kernels induce a
surjective map into the concrete fiber product. -/
theorem surjective_pullbackLift_of_ker_eq
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : A →* H₁) (φ₂ : A →* H₂)
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂)
    (hker : (β₁.comp φ₁).ker = φ₁.ker ⊔ φ₂.ker) :
    Function.Surjective (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => by
      exact DFunLike.congr_fun hcomp a)) := by
  exact (pullbackLift_surjective_iff_ker_eq (β₁ := β₁) (β₂ := β₂) (φ₁ := φ₁) (φ₂ := φ₂) hφ₁ hφ₂
      hcomp).2 hker

/--
The algebraic pullback lift is bijective when the left map is injective and the required kernel
equality holds.
-/
theorem bijective_pullbackLift_of_left_injective_of_ker_eq
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : A →* H₁) (φ₂ : A →* H₂)
    (hφ₁surj : Function.Surjective φ₁) (hφ₂surj : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂)
    (hker : (β₁.comp φ₁).ker = φ₁.ker ⊔ φ₂.ker)
    (hφ₁inj : Function.Injective φ₁) :
    Function.Bijective (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => by
      exact DFunLike.congr_fun hcomp a)) := by
  refine ⟨?_, ?_⟩
  · exact pullbackLift_injective_of_left_injective β₁ β₂ φ₁ φ₂
      (fun a => DFunLike.congr_fun hcomp a) hφ₁inj
  · exact (pullbackLift_surjective_iff_ker_eq
      (β₁ := β₁) (β₂ := β₂) (φ₁ := φ₁) (φ₂ := φ₂) hφ₁surj hφ₂surj hcomp).2 hker

/--
The algebraic pullback lift is bijective when the right map is injective and the required kernel
equality holds.
-/
theorem bijective_pullbackLift_of_right_injective_of_ker_eq
    (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : A →* H₁) (φ₂ : A →* H₂)
    (hφ₁surj : Function.Surjective φ₁) (hφ₂surj : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂)
    (hker : (β₁.comp φ₁).ker = φ₁.ker ⊔ φ₂.ker)
    (hφ₂inj : Function.Injective φ₂) :
    Function.Bijective (FiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => by
      exact DFunLike.congr_fun hcomp a)) := by
  refine ⟨?_, ?_⟩
  · exact pullbackLift_injective_of_right_injective β₁ β₂ φ₁ φ₂
      (fun a => DFunLike.congr_fun hcomp a) hφ₂inj
  · exact (pullbackLift_surjective_iff_ker_eq
      (β₁ := β₁) (β₂ := β₂) (φ₁ := φ₁) (φ₂ := φ₂) hφ₁surj hφ₂surj hcomp).2 hker

end



end ProCGroups.Categorical
