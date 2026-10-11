/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.InverseLimits.Predicates

/-!
# Pro C Groups / Free Products / Universal Property

This module defines the binary free pro-C universal property and its canonical
comparison maps and equivalences.
-/


namespace ProCGroups.FreeProducts
universe u


section FreeProCProducts

variable {C : ProCGroups.FiniteGroupClass}
variable {G₁ : Type u} {G₂ : Type u} {F : Type u}
variable [Group G₁] [TopologicalSpace G₁]
variable [Group G₂] [TopologicalSpace G₂]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

/--
Binary free pro-\(C\) products via the strengthened universal property used elsewhere in the
project: every pair of continuous homomorphisms into a pro-\(C\) target extends uniquely.
-/
structure IsFreeProCProduct
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (ι₁ : G₁ →ₜ* F) (ι₂ : G₂ →ₜ* F) : Prop where
  /--
  Open normal subgroups with quotients in `C` form a neighborhood basis at one in the proposed
  free product.
  -/
  hasOpenNormalBasisInClass : ProCGroups.ProC.HasOpenNormalBasisInClass C F
  /--
  Any pair of continuous homomorphisms from the two factors into a pro-`C` target extends to a
  unique continuous homomorphism from `F`, with the two prescribed composites.
  -/
  existsUnique_lift :
    ∀ {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
      [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K],
    ProCGroups.ProC.HasOpenNormalBasisInClass C (K) →
      ∀ (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K),
        ∃! φ : F →ₜ* K, φ.comp ι₁ = φ₁ ∧ φ.comp ι₂ = φ₂


namespace IsFreeProCProduct

variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable {ι₁ : G₁ →ₜ* F} {ι₂ : G₂ →ₜ* F}

/-- The universal property selects a descent morphism from a binary free product object. -/
noncomputable def lift (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : ProCGroups.ProC.HasOpenNormalBasisInClass C (K))
    (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K) : F →ₜ* K :=
  Classical.choose (ExistsUnique.exists (hF.existsUnique_lift hK φ₁ φ₂))

omit [IsTopologicalGroup F] in
/-- The chosen free-product descent morphism has the prescribed composites. -/
theorem lift_spec (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : ProCGroups.ProC.HasOpenNormalBasisInClass C (K))
    (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K) :
    (hF.lift hK φ₁ φ₂).comp ι₁ = φ₁ ∧ (hF.lift hK φ₁ φ₂).comp ι₂ = φ₂ :=
  Classical.choose_spec (ExistsUnique.exists (hF.existsUnique_lift hK φ₁ φ₂))

omit [IsTopologicalGroup F] in
/-- The left composite of the chosen free-product descent morphism is the prescribed left leg. -/
@[simp] theorem lift_left (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : ProCGroups.ProC.HasOpenNormalBasisInClass C (K))
    (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K) :
    (hF.lift hK φ₁ φ₂).comp ι₁ = φ₁ :=
  (hF.lift_spec hK φ₁ φ₂).1

omit [IsTopologicalGroup F] in
/-- The right composite of the chosen free-product descent morphism is the prescribed right leg. -/
@[simp] theorem lift_right (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : ProCGroups.ProC.HasOpenNormalBasisInClass C (K))
    (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K) :
    (hF.lift hK φ₁ φ₂).comp ι₂ = φ₂ :=
  (hF.lift_spec hK φ₁ φ₂).2

omit [IsTopologicalGroup F] in
/-- Uniqueness of the chosen free-product descent morphism. -/
theorem lift_unique (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : ProCGroups.ProC.HasOpenNormalBasisInClass C (K))
    (φ₁ : G₁ →ₜ* K) (φ₂ : G₂ →ₜ* K)
    {ψ : F →ₜ* K} (hψ : ψ.comp ι₁ = φ₁ ∧ ψ.comp ι₂ = φ₂) :
    ψ = hF.lift hK φ₁ φ₂ := by
  exact
    (hF.existsUnique_lift hK φ₁ φ₂).unique hψ
      (hF.lift_spec hK φ₁ φ₂)

/-- The distinguished descent map from a free product object to itself is the identity. -/
@[simp] theorem lift_self (hF : IsFreeProCProduct (C := C) ι₁ ι₂) :
    hF.lift hF.hasOpenNormalBasisInClass ι₁ ι₂ = ContinuousMonoidHom.id F := by
  symm
  exact hF.lift_unique hF.hasOpenNormalBasisInClass ι₁ ι₂ ⟨rfl, rfl⟩

omit [IsTopologicalGroup F] in
/--
Homomorphisms out of a free-product object are equal when they agree on the canonical factors.
-/
theorem hom_ext (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (hK : ProCGroups.ProC.HasOpenNormalBasisInClass C (K))
    {ψ ψ' : F →ₜ* K}
    (h₁ : ψ.comp ι₁ = ψ'.comp ι₁) (h₂ : ψ.comp ι₂ = ψ'.comp ι₂) :
    ψ = ψ' := by
  exact
    (hF.existsUnique_lift hK (ψ.comp ι₁) (ψ.comp ι₂)).unique
      ⟨rfl, rfl⟩ ⟨h₁.symm, h₂.symm⟩

variable {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
variable [CompactSpace F'] [T2Space F'] [TotallyDisconnectedSpace F']
variable {ι₁' : G₁ →ₜ* F'} {ι₂' : G₂ →ₜ* F'}

/--
The canonical comparison morphism between two free product objects on the same pair of factors.
-/
noncomputable def compare (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    (hF' : IsFreeProCProduct (C := C) ι₁' ι₂') :
    F →ₜ* F' :=
  hF.lift hF'.hasOpenNormalBasisInClass ι₁' ι₂'

omit [IsTopologicalGroup F] in
/--
The left composite of the canonical comparison map between free product objects is the
prescribed left leg.
-/
@[simp 900] theorem compare_left (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    (hF' : IsFreeProCProduct (C := C) ι₁' ι₂') :
    (hF.compare hF').comp ι₁ = ι₁' :=
  hF.lift_left hF'.hasOpenNormalBasisInClass ι₁' ι₂'

omit [IsTopologicalGroup F] in
/--
The right composite of the canonical comparison map between free product objects is the
prescribed right leg.
-/
@[simp 900] theorem compare_right (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    (hF' : IsFreeProCProduct (C := C) ι₁' ι₂') :
    (hF.compare hF').comp ι₂ = ι₂' :=
  hF.lift_right hF'.hasOpenNormalBasisInClass ι₁' ι₂'

/-- The canonical comparison map from a free product object to itself is the identity. -/
@[simp 900] theorem compare_self (hF : IsFreeProCProduct (C := C) ι₁ ι₂) :
    hF.compare hF = ContinuousMonoidHom.id F := by
  exact hF.lift_self

variable {F'' : Type u} [Group F''] [TopologicalSpace F''] [IsTopologicalGroup F'']
variable [CompactSpace F''] [T2Space F''] [TotallyDisconnectedSpace F'']
variable {ι₁'' : G₁ →ₜ* F''} {ι₂'' : G₂ →ₜ* F''}

omit [IsTopologicalGroup F] in
/-- Composition of free-product comparison maps is the expected direct comparison map. -/
theorem compare_comp (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    (hF' : IsFreeProCProduct (C := C) ι₁' ι₂')
    (hF'' : IsFreeProCProduct (C := C) ι₁'' ι₂'') :
    (hF'.compare hF'').comp (hF.compare hF') = hF.compare hF'' := by
  apply hF.hom_ext hF''.hasOpenNormalBasisInClass
  · calc
      ((hF'.compare hF'').comp (hF.compare hF')).comp ι₁
          = (hF'.compare hF'').comp ((hF.compare hF').comp ι₁) := by rfl
      _ = (hF'.compare hF'').comp ι₁' := by rw [hF.compare_left hF']
      _ = ι₁'' := hF'.compare_left hF''
      _ = (hF.compare hF'').comp ι₁ := (hF.compare_left hF'').symm
  · calc
      ((hF'.compare hF'').comp (hF.compare hF')).comp ι₂
          = (hF'.compare hF'').comp ((hF.compare hF').comp ι₂) := by rfl
      _ = (hF'.compare hF'').comp ι₂' := by rw [hF.compare_right hF']
      _ = ι₂'' := hF'.compare_right hF''
      _ = (hF.compare hF'').comp ι₂ := (hF.compare_right hF'').symm

/-- Any two binary free product objects on the same factors are canonically isomorphic. -/
noncomputable def equiv (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    (hF' : IsFreeProCProduct (C := C) ι₁' ι₂') :
    F ≃ₜ* F' := by
  let φ : F →ₜ* F' := hF.compare hF'
  let ψ : F' →ₜ* F := hF'.compare hF
  have hleft : ψ.comp φ = ContinuousMonoidHom.id F := by
    calc
      ψ.comp φ = hF.compare hF := by
        simpa [φ, ψ] using hF.compare_comp hF' hF
      _ = ContinuousMonoidHom.id F := hF.compare_self
  have hright : φ.comp ψ = ContinuousMonoidHom.id F' := by
    calc
      φ.comp ψ = hF'.compare hF' := by
        simpa [φ, ψ] using hF'.compare_comp hF hF'
      _ = ContinuousMonoidHom.id F' := hF'.compare_self
  refine ContinuousMulEquiv.mk'
    (Homeomorph.mk
      (MonoidHom.toMulEquiv φ.toMonoidHom ψ.toMonoidHom
        (by
          have hleft' := congrArg ContinuousMonoidHom.toMonoidHom hleft
          change ψ.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id F at hleft'
          exact hleft')
        (by
          have hright' := congrArg ContinuousMonoidHom.toMonoidHom hright
          change φ.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id F' at hright'
          exact hright'))
      φ.continuous_toFun ψ.continuous_toFun)
    ?_
  intro x y
  exact φ.map_mul x y

/--
The left composite of the canonical equivalence between free-product objects is the canonical
left map.
-/
@[simp] theorem equiv_left (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    (hF' : IsFreeProCProduct (C := C) ι₁' ι₂') :
    ((hF.equiv hF' : F →ₜ* F').comp ι₁) = ι₁' := by
  exact hF.compare_left hF'

/--
The right composite of the canonical equivalence between free product objects is the prescribed
right leg.
-/
@[simp] theorem equiv_right (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    (hF' : IsFreeProCProduct (C := C) ι₁' ι₂') :
    ((hF.equiv hF' : F →ₜ* F').comp ι₂) = ι₂' := by
  exact hF.compare_right hF'

/-- Left-leg formula for the inverse canonical free-product equivalence. -/
theorem equiv_symm_left (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    (hF' : IsFreeProCProduct (C := C) ι₁' ι₂') :
    (((hF.equiv hF').symm : F' →ₜ* F).comp ι₁') = ι₁ := by
  change (hF'.compare hF).comp ι₁' = ι₁
  exact hF'.compare_left hF

/-- Right-leg formula for the inverse canonical free-product equivalence. -/
theorem equiv_symm_right (hF : IsFreeProCProduct (C := C) ι₁ ι₂)
    (hF' : IsFreeProCProduct (C := C) ι₁' ι₂') :
    (((hF.equiv hF').symm : F' →ₜ* F).comp ι₂') = ι₂ := by
  change (hF'.compare hF).comp ι₂' = ι₂
  exact hF'.compare_right hF

end IsFreeProCProduct


end FreeProCProducts

end ProCGroups.FreeProducts
