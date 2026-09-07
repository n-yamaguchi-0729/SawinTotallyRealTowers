import ProCGroups.ProC.InverseLimits.Predicates

set_option autoImplicit false

/-!
# Pro C Groups / Completion / Universal Property

This module defines the universal property of a pro-\(C\) completion and proves
the resulting lift, uniqueness, comparison, and canonical-equivalence results.
-/

open scoped Topology

namespace ProCGroups.Completion

universe u v

variable {C : ProCGroups.FiniteGroupClass}

/-- An abstract pro-\(C\) completion of a topological group. -/
structure IsProCCompletion
    (C : ProCGroups.FiniteGroupClass)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Ghat : Type u) [Group Ghat] [TopologicalSpace Ghat] [IsTopologicalGroup Ghat]
      [CompactSpace Ghat] [T2Space Ghat] [TotallyDisconnectedSpace Ghat]
    (ι : G →ₜ* Ghat) : Prop where
  /--
  Open normal subgroups with quotients in `C` form a neighborhood basis at one in the completed
  group.
  -/
  hasOpenNormalBasisInClass : ProCGroups.ProC.HasOpenNormalBasisInClass C Ghat
  /-- The image of the original group under the completion map is dense in `Ghat`. -/
  denseRange : DenseRange ι
  /--
  Every continuous homomorphism from `G` to a pro-`C` target extends uniquely to a continuous
  homomorphism from `Ghat`.
  -/
  existsUnique_lift :
    ∀ {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H],
    ProCGroups.ProC.HasOpenNormalBasisInClass C (H) →
      ∀ (φ : G →ₜ* H), ∃! φbar : Ghat →ₜ* H, φbar.comp ι = φ

namespace IsProCCompletion

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {Ghat : Type u} [Group Ghat] [TopologicalSpace Ghat] [IsTopologicalGroup Ghat]
variable [CompactSpace Ghat] [T2Space Ghat] [TotallyDisconnectedSpace Ghat]
variable {ι : G →ₜ* Ghat}

/--
A continuous homomorphism from the source group to a pro-\(C\) target factors uniquely through
the pro-\(C\) completion.
-/
noncomputable def lift
    (hι : IsProCCompletion C G Ghat ι)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H)) (φ : G →ₜ* H) :
    Ghat →ₜ* H :=
  Classical.choose (ExistsUnique.exists (hι.existsUnique_lift hH φ))

/--
The universal-property lift is continuous and extends the given homomorphism along the
completion map.
-/
theorem lift_spec
    (hι : IsProCCompletion C G Ghat ι)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H)) (φ : G →ₜ* H) :
    (hι.lift hH φ).comp ι = φ :=
  Classical.choose_spec (ExistsUnique.exists (hι.existsUnique_lift hH φ))

/-- The universal-property lift is the unique continuous map extending the given homomorphism. -/
theorem lift_unique
    (hι : IsProCCompletion C G Ghat ι)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H)) (φ : G →ₜ* H)
    {f : Ghat →ₜ* H} (hfac : f.comp ι = φ) :
    f = hι.lift hH φ :=
  (hι.existsUnique_lift hH φ).unique hfac (hι.lift_spec hH φ)

/--
Continuous homomorphisms out of a pro-\(C\) completion are determined by their composites with
the dense source map.
-/
theorem hom_ext
    (hι : IsProCCompletion C G Ghat ι)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    {f g : Ghat →ₜ* H}
    (hfg : f.comp ι = g.comp ι) :
    f = g :=
  (hι.existsUnique_lift hH (f.comp ι)).unique rfl hfg.symm

/-- The lift of the completion map to the completion itself is the identity. -/
@[simp] theorem lift_self_eq_id
    (hι : IsProCCompletion C G Ghat ι) :
    hι.lift hι.hasOpenNormalBasisInClass ι = ContinuousMonoidHom.id Ghat := by
  symm
  exact hι.lift_unique hι.hasOpenNormalBasisInClass ι rfl

variable {Ghat₂ : Type u} [Group Ghat₂] [TopologicalSpace Ghat₂] [IsTopologicalGroup Ghat₂]
variable [CompactSpace Ghat₂] [T2Space Ghat₂] [TotallyDisconnectedSpace Ghat₂]
variable {ι₂ : G →ₜ* Ghat₂}

/-- The canonical comparison map between two pro-\(C\) completions of the same group. -/
noncomputable def comparison
    (h₁ : IsProCCompletion C G Ghat ι)
    (h₂ : IsProCCompletion C G Ghat₂ ι₂) : Ghat →ₜ* Ghat₂ :=
  h₁.lift h₂.hasOpenNormalBasisInClass ι₂

/--
The comparison map between two pro-\(C\) completions agrees with the second completion map on
the source.
-/
theorem comparison_spec
    (h₁ : IsProCCompletion C G Ghat ι)
    (h₂ : IsProCCompletion C G Ghat₂ ι₂) :
    (h₁.comparison h₂).comp ι = ι₂ :=
  h₁.lift_spec h₂.hasOpenNormalBasisInClass ι₂

/-- The two comparison maps between pro-\(C\) completions compose to the identity. -/
@[simp 900] theorem comparison_comp_eq_id
    (h₁ : IsProCCompletion C G Ghat ι)
    (h₂ : IsProCCompletion C G Ghat₂ ι₂) :
    (h₂.comparison h₁).comp (h₁.comparison h₂) = ContinuousMonoidHom.id Ghat := by
  let e12 : Ghat →ₜ* Ghat₂ := h₁.comparison h₂
  let e21 : Ghat₂ →ₜ* Ghat := h₂.comparison h₁
  have he12 : e12.comp ι = ι₂ := h₁.comparison_spec h₂
  have he21 : e21.comp ι₂ = ι := h₂.comparison_spec h₁
  have hfac : (e21.comp e12).comp ι = ι := by
    ext x
    have h12 : e12 (ι x) = ι₂ x := congrArg (fun f : G →ₜ* Ghat₂ => f x) he12
    have h21 : e21 (ι₂ x) = ι x := congrArg (fun f : G →ₜ* Ghat => f x) he21
    simpa [MonoidHom.comp_apply, h12] using h21
  calc
    e21.comp e12 = h₁.lift h₁.hasOpenNormalBasisInClass ι :=
      h₁.lift_unique h₁.hasOpenNormalBasisInClass ι hfac
    _ = ContinuousMonoidHom.id Ghat := h₁.lift_self_eq_id

/--
The canonical multiplicative homeomorphism between two pro-\(C\) completions of the same
topological group.
-/
noncomputable def continuousMulEquiv
    (h₁ : IsProCCompletion C G Ghat ι)
    (h₂ : IsProCCompletion C G Ghat₂ ι₂) : Ghat ≃ₜ* Ghat₂ :=
  let f : Ghat →ₜ* Ghat₂ := h₁.comparison h₂
  let g : Ghat₂ →ₜ* Ghat := h₂.comparison h₁
  { toMulEquiv :=
      { toFun := f
        invFun := g
        left_inv := by
          intro x
          have hgf : g.comp f = ContinuousMonoidHom.id Ghat := h₁.comparison_comp_eq_id h₂
          exact congrArg (fun h : Ghat →ₜ* Ghat => h x) hgf
        right_inv := by
          intro x
          have hfg : f.comp g = ContinuousMonoidHom.id Ghat₂ := h₂.comparison_comp_eq_id h₁
          exact congrArg (fun h : Ghat₂ →ₜ* Ghat₂ => h x) hfg
        map_mul' := f.map_mul }
    continuous_toFun := f.continuous_toFun
    continuous_invFun := g.continuous_toFun }

/--
The canonical equivalence between pro-\(C\) completions sends one completion map to the other.
-/
@[simp] theorem continuousMulEquiv_apply_completionMap
    (h₁ : IsProCCompletion C G Ghat ι)
    (h₂ : IsProCCompletion C G Ghat₂ ι₂) (x : G) :
    h₁.continuousMulEquiv h₂ (ι x) = ι₂ x := by
  simpa [continuousMulEquiv, comparison] using
    congrArg (fun f : G →ₜ* Ghat₂ => f x) (h₁.comparison_spec h₂)

/--
The inverse canonical equivalence between pro-\(C\) completions sends the second completion map
back to the first.
-/
@[simp] theorem continuousMulEquiv_symm_apply_completionMap
    (h₁ : IsProCCompletion C G Ghat ι)
    (h₂ : IsProCCompletion C G Ghat₂ ι₂) (x : G) :
    (h₁.continuousMulEquiv h₂).symm (ι₂ x) = ι x := by
  change h₂.comparison h₁ (ι₂ x) = ι x
  exact congrArg (fun f : G →ₜ* Ghat => f x) (h₂.comparison_spec h₁)

end IsProCCompletion

end ProCGroups.Completion
