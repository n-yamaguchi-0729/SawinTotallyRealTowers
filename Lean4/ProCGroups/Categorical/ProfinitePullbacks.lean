import ProCGroups.Categorical.AlgebraicPullbacks
import ProCGroups.Profinite.Basic
import ProCGroups.Topologies.ContinuousMulEquiv
import ProCGroups.TopologicalGroups

set_option autoImplicit false

/-!
# Continuous pullbacks of topological groups

This module develops continuous fiber products and the universal property
obtained by testing a continuous square against profinite source groups. The
four objects in a tested square are not required to be profinite.
-/

namespace ProCGroups.Categorical

open CategoryTheory Limits

universe u v

section

open _root_.ProCGroups.ContinuousMonoidHom

variable {A G H H₁ H₂ K : Type u}

/-- Continuous pullback carrier attached to two continuous homomorphisms. -/
abbrev TopologicalFiberProduct.carrier
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :=
  FiberProduct.carrier (β₁ : H₁ →* H) (β₂ : H₂ →* H)

/-- The first projection from the continuous pullback. -/
def TopologicalFiberProduct.fst
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :
    TopologicalFiberProduct.carrier β₁ β₂ →ₜ* H₁ :=
  { FiberProduct.fst (β₁ : H₁ →* H) (β₂ : H₂ →* H) with
    continuous_toFun := continuous_fst.comp continuous_subtype_val }

/-- The second projection from the continuous pullback. -/
def TopologicalFiberProduct.snd
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :
    TopologicalFiberProduct.carrier β₁ β₂ →ₜ* H₂ :=
  { FiberProduct.snd (β₁ : H₁ →* H) (β₂ : H₂ →* H) with
    continuous_toFun := continuous_snd.comp continuous_subtype_val }

/-- Extensionality for continuous homomorphisms into the concrete continuous fiber product. -/
theorem TopologicalFiberProduct.hom_ext
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    {ψ ψ' : K →ₜ* TopologicalFiberProduct.carrier β₁ β₂}
    (h₁ : ∀ k, TopologicalFiberProduct.fst β₁ β₂ (ψ k) = TopologicalFiberProduct.fst β₁ β₂ (ψ' k))
    (h₂ : ∀ k, TopologicalFiberProduct.snd β₁ β₂ (ψ k) = TopologicalFiberProduct.snd β₁ β₂ (ψ' k)) :
    ψ = ψ' := by
  apply ContinuousMonoidHom.ext
  intro k
  exact Subtype.ext <| Prod.ext (h₁ k) (h₂ k)

/--
If the right map in the pullback square is surjective, then the first projection from the
continuous pullback is surjective.
-/
theorem pullbackFstCont_surjective_of_right_surjective
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hβ₂ : Function.Surjective β₂) :
    Function.Surjective (TopologicalFiberProduct.fst β₁ β₂) := by
  change Function.Surjective
    (FiberProduct.fst (β₁ : H₁ →* H) (β₂ : H₂ →* H))
  exact pullbackFst_surjective_of_right_surjective
    (β₁ := (β₁ : H₁ →* H)) (β₂ := (β₂ : H₂ →* H)) hβ₂

/--
If the left map in the pullback square is surjective, then the second projection from the
continuous pullback is surjective.
-/
theorem pullbackSndCont_surjective_of_left_surjective
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hβ₁ : Function.Surjective β₁) :
    Function.Surjective (TopologicalFiberProduct.snd β₁ β₂) := by
  change Function.Surjective
    (FiberProduct.snd (β₁ : H₁ →* H) (β₂ : H₂ →* H))
  exact pullbackSnd_surjective_of_left_surjective
    (β₁ := (β₁ : H₁ →* H)) (β₂ := (β₂ : H₂ →* H)) hβ₁

/-- If \(\beta_2\) is injective, then the first continuous pullback projection is injective. -/
theorem pullbackFstCont_injective_of_right_injective
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hβ₂ : Function.Injective β₂) :
    Function.Injective (TopologicalFiberProduct.fst β₁ β₂) := by
  change Function.Injective
    (FiberProduct.fst (β₁ : H₁ →* H) (β₂ : H₂ →* H))
  exact pullbackFst_injective_of_right_injective
    (β₁ := (β₁ : H₁ →* H)) (β₂ := (β₂ : H₂ →* H)) hβ₂

/-- If \(\beta_1\) is injective, then the second continuous pullback projection is injective. -/
theorem pullbackSndCont_injective_of_left_injective
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (hβ₁ : Function.Injective β₁) :
    Function.Injective (TopologicalFiberProduct.snd β₁ β₂) := by
  change Function.Injective
    (FiberProduct.snd (β₁ : H₁ →* H) (β₂ : H₂ →* H))
  exact pullbackSnd_injective_of_left_injective
    (β₁ := (β₁ : H₁ →* H)) (β₂ := (β₂ : H₂ →* H)) hβ₁

/-- The canonical continuous map into the pullback. -/
def TopologicalFiberProduct.lift
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    K →ₜ* TopologicalFiberProduct.carrier β₁ β₂ :=
  { FiberProduct.lift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
      (φ₁ : K →* H₁) (φ₂ : K →* H₂) h with
    continuous_toFun := by
      exact Continuous.subtype_mk
        (φ₁.continuous_toFun.prodMk φ₂.continuous_toFun)
        (by
          intro k
          exact h k) }

/-- Composing the first projection with the continuous pullback lift gives \(\varphi_1\). -/
@[simp] theorem pullbackFstCont_pullbackLiftCont
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (TopologicalFiberProduct.fst β₁ β₂).comp (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ h) = φ₁ := by
  ext k
  rfl

/-- Composing the second projection with the continuous pullback lift gives \(\varphi_2\). -/
@[simp] theorem pullbackSndCont_pullbackLiftCont
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (TopologicalFiberProduct.snd β₁ β₂).comp (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ h) = φ₂ := by
  ext k
  rfl

/-- The continuous pullback is reconstructed from its two projections by the canonical lift. -/
@[simp] theorem pullbackLiftCont_eta
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    (ψ : K →ₜ* TopologicalFiberProduct.carrier β₁ β₂) :
    TopologicalFiberProduct.lift β₁ β₂
      ((TopologicalFiberProduct.fst β₁ β₂).comp ψ)
      ((TopologicalFiberProduct.snd β₁ β₂).comp ψ)
      (fun k => by exact (ψ k).2) = ψ := by
  apply TopologicalFiberProduct.hom_ext
  · intro k
    rfl
  · intro k
    rfl

/-- The concrete topological fiber product as a categorical pullback cone in TopGrp. -/
def TopologicalFiberProduct.cone
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [IsTopologicalGroup H] [IsTopologicalGroup H₁] [IsTopologicalGroup H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :
    PullbackCone (TopGrp.ofHom β₁) (TopGrp.ofHom β₂) :=
  PullbackCone.mk
    (TopGrp.ofHom (TopologicalFiberProduct.fst β₁ β₂))
    (TopGrp.ofHom (TopologicalFiberProduct.snd β₁ β₂))
    (by
      apply TopGrp.hom_ext
      ext x
      exact x.2)

/-- The concrete topological fiber product cone is a limit cone in TopGrp. -/
def TopologicalFiberProduct.isLimit
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [IsTopologicalGroup H] [IsTopologicalGroup H₁] [IsTopologicalGroup H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :
    IsLimit (TopologicalFiberProduct.cone β₁ β₂) := by
  refine PullbackCone.IsLimit.mk (by
    apply TopGrp.hom_ext
    ext x
    exact x.2) ?lift ?fac_left ?fac_right ?uniq
  · intro s
    exact TopGrp.ofHom <|
      TopologicalFiberProduct.lift β₁ β₂ s.fst.hom s.snd.hom (fun x => by
        have hcondition :
            (s.fst ≫ TopGrp.ofHom β₁).hom =
              (s.snd ≫ TopGrp.ofHom β₂).hom :=
          congrArg (fun f : s.pt ⟶ TopGrp.of H => f.hom) s.condition
        exact DFunLike.congr_fun hcondition x)
  · intro s
    apply TopGrp.hom_ext
    rfl
  · intro s
    apply TopGrp.hom_ext
    rfl
  · intro s m hfst hsnd
    apply TopGrp.hom_ext
    ext x
    · have hfst' :
          (m ≫ TopGrp.ofHom (TopologicalFiberProduct.fst β₁ β₂)).hom = s.fst.hom :=
        congrArg (fun f : s.pt ⟶ TopGrp.of H₁ => f.hom) hfst
      exact DFunLike.congr_fun hfst' x
    · have hsnd' :
          (m ≫ TopGrp.ofHom (TopologicalFiberProduct.snd β₁ β₂)).hom = s.snd.hom :=
        congrArg (fun f : s.pt ⟶ TopGrp.of H₂ => f.hom) hsnd
      exact DFunLike.congr_fun hsnd' x

/--
If \(\varphi_1\) is injective, then the continuous canonical map into the continuous fiber
product is injective.
-/
theorem pullbackLiftCont_injective_of_left_injective
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k))
    (hφ₁ : Function.Injective φ₁) :
    Function.Injective (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ h) := by
  change Function.Injective
    (FiberProduct.lift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
      (φ₁ : K →* H₁) (φ₂ : K →* H₂) h)
  exact pullbackLift_injective_of_left_injective
    (β₁ := (β₁ : H₁ →* H)) (β₂ := (β₂ : H₂ →* H))
    (φ₁ := (φ₁ : K →* H₁)) (φ₂ := (φ₂ : K →* H₂))
    h hφ₁

/--
If \(\varphi_2\) is injective, then the continuous canonical map into the continuous fiber
product is injective.
-/
theorem pullbackLiftCont_injective_of_right_injective
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k))
    (hφ₂ : Function.Injective φ₂) :
    Function.Injective (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ h) := by
  change Function.Injective
    (FiberProduct.lift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
      (φ₁ : K →* H₁) (φ₂ : K →* H₂) h)
  exact pullbackLift_injective_of_right_injective
    (β₁ := (β₁ : H₁ →* H)) (β₂ := (β₂ : H₂ →* H))
    (φ₁ := (φ₁ : K →* H₁)) (φ₂ := (φ₂ : K →* H₂))
    h hφ₂

/--
Continuous pullback property tested by profinite source objects. The property tests the square
against profinite objects without requiring the four objects of the square themselves to be
profinite.
-/
def HasProfiniteTestPullbackProperty
    [Group G] [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) : Prop :=
  β₁.comp α₁ = β₂.comp α₂ ∧
    ∀ ⦃K : Type u⦄ [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
      [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K],
      ∀ (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂),
      β₁.comp φ₁ = β₂.comp φ₂ →
      ∃! φ : K →ₜ* G, α₁.comp φ = φ₁ ∧ α₂.comp φ = φ₂




/-- Chosen continuous morphism induced by the pullback universal property. -/
noncomputable def pullbackDescCont
    [Group G] [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    {α₁ : G →ₜ* H₁} {α₂ : G →ₜ* H₂}
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) : K →ₜ* G :=
  Classical.choose (ExistsUnique.exists (hpb.2 (K := K) φ₁ φ₂ hφ))

/-- Specification of the chosen continuous pullback descent map. -/
theorem pullbackDescCont_spec
    [Group G] [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    {α₁ : G →ₜ* H₁} {α₂ : G →ₜ* H₂}
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) :
    α₁.comp (pullbackDescCont hpb φ₁ φ₂ hφ) = φ₁ ∧
      α₂.comp (pullbackDescCont hpb φ₁ φ₂ hφ) = φ₂ :=
  Classical.choose_spec (ExistsUnique.exists (hpb.2 (K := K) φ₁ φ₂ hφ))

/-- The left composite of the chosen continuous pullback descent map is the prescribed left leg. -/
@[simp] theorem pullbackDescCont_left
    [Group G] [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    {α₁ : G →ₜ* H₁} {α₂ : G →ₜ* H₂}
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) :
    α₁.comp (pullbackDescCont hpb φ₁ φ₂ hφ) = φ₁ :=
  (pullbackDescCont_spec hpb φ₁ φ₂ hφ).1

/--
The right composite of the chosen continuous pullback descent map is the prescribed right leg.
-/
@[simp] theorem pullbackDescCont_right
    [Group G] [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    {α₁ : G →ₜ* H₁} {α₂ : G →ₜ* H₂}
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) :
    α₂.comp (pullbackDescCont hpb φ₁ φ₂ hφ) = φ₂ :=
  (pullbackDescCont_spec hpb φ₁ φ₂ hφ).2

/-- Uniqueness of the chosen continuous pullback descent map. -/
theorem pullbackDescCont_uniq
    [Group G] [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    {α₁ : G →ₜ* H₁} {α₂ : G →ₜ* H₂}
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂)
    {ψ : K →ₜ* G}
    (hψ : α₁.comp ψ = φ₁ ∧ α₂.comp ψ = φ₂) :
    ψ = pullbackDescCont hpb φ₁ φ₂ hφ :=
  (hpb.2 (K := K) φ₁ φ₂ hφ).unique hψ
    (pullbackDescCont_spec hpb φ₁ φ₂ hφ)

/-- The concrete pullback subgroup is closed in \(H_1 \times H_2\). -/
theorem pullback_isClosed
    {H H₁ H₂ : Type u}
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [T2Space H]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :
    IsClosed ((FiberProduct.subgroup (β₁ : H₁ →* H) (β₂ : H₂ →* H) : Subgroup (H₁ × H₂)) :
      Set (H₁ × H₂)) := by
  change IsClosed { x : H₁ × H₂ | β₁ x.1 = β₂ x.2 }
  exact isClosed_eq (β₁.continuous_toFun.comp continuous_fst)
    (β₂.continuous_toFun.comp continuous_snd)

/-- The concrete pullback of continuous maps between compact Hausdorff groups is compact. -/
noncomputable instance TopologicalFiberProduct.compactSpace
    {H H₁ H₂ : Type u}
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [CompactSpace H₁] [CompactSpace H₂] [T2Space H]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    : CompactSpace (TopologicalFiberProduct.carrier β₁ β₂) := by
  apply isCompact_iff_compactSpace.1
  simpa [TopologicalFiberProduct.carrier, FiberProduct.carrier] using
    (pullback_isClosed β₁ β₂).isCompact

/-- The concrete continuous fiber product has the restricted profinite-source test property. -/
theorem TopologicalFiberProduct.hasProfiniteTestPullbackProperty
    {H H₁ H₂ : Type u}
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :
    HasProfiniteTestPullbackProperty (TopologicalFiberProduct.fst β₁ β₂)
        (TopologicalFiberProduct.snd β₁ β₂) β₁ β₂ := by
  refine ⟨?_, ?_⟩
  · ext x
    exact x.2
  · intro K _ _ _ _ _ _ φ₁ φ₂ hφ
    refine ⟨TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k), ?_, ?_⟩
    · exact ⟨pullbackFstCont_pullbackLiftCont β₁ β₂ φ₁ φ₂
        (fun k => DFunLike.congr_fun hφ k),
        pullbackSndCont_pullbackLiftCont β₁ β₂ φ₁ φ₂
          (fun k => DFunLike.congr_fun hφ k)⟩
    · intro ψ hψ
      have hfst :
          (TopologicalFiberProduct.fst β₁ β₂).comp ψ =
            (TopologicalFiberProduct.fst β₁ β₂).comp
              (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)) := by
        calc
          (TopologicalFiberProduct.fst β₁ β₂).comp ψ = φ₁ := hψ.1
          _ =
              (TopologicalFiberProduct.fst β₁ β₂).comp
                (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)) := by
              symm
              exact pullbackFstCont_pullbackLiftCont β₁ β₂ φ₁ φ₂
                (fun k => DFunLike.congr_fun hφ k)
      have hsnd :
          (TopologicalFiberProduct.snd β₁ β₂).comp ψ =
            (TopologicalFiberProduct.snd β₁ β₂).comp
              (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)) := by
        calc
          (TopologicalFiberProduct.snd β₁ β₂).comp ψ = φ₂ := hψ.2
          _ =
              (TopologicalFiberProduct.snd β₁ β₂).comp
                (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)) := by
              symm
              exact pullbackSndCont_pullbackLiftCont β₁ β₂ φ₁ φ₂
                (fun k => DFunLike.congr_fun hφ k)
      exact TopologicalFiberProduct.hom_ext
        (fun k => by
          exact congrArg (fun f : K →ₜ* H₁ => f k) hfst)
        (fun k => by
          exact congrArg (fun f : K →ₜ* H₂ => f k) hsnd)



/--
A profinite square with a bijective continuous comparison map to the concrete fiber product has
the profinite-source test property.
-/
theorem hasProfiniteTestPullbackProperty_of_bijective_toConcretePullback
    {G H H₁ H₂ : Type u}
    [Group G] [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [IsTopologicalGroup H₁] [IsTopologicalGroup H₂]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    [CompactSpace H₁] [T2Space H₁] [TotallyDisconnectedSpace H₁]
    [CompactSpace H₂] [T2Space H₂] [TotallyDisconnectedSpace H₂]
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (τ : G →ₜ* TopologicalFiberProduct.carrier β₁ β₂)
    (hτ : Function.Bijective τ)
    (h₁ : (TopologicalFiberProduct.fst β₁ β₂).comp τ = α₁)
    (h₂ : (TopologicalFiberProduct.snd β₁ β₂).comp τ = α₂) :
    HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂ := by
  refine ⟨?_, ?_⟩
  · ext g
    have hτ₁ : TopologicalFiberProduct.fst β₁ β₂ (τ g) = α₁ g := by
      simpa using congrArg (fun f : G →ₜ* H₁ => f g) h₁
    have hτ₂ : TopologicalFiberProduct.snd β₁ β₂ (τ g) = α₂ g := by
      simpa using congrArg (fun f : G →ₜ* H₂ => f g) h₂
    calc
      β₁ (α₁ g) = β₁ (TopologicalFiberProduct.fst β₁ β₂ (τ g)) := by rw [← hτ₁]
      _ = β₂ (TopologicalFiberProduct.snd β₁ β₂ (τ g)) := (τ g).2
      _ = β₂ (α₂ g) := by rw [hτ₂]
  · intro K _ _ _ _ _ _ φ₁ φ₂ hφ
    let e : G ≃ₜ* TopologicalFiberProduct.carrier β₁ β₂ :=
      ContinuousMulEquiv.ofBijectiveCompactToT2 τ τ.continuous_toFun hτ
    let θ : K →ₜ* TopologicalFiberProduct.carrier β₁ β₂ :=
      TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)
    have hθ₁ : (TopologicalFiberProduct.fst β₁ β₂).comp θ = φ₁ := by
      ext k
      rfl
    have hθ₂ : (TopologicalFiberProduct.snd β₁ β₂).comp θ = φ₂ := by
      ext k
      rfl
    refine ⟨(ContinuousMonoidHom.toContinuousMonoidHom e.symm).comp θ, ?_, ?_⟩
    · constructor
      · ext k
        have hτ₁ : TopologicalFiberProduct.fst β₁ β₂ (τ (e.symm (θ k))) = α₁ (e.symm (θ k)) := by
          simpa using congrArg (fun f : G →ₜ* H₁ => f (e.symm (θ k))) h₁
        have hθ₁' : TopologicalFiberProduct.fst β₁ β₂ (θ k) = φ₁ k := by
          simpa using congrArg (fun f : K →ₜ* H₁ => f k) hθ₁
        calc
          α₁ (e.symm (θ k)) = TopologicalFiberProduct.fst β₁ β₂ (τ (e.symm (θ k))) := by
            simpa using hτ₁.symm
          _ = TopologicalFiberProduct.fst β₁ β₂ (θ k) := by
            rw [show τ (e.symm (θ k)) = θ k from e.apply_symm_apply (θ k)]
          _ = φ₁ k := hθ₁'
      · ext k
        have hτ₂ : TopologicalFiberProduct.snd β₁ β₂ (τ (e.symm (θ k))) = α₂ (e.symm (θ k)) := by
          simpa using congrArg (fun f : G →ₜ* H₂ => f (e.symm (θ k))) h₂
        have hθ₂' : TopologicalFiberProduct.snd β₁ β₂ (θ k) = φ₂ k := by
          simpa using congrArg (fun f : K →ₜ* H₂ => f k) hθ₂
        calc
          α₂ (e.symm (θ k)) = TopologicalFiberProduct.snd β₁ β₂ (τ (e.symm (θ k))) := by
            simpa using hτ₂.symm
          _ = TopologicalFiberProduct.snd β₁ β₂ (θ k) := by
            rw [show τ (e.symm (θ k)) = θ k from e.apply_symm_apply (θ k)]
          _ = φ₂ k := hθ₂'
    · intro ψ hψ
      have hcoord : τ.comp ψ = θ := by
        apply TopologicalFiberProduct.hom_ext
        · intro k
          have hτ₁ : TopologicalFiberProduct.fst β₁ β₂ (τ (ψ k)) = α₁ (ψ k) := by
            simpa using congrArg (fun f : G →ₜ* H₁ => f (ψ k)) h₁
          have hψ₁ : α₁ (ψ k) = φ₁ k := by
            simpa using congrArg (fun f : K →ₜ* H₁ => f k) hψ.1
          have hθ₁' : TopologicalFiberProduct.fst β₁ β₂ (θ k) = φ₁ k := by
            simpa using congrArg (fun f : K →ₜ* H₁ => f k) hθ₁
          calc
            TopologicalFiberProduct.fst β₁ β₂ ((τ.comp ψ) k) = α₁ (ψ k) := by
              simpa using hτ₁
            _ = φ₁ k := hψ₁
            _ = TopologicalFiberProduct.fst β₁ β₂ (θ k) := hθ₁'.symm
        · intro k
          have hτ₂ : TopologicalFiberProduct.snd β₁ β₂ (τ (ψ k)) = α₂ (ψ k) := by
            simpa using congrArg (fun f : G →ₜ* H₂ => f (ψ k)) h₂
          have hψ₂ : α₂ (ψ k) = φ₂ k := by
            simpa using congrArg (fun f : K →ₜ* H₂ => f k) hψ.2
          have hθ₂' : TopologicalFiberProduct.snd β₁ β₂ (θ k) = φ₂ k := by
            simpa using congrArg (fun f : K →ₜ* H₂ => f k) hθ₂
          calc
            TopologicalFiberProduct.snd β₁ β₂ ((τ.comp ψ) k) = α₂ (ψ k) := by
              simpa using hτ₂
            _ = φ₂ k := hψ₂
            _ = TopologicalFiberProduct.snd β₁ β₂ (θ k) := hθ₂'.symm
      ext k
      apply hτ.1
      calc
        τ (ψ k) = (τ.comp ψ) k := by rfl
        _ = θ k := by
          exact congrArg (fun f : K →ₜ* TopologicalFiberProduct.carrier β₁ β₂ => f k) hcoord
        _ = τ (((ContinuousMonoidHom.toContinuousMonoidHom e.symm).comp θ) k) := by
          change θ k = τ (e.symm (θ k))
          symm
          exact e.apply_symm_apply (θ k)


/--
A continuous multiplicative equivalence with the concrete fiber product transports the
profinite-source test property.
-/
theorem hasProfiniteTestPullbackProperty_of_equiv_toConcretePullback
    [Group G] [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (e : G ≃ₜ* TopologicalFiberProduct.carrier β₁ β₂)
    (h₁ : (TopologicalFiberProduct.fst β₁ β₂).comp (ContinuousMonoidHom.toContinuousMonoidHom e)
        = α₁)
    (h₂ : (TopologicalFiberProduct.snd β₁ β₂).comp (ContinuousMonoidHom.toContinuousMonoidHom e)
        = α₂) :
    HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂ := by
  refine ⟨?_, ?_⟩
  · ext g
    have h₁g : TopologicalFiberProduct.fst β₁ β₂ (e g) = α₁ g := by
      simpa using congrArg (fun f : G →ₜ* H₁ => f g) h₁
    have h₂g : TopologicalFiberProduct.snd β₁ β₂ (e g) = α₂ g := by
      simpa using congrArg (fun f : G →ₜ* H₂ => f g) h₂
    calc
      β₁ (α₁ g) = β₁ (TopologicalFiberProduct.fst β₁ β₂ (e g)) := by rw [← h₁g]
      _ = β₂ (TopologicalFiberProduct.snd β₁ β₂ (e g)) := (e g).2
      _ = β₂ (α₂ g) := by rw [h₂g]
  · intro K _ _ _ _ _ _ φ₁ φ₂ hφ
    let θ : K →ₜ* TopologicalFiberProduct.carrier β₁ β₂ :=
      TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k)
    refine ⟨(ContinuousMonoidHom.toContinuousMonoidHom e.symm).comp θ, ?_, ?_⟩
    · constructor
      · ext k
        have h₁k : TopologicalFiberProduct.fst β₁ β₂ (e (e.symm (θ k))) = α₁ (e.symm (θ k)) := by
          simpa using congrArg (fun f : G →ₜ* H₁ => f (e.symm (θ k))) h₁
        calc
          α₁ (((ContinuousMonoidHom.toContinuousMonoidHom e.symm).comp θ) k) = α₁ (e.symm (θ k))
              := rfl
          _ = TopologicalFiberProduct.fst β₁ β₂ (e (e.symm (θ k))) := by
            simpa using h₁k.symm
          _ = TopologicalFiberProduct.fst β₁ β₂ (θ k) := by rw [e.apply_symm_apply]
          _ = φ₁ k := by
            change
              TopologicalFiberProduct.fst β₁ β₂
                (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k) k) =
                  φ₁ k
            rfl
      · ext k
        have h₂k : TopologicalFiberProduct.snd β₁ β₂ (e (e.symm (θ k))) = α₂ (e.symm (θ k)) := by
          simpa using congrArg (fun f : G →ₜ* H₂ => f (e.symm (θ k))) h₂
        calc
          α₂ (((ContinuousMonoidHom.toContinuousMonoidHom e.symm).comp θ) k) = α₂ (e.symm (θ k))
              := rfl
          _ = TopologicalFiberProduct.snd β₁ β₂ (e (e.symm (θ k))) := by
            simpa using h₂k.symm
          _ = TopologicalFiberProduct.snd β₁ β₂ (θ k) := by rw [e.apply_symm_apply]
          _ = φ₂ k := by
            change
              TopologicalFiberProduct.snd β₁ β₂
                (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k) k) =
                  φ₂ k
            rfl
    · intro ψ hψ
      have hcoord : (ContinuousMonoidHom.toContinuousMonoidHom e).comp ψ = θ := by
        apply TopologicalFiberProduct.hom_ext
        · intro k
          have h₁ψ : TopologicalFiberProduct.fst β₁ β₂ (e (ψ k)) = α₁ (ψ k) := by
            simpa using congrArg (fun f : G →ₜ* H₁ => f (ψ k)) h₁
          have hψ₁ : α₁ (ψ k) = φ₁ k := by
            simpa using congrArg (fun f : K →ₜ* H₁ => f k) hψ.1
          calc
            TopologicalFiberProduct.fst β₁ β₂ (((ContinuousMonoidHom.toContinuousMonoidHom
                e).comp ψ) k) = α₁ (ψ k) := by
              simpa using h₁ψ
            _ = φ₁ k := hψ₁
            _ = TopologicalFiberProduct.fst β₁ β₂ (θ k) := by
              change
                φ₁ k =
                  TopologicalFiberProduct.fst β₁ β₂
                    (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k) k)
              rfl
        · intro k
          have h₂ψ : TopologicalFiberProduct.snd β₁ β₂ (e (ψ k)) = α₂ (ψ k) := by
            simpa using congrArg (fun f : G →ₜ* H₂ => f (ψ k)) h₂
          have hψ₂ : α₂ (ψ k) = φ₂ k := by
            simpa using congrArg (fun f : K →ₜ* H₂ => f k) hψ.2
          calc
            TopologicalFiberProduct.snd β₁ β₂ (((ContinuousMonoidHom.toContinuousMonoidHom
                e).comp ψ) k) = α₂ (ψ k) := by
              simpa using h₂ψ
            _ = φ₂ k := hψ₂
            _ = TopologicalFiberProduct.snd β₁ β₂ (θ k) := by
              change
                φ₂ k =
                  TopologicalFiberProduct.snd β₁ β₂
                    (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun k => DFunLike.congr_fun hφ k) k)
              rfl
      ext k
      apply e.injective
      calc
        e (ψ k) = ((ContinuousMonoidHom.toContinuousMonoidHom e).comp ψ) k := by rfl
        _ = θ k := by
          exact congrArg (fun f : K →ₜ* TopologicalFiberProduct.carrier β₁ β₂ => f k) hcoord
        _ = e (e.symm (θ k)) := by rw [e.apply_symm_apply]

/-- The continuous pullback lift is surjective exactly when the underlying composite kernel is
contained in the supremum of the two underlying coordinate kernels. -/
theorem pullbackLiftCont_surjective_iff_ker_comp_le_sup_ker
    [Group A] [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace A] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    {β₁ : H₁ →ₜ* H} (β₂ : H₂ →ₜ* H)
    {φ₁ : A →ₜ* H₁} {φ₂ : A →ₜ* H₂}
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂) :
    Function.Surjective (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂
        (fun a => DFunLike.congr_fun hcomp a)) ↔
      ((β₁.comp φ₁ : A →ₜ* H).toMonoidHom).ker ≤
        ((φ₁ : A →ₜ* H₁).toMonoidHom).ker ⊔
          ((φ₂ : A →ₜ* H₂).toMonoidHom).ker := by
  have hcomp' :
      ((β₁ : H₁ →* H).comp (φ₁ : A →* H₁)) =
        ((β₂ : H₂ →* H).comp (φ₂ : A →* H₂)) := by
    ext a
    exact DFunLike.congr_fun hcomp a
  change
    Function.Surjective
        (FiberProduct.lift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
          (φ₁ : A →* H₁) (φ₂ : A →* H₂) _) ↔
      ((β₁ : H₁ →* H).comp (φ₁ : A →* H₁)).ker ≤
        (φ₁ : A →* H₁).ker ⊔ (φ₂ : A →* H₂).ker
  exact pullbackLift_surjective_iff_ker_comp_le_sup_ker
    (β₁ := (β₁ : H₁ →* H)) (β₂ := (β₂ : H₂ →* H))
    (φ₁ := (φ₁ : A →* H₁)) (φ₂ := (φ₂ : A →* H₂))
    hφ₁ hφ₂ hcomp'

/-- Surjectivity of the continuous pullback lift is equivalent to the required kernel equality. -/
theorem pullbackLiftCont_surjective_iff_ker_eq
    [Group A] [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace A] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    {β₁ : H₁ →ₜ* H} (β₂ : H₂ →ₜ* H)
    {φ₁ : A →ₜ* H₁} {φ₂ : A →ₜ* H₂}
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂) :
    Function.Surjective (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂
        (fun a => DFunLike.congr_fun hcomp a)) ↔
      ((β₁.comp φ₁ : A →ₜ* H).toMonoidHom).ker =
        ((φ₁ : A →ₜ* H₁).toMonoidHom).ker ⊔
          ((φ₂ : A →ₜ* H₂).toMonoidHom).ker := by
  have hcomp' :
      ((β₁ : H₁ →* H).comp (φ₁ : A →* H₁)) =
        ((β₂ : H₂ →* H).comp (φ₂ : A →* H₂)) := by
    ext a
    exact DFunLike.congr_fun hcomp a
  change
    Function.Surjective
        (FiberProduct.lift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
          (φ₁ : A →* H₁) (φ₂ : A →* H₂) _) ↔
      ((β₁ : H₁ →* H).comp (φ₁ : A →* H₁)).ker =
        (φ₁ : A →* H₁).ker ⊔ (φ₂ : A →* H₂).ker
  exact pullbackLift_surjective_iff_ker_eq
    (β₁ := (β₁ : H₁ →* H)) (β₂ := (β₂ : H₂ →* H))
    (φ₁ := (φ₁ : A →* H₁)) (φ₂ := (φ₂ : A →* H₂))
    hφ₁ hφ₂ hcomp'

/-- Surjective continuous coordinate maps whose underlying composite kernel is the supremum of
their kernels induce a surjective continuous map into the fiber product. -/
theorem surjective_pullbackLiftCont_of_ker_eq
    [Group A] [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace A] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : A →ₜ* H₁) (φ₂ : A →ₜ* H₂)
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂)
    (hker : ((β₁.comp φ₁ : A →ₜ* H).toMonoidHom).ker =
      ((φ₁ : A →ₜ* H₁).toMonoidHom).ker ⊔ ((φ₂ : A →ₜ* H₂).toMonoidHom).ker) :
    Function.Surjective (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => by
      exact DFunLike.congr_fun hcomp a)) := by
  exact (pullbackLiftCont_surjective_iff_ker_eq
    (β₁ := β₁) (β₂ := β₂) (φ₁ := φ₁) (φ₂ := φ₂) hφ₁ hφ₂ hcomp).2 hker

/--
The continuous pullback lift is bijective when the left map is injective and the required kernel
equality holds.
-/
theorem bijective_pullbackLiftCont_of_left_injective_of_ker_eq
    [Group A] [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace A] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : A →ₜ* H₁) (φ₂ : A →ₜ* H₂)
    (hφ₁surj : Function.Surjective φ₁) (hφ₂surj : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂)
    (hker : ((β₁.comp φ₁ : A →ₜ* H).toMonoidHom).ker =
      ((φ₁ : A →ₜ* H₁).toMonoidHom).ker ⊔ ((φ₂ : A →ₜ* H₂).toMonoidHom).ker)
    (hφ₁inj : Function.Injective φ₁) :
    Function.Bijective (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => by
      exact DFunLike.congr_fun hcomp a)) := by
  refine ⟨?_, ?_⟩
  · exact pullbackLiftCont_injective_of_left_injective β₁ β₂ φ₁ φ₂
      (fun a => DFunLike.congr_fun hcomp a) hφ₁inj
  · exact surjective_pullbackLiftCont_of_ker_eq β₁ β₂ φ₁ φ₂
      hφ₁surj hφ₂surj hcomp hker

/--
The continuous pullback lift is bijective when the right map is injective and the required
kernel equality holds.
-/
theorem bijective_pullbackLiftCont_of_right_injective_of_ker_eq
    [Group A] [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace A] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : A →ₜ* H₁) (φ₂ : A →ₜ* H₂)
    (hφ₁surj : Function.Surjective φ₁) (hφ₂surj : Function.Surjective φ₂)
    (hcomp : β₁.comp φ₁ = β₂.comp φ₂)
    (hker : ((β₁.comp φ₁ : A →ₜ* H).toMonoidHom).ker =
      ((φ₁ : A →ₜ* H₁).toMonoidHom).ker ⊔ ((φ₂ : A →ₜ* H₂).toMonoidHom).ker)
    (hφ₂inj : Function.Injective φ₂) :
    Function.Bijective (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ (fun a => by
      exact DFunLike.congr_fun hcomp a)) := by
  refine ⟨?_, ?_⟩
  · exact pullbackLiftCont_injective_of_right_injective β₁ β₂ φ₁ φ₂
      (fun a => DFunLike.congr_fun hcomp a) hφ₂inj
  · exact surjective_pullbackLiftCont_of_ker_eq β₁ β₂ φ₁ φ₂
      hφ₁surj hφ₂surj hcomp hker

namespace TopologicalFiberProduct

/-- Composing the first projection with a topological fiber-product lift gives the left map. -/
@[simp] theorem fst_lift
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (fst β₁ β₂).comp (lift β₁ β₂ φ₁ φ₂ h) = φ₁ :=
  pullbackFstCont_pullbackLiftCont β₁ β₂ φ₁ φ₂ h

/-- Composing the second projection with a topological fiber-product lift gives the right map. -/
@[simp] theorem snd_lift
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (snd β₁ β₂).comp (lift β₁ β₂ φ₁ φ₂ h) = φ₂ :=
  pullbackSndCont_pullbackLiftCont β₁ β₂ φ₁ φ₂ h

/-- The first projection of a lifted element is the value of the first coordinate map. -/
@[simp] theorem fst_lift_apply
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) (k : K) :
    fst β₁ β₂ (lift β₁ β₂ φ₁ φ₂ h k) = φ₁ k :=
  rfl

/-- The second projection of a lifted element is the value of the second coordinate map. -/
@[simp] theorem snd_lift_apply
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) (k : K) :
    snd β₁ β₂ (lift β₁ β₂ φ₁ φ₂ h k) = φ₂ k :=
  rfl

end TopologicalFiberProduct

end



end ProCGroups.Categorical
