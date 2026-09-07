import ProCGroups.Categorical.ProfinitePullbacks
import ProCGroups.ProC.Quotients.ClosedNormal

set_option autoImplicit false

/-!
# Pro C Groups / Categorical / Quotient Pullback Equivalences

This module identifies the quotient by an intersection with the concrete
fiber product of the two quotient maps to the quotient by their supremum, in
both the algebraic and continuous settings.
-/

namespace ProCGroups

namespace Subgroup

/-- An infimum of normal subgroups is normal. -/
instance normal_iInf
    {ι : Type*} {G : Type*} [Group G] (W : ι → Subgroup G)
    [∀ i, (W i).Normal] :
    (⨅ i, W i).Normal where
  conj_mem := by
    intro n hn g
    rw [Subgroup.mem_iInf] at hn ⊢
    intro i
    exact (show (W i).Normal by infer_instance).conj_mem n (hn i) g

/--
In a Hausdorff topological group, the join of a compact subgroup with a compact normal subgroup
is closed.
-/
theorem isClosed_sup_of_isCompact_of_normal_right
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [T2Space G]
    (U V : Subgroup G) [V.Normal]
    (hU : IsCompact (U : Set G)) (hV : IsCompact (V : Set G)) :
    IsClosed ((U ⊔ V : Subgroup G) : Set G) := by
  have hmul : Continuous (fun p : G × G => p.1 * p.2) :=
    continuous_fst.mul continuous_snd
  have hcompact :
      IsCompact ((fun p : G × G => p.1 * p.2) '' ((U : Set G) ×ˢ (V : Set G))) :=
    (hU.prod hV).image hmul
  have hsup_eq_image :
      ((U ⊔ V : Subgroup G) : Set G) =
        (fun p : G × G => p.1 * p.2) '' ((U : Set G) ×ˢ (V : Set G)) := by
    ext g
    constructor
    · intro hg
      rcases (Subgroup.mem_sup_of_normal_right (s := U) (t := V)).1 hg with
        ⟨u, hu, v, hv, huv⟩
      exact ⟨(u, v), ⟨hu, hv⟩, by simp only [huv]⟩
    · rintro ⟨p, hp, rfl⟩
      exact (U ⊔ V).mul_mem
        ((le_sup_left : U ≤ U ⊔ V) hp.1)
        ((le_sup_right : V ≤ U ⊔ V) hp.2)
  simpa [hsup_eq_image] using hcompact.isClosed

/--
In a compact Hausdorff topological group, the join of a closed subgroup with a closed normal
subgroup is closed.
-/
theorem isClosed_sup_of_normal
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G]
    (U V : Subgroup G) [V.Normal]
    (hUclosed : IsClosed (U : Set G)) (hVclosed : IsClosed (V : Set G)) :
    IsClosed ((U ⊔ V : Subgroup G) : Set G) :=
  isClosed_sup_of_isCompact_of_normal_right U V hUclosed.isCompact hVclosed.isCompact

end Subgroup

end ProCGroups

namespace ProCGroups.Categorical

universe u v

variable {G : Type u} [Group G]
variable (U V : Subgroup G) [U.Normal] [V.Normal]

/-- The quotient map induced by an inclusion of normal subgroups. -/
def quotientMapOfLE (M N : Subgroup G) [M.Normal] [N.Normal] (hMN : M ≤ N) :
    G ⧸ M →* G ⧸ N :=
  QuotientGroup.map M N (MonoidHom.id G) (by
    intro g hg
    exact hMN hg)

/-- The quotient map induced by an inclusion sends a coset to its image coset. -/
@[simp] theorem quotientMapOfLE_mk (M N : Subgroup G) [M.Normal] [N.Normal]
    (hMN : M ≤ N) (g : G) :
    quotientMapOfLE (G := G) M N hMN (QuotientGroup.mk g) = QuotientGroup.mk g :=
  by
    have hcomap : M ≤ Subgroup.comap (MonoidHom.id G) N := by
      intro x hx
      exact hMN hx
    exact QuotientGroup.map_mk' (N := M) N (MonoidHom.id G) hcomap g

/-- Coordinate map from the quotient by an indexed intersection of normal subgroups. -/
def quotientIInfToCoordinate {ι : Type v} (W : ι → Subgroup G) [∀ i, (W i).Normal]
    (i : ι) :
    G ⧸ (⨅ j, W j) →* G ⧸ W i :=
  quotientMapOfLE (G := G) (⨅ j, W j) (W i) (iInf_le W i)

/--
The map from the quotient by the infimum to a coordinate quotient sends a representative to its
coordinate coset.
-/
@[simp] theorem quotientIInfToCoordinate_mk {ι : Type v}
    (W : ι → Subgroup G) [∀ i, (W i).Normal] (i : ι) (g : G) :
    quotientIInfToCoordinate (G := G) W i (QuotientGroup.mk' (⨅ j, W j) g) =
      QuotientGroup.mk' (W i) g := by
  simp only [quotientIInfToCoordinate, QuotientGroup.mk'_apply, quotientMapOfLE_mk]

/--
Quotient classes modulo an indexed intersection are equal when all coordinate quotients are
equal.
-/
theorem quotient_iInf_isLimit {ι : Type v}
    (W : ι → Subgroup G) [∀ i, (W i).Normal]
    {x y : G ⧸ (⨅ i, W i)}
    (hxy : ∀ i, quotientIInfToCoordinate (G := G) W i x =
      quotientIInfToCoordinate (G := G) W i y) :
    x = y := by
  rcases QuotientGroup.mk'_surjective (⨅ i, W i) x with ⟨gx, rfl⟩
  rcases QuotientGroup.mk'_surjective (⨅ i, W i) y with ⟨gy, rfl⟩
  apply QuotientGroup.eq.2
  rw [Subgroup.mem_iInf]
  intro i
  have hi := hxy i
  simpa [quotientIInfToCoordinate] using (QuotientGroup.eq.1 hi)


/--
Kernel of the quotient map induced by M \(\le\) N, after precomposition with the quotient map
from \(G\).
-/
@[simp] theorem ker_quotientMapOfLE_comp_mk (M N : Subgroup G) [M.Normal] [N.Normal]
    (hMN : M ≤ N) :
    ((quotientMapOfLE (G := G) M N hMN).comp (QuotientGroup.mk' M)).ker = N := by
  ext g
  change quotientMapOfLE (G := G) M N hMN (QuotientGroup.mk g) = 1 ↔ g ∈ N
  rw [quotientMapOfLE_mk (G := G) M N hMN g]
  exact QuotientGroup.eq_one_iff (N := N) g

/-- The left-hand map in the quotient pullback square. -/
def quotientInfToLeft : G ⧸ (U ⊓ V) →* G ⧸ U :=
  quotientMapOfLE (G := G) (U ⊓ V) U inf_le_left

/-- The right-hand map in the quotient pullback square. -/
def quotientInfToRight : G ⧸ (U ⊓ V) →* G ⧸ V :=
  quotientMapOfLE (G := G) (U ⊓ V) V inf_le_right

/-- The bottom-left map in the quotient pullback square. -/
def quotientToSupLeft : G ⧸ U →* G ⧸ (U ⊔ V) :=
  quotientMapOfLE (G := G) U (U ⊔ V) le_sup_left

/-- The bottom-right map in the quotient pullback square. -/
def quotientToSupRight : G ⧸ V →* G ⧸ (U ⊔ V) :=
  quotientMapOfLE (G := G) V (U ⊔ V) le_sup_right

/-- Kernel of the left quotient-to-sup map after precomposition with the quotient map from \(G\). -/
@[simp] theorem ker_quotientToSupLeft_comp_mk :
    ((quotientToSupLeft (G := G) U V).comp (QuotientGroup.mk' U)).ker = U ⊔ V := by
  simp only [quotientToSupLeft, ker_quotientMapOfLE_comp_mk]

/--
This lemma identifies the kernel of the right quotient-to-sup map after precomposition with the
quotient map from \(G\).
-/
@[simp] theorem ker_quotientToSupRight_comp_mk :
    ((quotientToSupRight (G := G) U V).comp (QuotientGroup.mk' V)).ker = U ⊔ V := by
  simp only [quotientToSupRight, ker_quotientMapOfLE_comp_mk]

/-- The quotient map induced by an inclusion of normal subgroups is viewed as continuous. -/
def quotientMapOfLECont
    {G : Type u} [Group G] [TopologicalSpace G]
    (M N : Subgroup G) [M.Normal] [N.Normal] (hMN : M ≤ N) :
    G ⧸ M →ₜ* G ⧸ N :=
  QuotientGroup.mapₜ M N (ContinuousMonoidHom.id G) (by
    intro g hg
    exact hMN hg)

/--
The quotient map sends the class of an element to the class of its image under the underlying
group homomorphism.
-/
@[simp] theorem quotientMapOfLECont_toMonoidHom
    {G : Type u} [Group G] [TopologicalSpace G]
    (M N : Subgroup G) [M.Normal] [N.Normal] (hMN : M ≤ N) :
    (quotientMapOfLECont (G := G) M N hMN).toMonoidHom =
      quotientMapOfLE (G := G) M N hMN :=
  by
    exact QuotientGroup.mapₜ_toMonoidHom M N (ContinuousMonoidHom.id G) (by
      intro g hg
      exact hMN hg)

/-- Evaluation of the continuous quotient map induced by inclusion on a quotient class. -/
@[simp] theorem quotientMapOfLECont_mk
    {G : Type u} [Group G] [TopologicalSpace G]
    (M N : Subgroup G) [M.Normal] [N.Normal] (hMN : M ≤ N) (g : G) :
    quotientMapOfLECont (G := G) M N hMN (QuotientGroup.mk g) = QuotientGroup.mk g := by
  change quotientMapOfLECont (G := G) M N hMN (QuotientGroup.mk' M g) =
    QuotientGroup.mk' N g
  simpa [quotientMapOfLECont] using
    (QuotientGroup.mapₜ_apply_mk
      (N := M) (M := N) (f := ContinuousMonoidHom.id G)
      (hNM := by
        intro g hg
        exact hMN hg) g)

/--
The canonical map from \(G/(U \cap V)\) to the concrete pullback of \(G/U\) and \(G/V\) over
\(G/(UV)\).
-/
noncomputable def quotientInfToPullback :
    G ⧸ (U ⊓ V) →*
      FiberProduct.carrier (quotientToSupLeft (G := G) U V) (quotientToSupRight (G := G) U V) := by
  refine FiberProduct.lift
    (quotientToSupLeft (G := G) U V)
    (quotientToSupRight (G := G) U V)
    (quotientInfToLeft (G := G) U V)
    (quotientInfToRight (G := G) U V) ?_
  intro x
  refine Quotient.inductionOn x ?_
  intro g
  rfl

/-- The quotient-to-pullback map sends a coset to the corresponding pair of quotient cosets. -/
@[simp] theorem quotientInfToPullback_mk (g : G) :
    quotientInfToPullback (G := G) U V (QuotientGroup.mk g) =
      ⟨(QuotientGroup.mk g, QuotientGroup.mk g), rfl⟩ := by
  rfl

/-- The first projection of the quotient-to-pullback map is the natural quotient map to \(G/U\). -/
@[simp] theorem pullbackFst_quotientInfToPullback :
    (FiberProduct.fst _ _).comp
        (quotientInfToPullback (G := G) U V) =
      quotientInfToLeft (G := G) U V := by
  apply MonoidHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro g
  rfl

/-- The second projection of the quotient-to-pullback map is the natural quotient map to \(G/V\). -/
@[simp] theorem pullbackSnd_quotientInfToPullback :
    (FiberProduct.snd _ _).comp
        (quotientInfToPullback (G := G) U V) =
      quotientInfToRight (G := G) U V := by
  apply MonoidHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro g
  rfl

/--
The canonical map from \(G/(U \cap V)\) to the pullback of \(G/U\) and \(G/V\) over \(G/(UV)\)
is injective.
-/
theorem quotientInfToPullback_injective :
    Function.Injective (quotientInfToPullback (G := G) U V) := by
  intro x y hxy
  revert hxy
  refine Quotient.inductionOn₂' x y ?_
  intro g h hEq
  apply QuotientGroup.eq.2
  have hU :
      QuotientGroup.mk' U g = QuotientGroup.mk' U h := by
    exact congrArg (fun z => z.1.1) hEq
  have hV :
      QuotientGroup.mk' V g = QuotientGroup.mk' V h := by
    exact congrArg (fun z => z.1.2) hEq
  exact ⟨QuotientGroup.eq.1 hU, QuotientGroup.eq.1 hV⟩

/--
The canonical map from the quotient by \(U \cap V\) to the pullback of the quotients by \(U\)
and \(V\) is surjective.
-/
theorem quotientInfToPullback_surjective :
    Function.Surjective (quotientInfToPullback (G := G) U V) := by
  intro x
  rcases QuotientGroup.mk'_surjective U x.1.1 with ⟨a, ha⟩
  rcases QuotientGroup.mk'_surjective V x.1.2 with ⟨b, hb⟩
  have hsup :
      QuotientGroup.mk' (U ⊔ V) a = QuotientGroup.mk' (U ⊔ V) b := by
    calc
      QuotientGroup.mk' (U ⊔ V) a =
          quotientToSupLeft (G := G) U V x.1.1 := by
            rw [← ha]
            rfl
      _ = quotientToSupRight (G := G) U V x.1.2 := x.2
      _ = QuotientGroup.mk' (U ⊔ V) b := by
            rw [← hb]
            rfl
  have hab : a⁻¹ * b ∈ U ⊔ V := QuotientGroup.eq.1 hsup
  rcases (Subgroup.mem_sup_of_normal_right (s := U) (t := V)).1 hab with
    ⟨u, hu, v, hv, huv⟩
  have hb_eq : b = (a * u) * v := by
    calc
      b = a * (a⁻¹ * b) := by simp only [mul_inv_cancel_left]
      _ = a * (u * v) := by rw [← huv]
      _ = (a * u) * v := by simp only [mul_assoc]
  have hU : QuotientGroup.mk' U (a * u) = QuotientGroup.mk' U a := by
    symm
    apply QuotientGroup.eq.2
    have hmem : a⁻¹ * (a * u) = u := by simp only [inv_mul_cancel_left]
    simpa [hmem] using hu
  have hV : QuotientGroup.mk' V (a * u) = QuotientGroup.mk' V b := by
    apply QuotientGroup.eq.2
    have hmem : (a * u)⁻¹ * b = v := by
      calc
        (a * u)⁻¹ * b = (a * u)⁻¹ * ((a * u) * v) := by rw [hb_eq]
        _ = v := by simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    rw [hmem]
    exact hv
  refine ⟨QuotientGroup.mk' (U ⊓ V) (a * u), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · calc
      (quotientInfToPullback (G := G) U V
          (QuotientGroup.mk' (U ⊓ V) (a * u))).1.1 =
          QuotientGroup.mk' U (a * u) := rfl
      _ = QuotientGroup.mk' U a := hU
      _ = x.1.1 := ha
  · calc
      (quotientInfToPullback (G := G) U V
          (QuotientGroup.mk' (U ⊓ V) (a * u))).1.2 =
          QuotientGroup.mk' V (a * u) := rfl
      _ = QuotientGroup.mk' V b := hV
      _ = x.1.2 := hb

/-- The canonical quotient-to-pullback map is bijective. -/
theorem quotientInfToPullback_bijective :
    Function.Bijective (quotientInfToPullback (G := G) U V) := by
  exact ⟨quotientInfToPullback_injective (G := G) U V,
    quotientInfToPullback_surjective (G := G) U V⟩

/-- The quotient square is canonically isomorphic to the pullback. -/
noncomputable def quotientInfPullbackEquiv :
    G ⧸ (U ⊓ V) ≃*
      FiberProduct.carrier (quotientToSupLeft (G := G) U V) (quotientToSupRight (G := G) U V) :=
  MulEquiv.ofBijective (quotientInfToPullback (G := G) U V)
    (quotientInfToPullback_bijective (G := G) U V)

/-- The first coordinate of the quotient pullback equivalence is the natural map to \(G/U\). -/
@[simp] theorem quotientInfPullbackEquiv_fst :
    (FiberProduct.fst _ _).comp (quotientInfPullbackEquiv (G := G) U V).toMonoidHom =
      quotientInfToLeft (G := G) U V := by
  change (FiberProduct.fst _ _).comp (quotientInfToPullback (G := G) U V) =
      quotientInfToLeft (G := G) U V
  exact pullbackFst_quotientInfToPullback (G := G) U V

/-- The second coordinate of the quotient pullback equivalence is the natural map to \(G/V\). -/
@[simp] theorem quotientInfPullbackEquiv_snd :
    (FiberProduct.snd _ _).comp (quotientInfPullbackEquiv (G := G) U V).toMonoidHom =
      quotientInfToRight (G := G) U V := by
  change (FiberProduct.snd _ _).comp (quotientInfToPullback (G := G) U V) =
      quotientInfToRight (G := G) U V
  exact pullbackSnd_quotientInfToPullback (G := G) U V

/-- The quotient square is a pullback square. -/
theorem quotientInf_isPullback :
    CategoryTheory.IsPullback
      (GrpCat.ofHom (quotientInfToLeft (G := G) U V))
      (GrpCat.ofHom (quotientInfToRight (G := G) U V))
      (GrpCat.ofHom (quotientToSupLeft (G := G) U V))
      (GrpCat.ofHom (quotientToSupRight (G := G) U V)) := by
  apply
    (FiberProduct.isPullback
      (quotientToSupLeft (G := G) U V)
      (quotientToSupRight (G := G) U V)).of_iso'
      (quotientInfPullbackEquiv (G := G) U V).toGrpIso
      (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)
      (CategoryTheory.Iso.refl _)
  · apply GrpCat.hom_ext
    exact quotientInfPullbackEquiv_fst (G := G) U V
  · apply GrpCat.hom_ext
    exact quotientInfPullbackEquiv_snd (G := G) U V
  · simp
  · simp

section

variable [TopologicalSpace G]

/-- The left map in the continuous quotient square. -/
def quotientInfToLeftCont : G ⧸ (U ⊓ V) →ₜ* G ⧸ U :=
  quotientMapOfLECont (G := G) (U ⊓ V) U inf_le_left

/-- The right map in the continuous quotient square. -/
def quotientInfToRightCont : G ⧸ (U ⊓ V) →ₜ* G ⧸ V :=
  quotientMapOfLECont (G := G) (U ⊓ V) V inf_le_right

/-- The bottom-left map in the continuous quotient square. -/
def quotientToSupLeftCont : G ⧸ U →ₜ* G ⧸ (U ⊔ V) :=
  quotientMapOfLECont (G := G) U (U ⊔ V) le_sup_left

/-- The bottom-right map in the continuous quotient square. -/
def quotientToSupRightCont : G ⧸ V →ₜ* G ⧸ (U ⊔ V) :=
  quotientMapOfLECont (G := G) V (U ⊔ V) le_sup_right

/--
Forgetting continuity from the left continuous quotient-square map recovers the algebraic map.
-/
@[simp] theorem quotientInfToLeftCont_toMonoidHom :
    (quotientInfToLeftCont (G := G) U V).toMonoidHom = quotientInfToLeft (G := G) U V :=
  rfl

/-- Forgetting continuity from the right continuous quotient-square map recovers the
algebraic map. -/
@[simp] theorem quotientInfToRightCont_toMonoidHom :
    (quotientInfToRightCont (G := G) U V).toMonoidHom = quotientInfToRight (G := G) U V :=
  rfl

/--
Forgetting continuity from the lower-left continuous quotient-square map recovers the algebraic
map.
-/
@[simp] theorem quotientToSupLeftCont_toMonoidHom :
    (quotientToSupLeftCont (G := G) U V).toMonoidHom = quotientToSupLeft (G := G) U V :=
  rfl

/--
Forgetting continuity from the lower-right continuous quotient-square map recovers the algebraic
map.
-/
@[simp] theorem quotientToSupRightCont_toMonoidHom :
    (quotientToSupRightCont (G := G) U V).toMonoidHom = quotientToSupRight (G := G) U V :=
  rfl

/-- Evaluation of the left continuous quotient-square map on a quotient class. -/
@[simp] theorem quotientInfToLeftCont_mk (g : G) :
    quotientInfToLeftCont (G := G) U V (QuotientGroup.mk g) = QuotientGroup.mk g := by
  simp only [quotientInfToLeftCont, quotientMapOfLECont_mk]

/-- Evaluation of the right continuous quotient-square map on a quotient class. -/
@[simp] theorem quotientInfToRightCont_mk (g : G) :
    quotientInfToRightCont (G := G) U V (QuotientGroup.mk g) = QuotientGroup.mk g := by
  simp only [quotientInfToRightCont, quotientMapOfLECont_mk]

/-- Evaluation of the lower-left continuous quotient-square map on a quotient class. -/
@[simp] theorem quotientToSupLeftCont_mk (g : G) :
    quotientToSupLeftCont (G := G) U V (QuotientGroup.mk g) = QuotientGroup.mk g := by
  simp only [quotientToSupLeftCont, quotientMapOfLECont_mk]

/-- Evaluation of the lower-right continuous quotient-square map on a quotient class. -/
@[simp] theorem quotientToSupRightCont_mk (g : G) :
    quotientToSupRightCont (G := G) U V (QuotientGroup.mk g) = QuotientGroup.mk g := by
  simp only [quotientToSupRightCont, quotientMapOfLECont_mk]

variable [IsTopologicalGroup G]

/--
The canonical continuous map from \(G/(U \cap V)\) to the concrete continuous pullback of
\(G/U\) and \(G/V\) over \(G/(UV)\).
-/
def quotientInfToContinuousPullback :
    G ⧸ (U ⊓ V) →ₜ*
      TopologicalFiberProduct.carrier (quotientToSupLeftCont (G := G) U V)
          (quotientToSupRightCont (G := G) U V) := by
  refine TopologicalFiberProduct.lift
    (quotientToSupLeftCont (G := G) U V)
    (quotientToSupRightCont (G := G) U V)
    (quotientInfToLeftCont (G := G) U V)
    (quotientInfToRightCont (G := G) U V) ?_
  intro x
  refine Quotient.inductionOn x ?_
  intro g
  rfl

omit [IsTopologicalGroup G] in
/--
Forgetting continuity from the continuous quotient-to-pullback map recovers the algebraic one.
-/
@[simp] theorem quotientInfToContinuousPullback_toMonoidHom :
    (quotientInfToContinuousPullback (G := G) U V).toMonoidHom =
      quotientInfToPullback (G := G) U V := by
  apply MonoidHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro g
  exact Subtype.ext <| Prod.ext rfl rfl

omit [IsTopologicalGroup G] in
/-- Evaluation formula for the continuous quotient-to-pullback map. -/
@[simp] theorem quotientInfToContinuousPullback_mk (g : G) :
    quotientInfToContinuousPullback (G := G) U V (QuotientGroup.mk g) =
      ⟨(QuotientGroup.mk g, QuotientGroup.mk g), rfl⟩ := by
  rfl

omit [IsTopologicalGroup G] in
/-- The first projection of the continuous quotient-to-pullback map is the natural quotient map to
`G/U`. -/
@[simp] theorem pullbackFstCont_quotientInfToContinuousPullback :
    (TopologicalFiberProduct.fst _ _).comp (quotientInfToContinuousPullback (G := G) U V) =
      quotientInfToLeftCont (G := G) U V := by
  apply ContinuousMonoidHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro g
  rfl

omit [IsTopologicalGroup G] in
/-- The second projection of the continuous quotient-to-pullback map is the natural quotient map to
`G/V`. -/
@[simp] theorem pullbackSndCont_quotientInfToContinuousPullback :
    (TopologicalFiberProduct.snd _ _).comp (quotientInfToContinuousPullback (G := G) U V) =
      quotientInfToRightCont (G := G) U V := by
  apply ContinuousMonoidHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro g
  rfl

omit [IsTopologicalGroup G] in
/-- Injectivity of the continuous quotient-to-pullback map on the underlying groups. -/
theorem quotientInfToContinuousPullback_injective :
    Function.Injective (quotientInfToContinuousPullback (G := G) U V) := by
  intro x y hxy
  apply quotientInfToPullback_injective (G := G) U V
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z => z.1.1) hxy
  · exact congrArg (fun z => z.1.2) hxy

omit [IsTopologicalGroup G] in
/-- Surjectivity of the continuous quotient-to-pullback map on the underlying groups. -/
theorem quotientInfToContinuousPullback_surjective :
    Function.Surjective (quotientInfToContinuousPullback (G := G) U V) := by
  intro x
  rcases quotientInfToPullback_surjective (G := G) U V x with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z => z.1.1) hy
  · exact congrArg (fun z => z.1.2) hy

omit [IsTopologicalGroup G] in
/-- The continuous quotient-to-pullback map is bijective on the underlying groups. -/
theorem quotientInfToContinuousPullback_bijective :
    Function.Bijective (quotientInfToContinuousPullback (G := G) U V) := by
  exact ⟨quotientInfToContinuousPullback_injective (G := G) U V,
    quotientInfToContinuousPullback_surjective (G := G) U V⟩

/-- The quotient square is canonically isomorphic to the concrete continuous fiber product. -/
noncomputable def quotientInfContinuousPullbackEquiv
    [CompactSpace G] [T2Space G]
    (hUclosed : IsClosed (U : Set G)) (hVclosed : IsClosed (V : Set G)) :
    G ⧸ (U ⊓ V) ≃ₜ*
      TopologicalFiberProduct.carrier (quotientToSupLeftCont (G := G) U V)
          (quotientToSupRightCont (G := G) U V) := by
  exact ContinuousMulEquiv.ofBijectiveCompactToT2
    (quotientInfToContinuousPullback (G := G) U V)
    (quotientInfToContinuousPullback (G := G) U V).continuous_toFun
    (quotientInfToContinuousPullback_bijective (G := G) U V)

/-- The quotient pullback equivalence is induced by the canonical comparison map. -/
@[simp] theorem quotientInfContinuousPullbackEquiv_toContinuousMonoidHom
    [CompactSpace G] [T2Space G]
    (hUclosed : IsClosed (U : Set G)) (hVclosed : IsClosed (V : Set G)) :
    ContinuousMonoidHom.toContinuousMonoidHom (quotientInfContinuousPullbackEquiv
        (G := G) (U := U) (V := V) hUclosed hVclosed) =
      quotientInfToContinuousPullback (G := G) U V := by
  apply ContinuousMonoidHom.ext
  intro x
  exact Subtype.ext <| Prod.ext rfl rfl

/-- Evaluation formula for the continuous quotient pullback equivalence on a quotient class.
-/
@[simp] theorem quotientInfContinuousPullbackEquiv_mk
    [CompactSpace G] [T2Space G]
    (hUclosed : IsClosed (U : Set G)) (hVclosed : IsClosed (V : Set G)) (g : G) :
    quotientInfContinuousPullbackEquiv (G := G) (U := U) (V := V) hUclosed hVclosed
      (QuotientGroup.mk g) = ⟨(QuotientGroup.mk g, QuotientGroup.mk g), rfl⟩ := by
  change quotientInfToContinuousPullback (G := G) U V (QuotientGroup.mk g) = _
  exact quotientInfToContinuousPullback_mk (G := G) U V g

/--
The first coordinate of the continuous quotient pullback equivalence is the natural map to `G/U`.
-/
@[simp] theorem quotientInfContinuousPullbackEquiv_fst
    [CompactSpace G] [T2Space G]
    (hUclosed : IsClosed (U : Set G)) (hVclosed : IsClosed (V : Set G)) :
    (TopologicalFiberProduct.fst _ _).comp
        (ContinuousMonoidHom.toContinuousMonoidHom (quotientInfContinuousPullbackEquiv
          (G := G) (U := U) (V := V) hUclosed hVclosed)) =
      quotientInfToLeftCont (G := G) U V := by
  rw [quotientInfContinuousPullbackEquiv_toContinuousMonoidHom
    (G := G) (U := U) (V := V) hUclosed hVclosed]
  exact pullbackFstCont_quotientInfToContinuousPullback (G := G) U V

/--
The second coordinate of the continuous quotient pullback equivalence is the natural map to `G/V`.
-/
@[simp] theorem quotientInfContinuousPullbackEquiv_snd
    [CompactSpace G] [T2Space G]
    (hUclosed : IsClosed (U : Set G)) (hVclosed : IsClosed (V : Set G)) :
    (TopologicalFiberProduct.snd _ _).comp
        (ContinuousMonoidHom.toContinuousMonoidHom (quotientInfContinuousPullbackEquiv
          (G := G) (U := U) (V := V) hUclosed hVclosed)) =
      quotientInfToRightCont (G := G) U V := by
  rw [quotientInfContinuousPullbackEquiv_toContinuousMonoidHom
    (G := G) (U := U) (V := V) hUclosed hVclosed]
  exact pullbackSndCont_quotientInfToContinuousPullback (G := G) U V

/-- For closed normal subgroups of a compact Hausdorff topological group, the quotient square
has the universal
property when tested against profinite source groups. -/
theorem quotientInf_hasProfiniteTestPullbackProperty
    [CompactSpace G] [T2Space G]
    (hUclosed : IsClosed (U : Set G)) (hVclosed : IsClosed (V : Set G)) :
    HasProfiniteTestPullbackProperty
      (quotientInfToLeftCont (G := G) U V)
      (quotientInfToRightCont (G := G) U V)
      (quotientToSupLeftCont (G := G) U V)
      (quotientToSupRightCont (G := G) U V) := by
  exact hasProfiniteTestPullbackProperty_of_equiv_toConcretePullback
    (quotientInfToLeftCont (G := G) U V)
    (quotientInfToRightCont (G := G) U V)
    (quotientToSupLeftCont (G := G) U V)
    (quotientToSupRightCont (G := G) U V)
    (quotientInfContinuousPullbackEquiv (G := G) (U := U) (V := V) hUclosed hVclosed)
    (quotientInfContinuousPullbackEquiv_fst (G := G) (U := U) (V := V) hUclosed hVclosed)
    (quotientInfContinuousPullbackEquiv_snd (G := G) (U := U) (V := V) hUclosed hVclosed)

end
end ProCGroups.Categorical
