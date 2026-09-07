import ProCGroups.InverseSystems.CofinalityAndDensity

set_option autoImplicit false

/-!
# Inverse systems formed from projection images

A subset of an inverse limit determines an inverse system of its stagewise projection images.
This module constructs the comparison lift, proves reconstruction for closed subsets of compact
Hausdorff systems, and derives closure and equality criteria from stagewise images.  It also
handles systems whose transition maps are surjective by identifying their projection images.
-/

open Set
open scoped Topology

namespace ProCGroups.InverseSystems

universe u v w

/-- The inverse system formed by the projection images of a subset of an inverse limit. -/
def InverseSystem.projectionImageSystem {I : Type u} [Preorder I]
    (S : InverseSystem (I := I)) (Y : Set S.inverseLimit) :
    InverseSystem (I := I) where
  X := fun i => S.projection i '' Y
  topologicalSpace := fun _ => inferInstance
  map := fun {i j} hij x => ⟨S.map hij x.1, by
    rcases x.2 with ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    exact (S.projection_compatible y i j hij).symm.trans (congrArg (S.map hij) hxy)⟩
  continuous_map := fun {i j} hij =>
    Continuous.subtype_mk
      ((S.continuous_map hij).comp continuous_subtype_val) (fun x => by
        rcases x.2 with ⟨y, hy, hxy⟩
        refine ⟨y, hy, ?_⟩
        exact (S.projection_compatible y i j hij).symm.trans (congrArg (S.map hij) hxy))
  map_id := fun i => by
    funext x
    apply Subtype.ext
    change S.map (le_rfl : i ≤ i) x.val = x.val
    exact S.map_id_apply i x.val
  map_comp := fun {i j k} hij hjk => by
    funext x
    apply Subtype.ext
    change S.map hij (S.map hjk x.val) = S.map (hij.trans hjk) x.val
    exact S.map_comp_apply hij hjk x.val

/-- The canonical morphism from the projection-image system into the ambient inverse system. -/
def projectionImageInclusion {I : Type u} [Preorder I]
    (S : InverseSystem (I := I)) (Y : Set S.inverseLimit) :
    (S.projectionImageSystem Y).Morphism S where
  map := fun _ => Subtype.val
  continuous_map := fun _ => continuous_subtype_val
  comm := fun {i j} hij => by
    funext x
    rfl

/--
The coordinatewise section map from a subset of an inverse limit to its projection-image system.
-/
def projectionImageSectionMap {I : Type u} [Preorder I]
    (S : InverseSystem (I := I)) (Y : Set S.inverseLimit) (i : I) :
    Y → (S.projectionImageSystem Y).X i :=
  fun y => ⟨S.projection i y.1, ⟨y.1, y.2, rfl⟩⟩

/--
The section map from the projection-image inverse limit back to the closed subspace is
continuous.
-/
theorem continuous_projectionImageSectionMap {I : Type u} [Preorder I]
    (S : InverseSystem (I := I)) (Y : Set S.inverseLimit) (i : I) :
    Continuous (projectionImageSectionMap S Y i) := by
  exact Continuous.subtype_mk ((S.continuous_projection i).comp continuous_subtype_val)
    (fun y => ⟨y.1, y.2, rfl⟩)

/-- The projection-image section maps are compatible with the inverse-system transition maps. -/
theorem compatible_projectionImageSectionMap {I : Type u} [Preorder I]
    (S : InverseSystem (I := I)) (Y : Set S.inverseLimit) :
    (S.projectionImageSystem Y).CompatibleMaps (projectionImageSectionMap S Y) := by
  intro i j hij
  funext y
  apply Subtype.ext
  exact S.projection_compatible y.1 i j hij

/-- Each coordinate section map onto a projection image is surjective. -/
theorem surjective_projectionImageSectionMap {I : Type u} [Preorder I]
    (S : InverseSystem (I := I)) (Y : Set S.inverseLimit) (i : I) :
    Function.Surjective (projectionImageSectionMap S Y i) := by
  intro x
  rcases x.2 with ⟨y, hy, hxy⟩
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  change S.projection i y = x.1
  exact hxy

/--
The canonical lift from a subset of an inverse limit to the inverse limit of its
projection-image system.
-/
def projectionImageLift {I : Type u} [Preorder I]
    (S : InverseSystem (I := I)) (Y : Set S.inverseLimit) :
    Y → (S.projectionImageSystem Y).inverseLimit :=
  (S.projectionImageSystem Y).inverseLimitLift (projectionImageSectionMap S Y)
    (compatible_projectionImageSectionMap S Y)

/--
The lift from a closed subspace into the inverse limit of its projection images is continuous.
-/
theorem continuous_projectionImageLift {I : Type u} [Preorder I]
    (S : InverseSystem (I := I)) (Y : Set S.inverseLimit) :
    Continuous (projectionImageLift S Y) := by
  exact (S.projectionImageSystem Y).continuous_inverseLimitLift (projectionImageSectionMap S Y)
    (continuous_projectionImageSectionMap S Y) (compatible_projectionImageSectionMap S Y)

/--
For a closed subset of a compact Hausdorff inverse limit, the canonical projection-image lift is
surjective.
-/
theorem surjective_projectionImageLift {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystem (I := I)) [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) (Y : Set S.inverseLimit) (hY : IsClosed Y) :
    Function.Surjective (projectionImageLift S Y) := by
  let T : InverseSystem (I := I) := S.projectionImageSystem Y
  let : CompactSpace Y := hY.isClosedEmbedding_subtypeVal.compactSpace
  let : ∀ i, T2Space (T.X i) := fun i => by
    change T2Space (S.projection i '' Y)
    infer_instance
  exact T.surjective_inverseLimitLift (projectionImageSectionMap S Y)
      (continuous_projectionImageSectionMap S Y)
    (compatible_projectionImageSectionMap S Y) (surjective_projectionImageSectionMap S Y) hdir

/--
Composing the projection-image lift with the inclusion morphism recovers the underlying point of
the original inverse limit.
-/
theorem projectionImageLift_comp_subtype {I : Type u} [Preorder I]
    (S : InverseSystem (I := I)) (Y : Set S.inverseLimit) :
    (S.projectionImageSystem Y).limMap (projectionImageInclusion S Y) ∘
        projectionImageLift S Y = Subtype.val := by
  funext y
  apply S.ext
  intro i
  change S.projection i ((S.projectionImageSystem Y).limMap (projectionImageInclusion S Y)
    (projectionImageLift S Y y)) = S.projection i y.val
  rw [(S.projectionImageSystem Y).π_limMap_apply (projectionImageInclusion S Y) i
    (projectionImageLift S Y y)]
  change ((S.projectionImageSystem Y).projection i (projectionImageLift S Y y)).val =
    S.projection i y.val
  exact congrArg Subtype.val
    ((S.projectionImageSystem Y).projection_inverseLimitLift_apply
      (projectionImageSectionMap S Y) (compatible_projectionImageSectionMap S Y) i y)

/-- The transition maps in the projection-image system are always surjective. -/
theorem InverseSystem.surjective_projectionImageSystem_map
    {I : Type u} [Preorder I] (S : InverseSystem (I := I)) (Y : Set S.inverseLimit)
    {i j : I} (hij : i ≤ j) :
    Function.Surjective ((S.projectionImageSystem Y).map hij) := by
  intro x
  rcases x.2 with ⟨y, hy, hxy⟩
  refine ⟨⟨S.projection j y, ⟨y, hy, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change S.map hij (S.projection j y) = x.1
  rw [S.projection_compatible y i j hij]
  exact hxy

/--
A closed subset of an inverse limit is homeomorphic to the inverse limit of its projection-image
system.
-/
noncomputable def InverseSystem.homeomorph_projectionImageSystem_of_isClosed
    {I : Type u} [Preorder I] (S : InverseSystem (I := I)) [Nonempty I]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (Y : Set S.inverseLimit) (hY : IsClosed Y) :
    Y ≃ₜ (S.projectionImageSystem Y).inverseLimit := by
  classical
  letI : CompactSpace Y := hY.isClosedEmbedding_subtypeVal.compactSpace
  letI : ∀ i, T2Space ((S.projectionImageSystem Y).X i) := fun i => by
    change T2Space (S.projection i '' Y)
    infer_instance
  let e : Y → (S.projectionImageSystem Y).inverseLimit := projectionImageLift S Y
  have he_inj : Function.Injective e := by
    intro y y' hyy
    have hy : y.1 = y'.1 := by
      calc
        y.1 = (S.projectionImageSystem Y).limMap (projectionImageInclusion S Y) (e y) := by
          simpa [Function.comp] using (congrFun (projectionImageLift_comp_subtype S Y) y).symm
        _ = (S.projectionImageSystem Y).limMap (projectionImageInclusion S Y) (e y') := by
          rw [hyy]
        _ = y'.1 := by
          simpa [Function.comp] using congrFun (projectionImageLift_comp_subtype S Y) y'
    exact Subtype.ext hy
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective e
      ⟨he_inj, surjective_projectionImageLift S hdir Y hY⟩)
    (continuous_projectionImageLift S Y)

/-- The range of the limit map is exactly the compatible inverse limit of the projection images. -/
theorem range_limMap_projectionImageInclusion_eq
    {I : Type u} [Preorder I] (S : InverseSystem (I := I)) [Nonempty I]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (Y : Set S.inverseLimit) (hY : IsClosed Y) :
    Set.range ((S.projectionImageSystem Y).limMap (projectionImageInclusion S Y)) = Y := by
  classical
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    rcases surjective_projectionImageLift S hdir Y hY z with ⟨y, hy⟩
    have hx :
        (S.projectionImageSystem Y).limMap (projectionImageInclusion S Y) z = y.1 := by
      calc
        (S.projectionImageSystem Y).limMap (projectionImageInclusion S Y) z
            = (S.projectionImageSystem Y).limMap
                (projectionImageInclusion S Y) (projectionImageLift S Y y) := by
                  rw [hy]
        _ = y.1 := by
          simpa [Function.comp] using congrFun (projectionImageLift_comp_subtype S Y) y
    exact hx ▸ y.2
  · intro y hy
    refine ⟨projectionImageLift S Y ⟨y, hy⟩, ?_⟩
    simpa [Function.comp] using congrFun (projectionImageLift_comp_subtype S Y) ⟨y, hy⟩

/-- Membership in the projected image system can be checked coordinatewise. -/
theorem InverseSystem.mem_isClosed_iff_forall_projection_mem
    {I : Type u} [Preorder I] {S : InverseSystem (I := I)} [Nonempty I]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    {Y : Set S.inverseLimit} (hY : IsClosed Y) {x : S.inverseLimit} :
    x ∈ Y ↔ ∀ i, S.projection i x ∈ S.projection i '' Y := by
  classical
  constructor
  · intro hx i
    exact ⟨x, hx, rfl⟩
  · intro hx
    let T := S.projectionImageSystem Y
    let incl : T.Morphism S := projectionImageInclusion S Y
    have hcompat :
        T.CompatibleMaps (fun (i : I) (_ : Unit) => (⟨S.projection i x, hx i⟩ : T.X i)) := by
      intro i j hij
      funext _
      apply Subtype.ext
      exact S.projection_compatible x i j hij
    let z : T.inverseLimit :=
      T.inverseLimitLift (fun (i : I) (_ : Unit) => (⟨S.projection i x, hx i⟩ : T.X i)) hcompat ()
    have hz : T.limMap incl z = x := by
      apply S.ext
      intro i
      have hpi : T.projection i z = (⟨S.projection i x, hx i⟩ : T.X i) := by
        simpa [Function.comp, z] using
          congrFun
            (T.projection_comp_inverseLimitLift (fun (i : I) (_ : Unit) => (⟨S.projection i x,
                hx i⟩ : T.X i)) hcompat i) ()
      calc
        S.projection i (T.limMap incl z) = incl.map i (T.projection i z) := by
          simpa [Function.comp] using congrFun (T.π_comp_limMap (Θ := incl) i) z
        _ = (T.projection i z).1 := rfl
        _ = S.projection i x := by rw [hpi]
    have hxrange : x ∈ Set.range (T.limMap incl) := ⟨z, hz⟩
    rw [range_limMap_projectionImageInclusion_eq S hdir Y hY] at hxrange
    exact hxrange

/-- A closed subspace of an inverse limit is again an inverse limit of its projection images. -/
theorem InverseSystem.exists_homeomorph_closed_subspace_projection_images
    {I : Type u} [Preorder I] (S : InverseSystem (I := I)) [Nonempty I]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (Y : Set S.inverseLimit) (hY : IsClosed Y) :
    (∀ i, Nonempty (((S.projectionImageSystem Y).X i) ≃ₜ (S.projection i '' Y))) ∧
      Nonempty (Y ≃ₜ (S.projectionImageSystem Y).inverseLimit) := by
  constructor
  · intro i
    exact ⟨Homeomorph.refl _⟩
  · exact ⟨S.homeomorph_projectionImageSystem_of_isClosed hdir Y hY⟩

/-- The projection of the closure of a subset equals the closure of the projection image. -/
theorem InverseSystem.projection_image_closure_eq_closure_projection_image
    {I : Type u} [Preorder I] (S : InverseSystem (I := I))
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (i : I) (Y : Set S.inverseLimit) :
    S.projection i '' closure Y = closure (S.projection i '' Y) := by
  let hclosed : IsClosedMap (S.projection i) := (S.continuous_projection i).isClosedMap
  simpa using (hclosed.closure_image_eq_of_continuous (S.continuous_projection i) Y).symm

/-
Projection images of an arbitrary subset need not be closed, even for an inverse system indexed
by a singleton, so raw projection images cannot reconstruct the closure of that subset. The
statements below instead form the projection-image system from `closure Y`; the preceding theorem
then identifies each of its stage images with the closure of the corresponding image of `Y`.
-/
/--
The closure of a subset of an inverse limit is homeomorphic to the inverse limit of the
projection-image system of that closure.
-/
theorem InverseSystem.exists_homeomorph_closure_projection_images
    {I : Type u} [Preorder I] (S : InverseSystem (I := I)) [Nonempty I]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (Y : Set S.inverseLimit) :
    (∀ i, Nonempty (((S.projectionImageSystem (closure Y)).X i) ≃ₜ (S.projection i '' closure Y))) ∧
      Nonempty (closure Y ≃ₜ (S.projectionImageSystem (closure Y)).inverseLimit) := by
  simpa using S.exists_homeomorph_closed_subspace_projection_images hdir (Y := closure Y)
    isClosed_closure

/--
Closed subsets of the inverse limit are equal when their projection images agree at every stage.
-/
theorem InverseSystem.closure_eq_of_projection_images_eq
    {I : Type u} [Preorder I] (S : InverseSystem (I := I)) [Nonempty I]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (Y Y' : Set S.inverseLimit)
    (hproj : ∀ i, S.projection i '' closure Y = S.projection i '' closure Y') :
    closure Y = closure Y' := by
  ext x
  constructor
  · intro hx
    rw [S.mem_isClosed_iff_forall_projection_mem hdir isClosed_closure] at hx
    rw [S.mem_isClosed_iff_forall_projection_mem hdir isClosed_closure]
    intro i
    rw [← hproj i]
    exact hx i
  · intro hx
    rw [S.mem_isClosed_iff_forall_projection_mem hdir isClosed_closure] at hx
    rw [S.mem_isClosed_iff_forall_projection_mem hdir isClosed_closure]
    intro i
    rw [hproj i]
    exact hx i

/--
Equal raw projection images of two subsets force their closures in the inverse limit to be
equal.
-/
theorem InverseSystem.closure_eq_of_projection_images_eq_of_subsets
    {I : Type u} [Preorder I] (S : InverseSystem (I := I)) [Nonempty I]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (Y Y' : Set S.inverseLimit)
    (hproj : ∀ i, S.projection i '' Y = S.projection i '' Y') :
    closure Y = closure Y' := by
  apply S.closure_eq_of_projection_images_eq hdir Y Y'
  intro i
  calc
    S.projection i '' closure Y = closure (S.projection i '' Y) := by
      exact S.projection_image_closure_eq_closure_projection_image i Y
    _ = closure (S.projection i '' Y') := by rw [hproj i]
    _ = S.projection i '' closure Y' := by
      symm
      exact S.projection_image_closure_eq_closure_projection_image i Y'

/--
Any inverse system of compact Hausdorff spaces admits a surjective projection-image system with
the same inverse limit.
-/
noncomputable def InverseSystem.homeomorph_surjectiveProjectionImageSystem
    {I : Type u} [Preorder I] (S : InverseSystem (I := I)) [Nonempty I]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    S.inverseLimit ≃ₜ (S.projectionImageSystem (Set.univ : Set S.inverseLimit)).inverseLimit :=
  (Homeomorph.Set.univ S.inverseLimit).symm.trans
    (S.homeomorph_projectionImageSystem_of_isClosed hdir Set.univ isClosed_univ)

/--
The projection-image system of the full inverse limit is surjective and has the same inverse
limit as the original system.
-/
theorem InverseSystem.exists_homeomorph_surjectiveProjectionImageSystem
    {I : Type u} [Preorder I] (S : InverseSystem (I := I)) [Nonempty I]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    (∀ {i j : I} (hij : i ≤ j),
      Function.Surjective ((S.projectionImageSystem (Set.univ : Set S.inverseLimit)).map hij)) ∧
      Nonempty (S.inverseLimit ≃ₜ
        (S.projectionImageSystem (Set.univ : Set S.inverseLimit)).inverseLimit) := by
  constructor
  · intro i j hij
    exact S.surjective_projectionImageSystem_map (Y := (Set.univ : Set S.inverseLimit)) hij
  · exact ⟨S.homeomorph_surjectiveProjectionImageSystem hdir⟩

end ProCGroups.InverseSystems
