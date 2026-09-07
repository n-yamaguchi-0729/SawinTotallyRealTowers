import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

set_option autoImplicit false

/-!
# Reidemeister Schreier / Groupoid

This module rebuilds the spanning-tree loop construction using public conversion functions between
mathlib's vertex type synonyms.  No private-root declaration or backward elaboration option enters
the public API.
-/

open CategoryTheory CategoryTheory.SingleObj Quiver

universe u

namespace ReidemeisterSchreier.Groupoid

/-- A generator-quiver vertex viewed in the ambient groupoid. -/
abbrev generatorObject
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (a : IsFreeGroupoid.Generators G) : G :=
  a

/-- A generating arrow with both endpoints expressed through `generatorObject`. -/
abbrev generatorHom
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    {a b : IsFreeGroupoid.Generators G} (e : a ⟶ b) :
    generatorObject a ⟶ generatorObject b :=
  IsFreeGroupoid.of e

/-- A spanning-tree vertex viewed in the ambient groupoid. -/
abbrev treeVertexObject
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G))
    (a : T) : G :=
  generatorObject a

/-- An ambient groupoid vertex viewed as a vertex of the wide spanning subquiver. -/
abbrev treeVertexOfObject
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G))
    (a : G) : T :=
  a

/-- The root vertex of a spanning tree, explicitly returned in the ambient groupoid type. -/
noncomputable abbrev rootObject
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G))
    [Quiver.Arborescence T] : G :=
  treeVertexObject T (Quiver.root T)

/-- A tree edge viewed as an arrow of the ambient groupoid. -/
noncomputable abbrev treeEdgeHom
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G))
    {a b : T} (e : a ⟶ b) : treeVertexObject T a ⟶ treeVertexObject T b :=
  Sum.recOn e.val (fun f => generatorHom f) (fun f => inv (generatorHom f))

/-- A path in the chosen spanning tree gives an arrow from its explicit root. -/
noncomputable def rootHomOfPath
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T] :
    ∀ {a : T}, Quiver.Path (Quiver.root T) a →
      (rootObject T ⟶ treeVertexObject T a)
  | _, Quiver.Path.nil => 𝟙 _
  | _, Quiver.Path.cons p e => rootHomOfPath T p ≫ treeEdgeHom T e

/-- The canonical spanning-tree arrow from the explicit root to a tree vertex. -/
noncomputable def rootTreeHom
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T]
    (a : T) : rootObject T ⟶ treeVertexObject T a :=
  rootHomOfPath T default

/-- Any spanning-tree path computes the canonical root arrow. -/
theorem rootTreeHom_eq
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T]
    {a : T} (p : Quiver.Path (Quiver.root T) a) :
    rootTreeHom T a = rootHomOfPath T p := by
  rw [rootTreeHom, Unique.default_eq]

/-- The canonical tree arrow at the explicit root is the identity. -/
@[simp] theorem rootTreeHom_root
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T] :
    rootTreeHom T (Quiver.root T) = 𝟙 _ :=
  (rootTreeHom_eq T Quiver.Path.nil).trans rfl

/-- The loop associated to a groupoid arrow, based at the explicit spanning-tree root. -/
noncomputable def rootLoopOfHom
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T]
    {a b : G} (p : a ⟶ b) : End (rootObject T) :=
  rootTreeHom T (treeVertexOfObject T a) ≫ p ≫
    inv (rootTreeHom T (treeVertexOfObject T b))

/-- A tree edge gives the identity explicit-root loop. -/
@[simp] theorem rootLoopOfHom_eq_id
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T]
    {a b : IsFreeGroupoid.Generators G} (e : a ⟶ b)
    (h : e ∈ Quiver.wideSubquiverSymmetrify T a b) :
    rootLoopOfHom T (generatorHom e) = 𝟙 (rootObject T) := by
  rcases h with h | h
  · have htb :
        rootTreeHom T (treeVertexOfObject T (generatorObject b)) =
          rootTreeHom T (treeVertexOfObject T (generatorObject a)) ≫ generatorHom e := by
      let p : Quiver.Path (Quiver.root T)
          (treeVertexOfObject T (generatorObject a)) := default
      let edge : treeVertexOfObject T (generatorObject a) ⟶
          treeVertexOfObject T (generatorObject b) := ⟨Sum.inl e, h⟩
      exact (rootTreeHom_eq T (p.cons edge)).trans
        (congrArg (fun q : rootObject T ⟶ generatorObject a => q ≫ generatorHom e)
          (rootTreeHom_eq T p).symm)
    unfold rootLoopOfHom
    rw [← Category.assoc, ← htb, IsIso.hom_inv_id]
  · have hta :
        rootTreeHom T (treeVertexOfObject T (generatorObject a)) =
          rootTreeHom T (treeVertexOfObject T (generatorObject b)) ≫ inv (generatorHom e) := by
      let p : Quiver.Path (Quiver.root T)
          (treeVertexOfObject T (generatorObject b)) := default
      let edge : treeVertexOfObject T (generatorObject b) ⟶
          treeVertexOfObject T (generatorObject a) := ⟨Sum.inr e, h⟩
      exact (rootTreeHom_eq T (p.cons edge)).trans
        (congrArg (fun q : rootObject T ⟶ generatorObject b => q ≫ inv (generatorHom e))
          (rootTreeHom_eq T p).symm)
    unfold rootLoopOfHom
    rw [hta]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id]

/-- The functor induced by a homomorphism from the explicit root vertex group. -/
noncomputable def rootFunctorOfMonoidHom
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T]
    {X : Type u} [Monoid X] (f : End (rootObject T) →* X) :
    G ⥤ CategoryTheory.SingleObj X where
  obj _ := ()
  map p := f (rootLoopOfHom T p)
  map_id := by
    intro a
    dsimp only [rootLoopOfHom]
    rw [Category.id_comp, IsIso.hom_inv_id, ← End.one_def, f.map_one, id_as_one]
  map_comp := by
    intros
    rw [CategoryTheory.SingleObj.comp_as_mul, ← f.map_mul]
    simp only [IsIso.inv_hom_id_assoc, rootLoopOfHom, End.mul_def, Category.assoc]

/--
The explicit-root induced functor applies the supplied homomorphism to the explicit-root loop.
-/
@[simp] theorem rootFunctorOfMonoidHom_map
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T]
    {X : Type u} [Monoid X] (f : End (rootObject T) →* X)
    {a b : G} (p : a ⟶ b) :
    (rootFunctorOfMonoidHom T f).map p = f (rootLoopOfHom T p) := rfl

/-- At the root, turning an endomorphism into a loop does nothing. -/
@[simp] theorem rootLoopOfHom_end
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T]
    (p : End (rootObject T)) : rootLoopOfHom T p = p := by
  simp only [rootLoopOfHom, treeVertexOfObject, rootObject, rootTreeHom_root,
    IsIso.inv_id, Category.id_comp, Category.comp_id]

/-- A functor trivial on the spanning tree maps every explicit-root loop to the original arrow. -/
lemma map_loopOfHom_eq_map
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T]
    {X : Type u} [Group X] (F : G ⥤ CategoryTheory.SingleObj X)
    (hTree : ∀ {a b : IsFreeGroupoid.Generators G} (e : a ⟶ b),
      e ∈ Quiver.wideSubquiverSymmetrify T a b → F.map (generatorHom e) = 1) :
    ∀ {a b} (q : a ⟶ b), F.map (rootLoopOfHom T q) = (F.map q : X) := by
  suffices
      ∀ {a : T} (p : Quiver.Path (Quiver.root T) a),
        F.map (rootHomOfPath T p) = 1 by
    intro x y q
    simp only [this, rootTreeHom, CategoryTheory.SingleObj.comp_as_mul, inv_as_inv,
      rootLoopOfHom, inv_one, mul_one, one_mul, Functor.map_inv, Functor.map_comp]
  intro a p
  induction p with
  | nil =>
      simpa only [rootHomOfPath, id_as_one] using F.map_id (rootObject T)
  | cons p e ih =>
      rw [rootHomOfPath, F.map_comp, CategoryTheory.SingleObj.comp_as_mul, ih, mul_one]
      rcases e with ⟨e | e, eT⟩
      · rw [treeEdgeHom, hTree e (Or.inl eT)]
      · rw [treeEdgeHom, F.map_inv, inv_as_inv, inv_eq_one, hTree e (Or.inr eT)]

/-- The complement of a chosen spanning tree in a free connected groupoid gives
an explicit free group basis of the root vertex group. -/
noncomputable def endBasis
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T] :
    FreeGroupBasis
      (((Quiver.wideSubquiverEquivSetTotal <| Quiver.wideSubquiverSymmetrify T)ᶜ : Set _))
      (End (rootObject T)) := by
  classical
  refine FreeGroupBasis.ofUniqueLift
    (((Quiver.wideSubquiverEquivSetTotal <| Quiver.wideSubquiverSymmetrify T)ᶜ : Set _))
    (fun e => rootLoopOfHom T (generatorHom e.val.hom))
    ?_
  intro X _ f
  let f' : Quiver.Labelling (IsFreeGroupoid.Generators G) X := fun a b e =>
    if h : e ∈ Quiver.wideSubquiverSymmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
  rcases IsFreeGroupoid.unique_lift f' with ⟨F', hF', uF'⟩
  refine ⟨F'.mapEnd _, ?_, ?_⟩
  · have hloop :
        ∀ {a b} (q : a ⟶ b), F'.map (rootLoopOfHom T q) = (F'.map q : X) :=
      map_loopOfHom_eq_map T F' (by
        intro a b e he
        rw [hF']
        simp only [f', he, ↓reduceDIte])
    rintro ⟨⟨a, b, e⟩, h⟩
    simp only [Functor.mapEnd, DFunLike.coe, hloop, hF']
    exact dif_neg h
  · intro E hE
    ext x
    change E x = (F'.map x : X)
    suffices (rootFunctorOfMonoidHom T E).map x = F'.map x by
      simpa only [rootFunctorOfMonoidHom_map, rootLoopOfHom_end] using this
    congr
    apply uF'
    intro a b e
    have hEval : E (rootLoopOfHom T (generatorHom e)) = f' e := by
      by_cases h : e ∈ Quiver.wideSubquiverSymmetrify T a b
      · rw [rootLoopOfHom_eq_id T e h, ← End.one_def, E.map_one]
        simp only [f', dif_pos h]
      · simpa only [f', dif_neg h] using hE ⟨⟨a, b, e⟩, h⟩
    exact (rootFunctorOfMonoidHom_map T E (generatorHom e)).trans hEval

/-- The explicit spanning-tree basis evaluates to the corresponding explicit-root loop. -/
@[simp] theorem endBasis_apply
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Quiver.Arborescence T]
    (e : (((Quiver.wideSubquiverEquivSetTotal <| Quiver.wideSubquiverSymmetrify T)ᶜ : Set _))) :
    endBasis T e = rootLoopOfHom T (generatorHom e.1.hom) := by
  unfold endBasis FreeGroupBasis.ofUniqueLift
  change
    FreeGroup.lift (fun e => rootLoopOfHom T (generatorHom e.1.hom))
      (FreeGroup.of e) = rootLoopOfHom T (generatorHom e.1.hom)
  simp only [FreeGroup.lift_apply_of]

end ReidemeisterSchreier.Groupoid
