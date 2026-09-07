import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false

/-!
# Finite-group classes and their closure properties

`FiniteGroupClass` bundles an isomorphism-invariant predicate whose members are finite.  The
module provides universe-independent membership through finite-group representatives and defines
the closure conditions used throughout the pro-\(C\) library, including formations, varieties,
Melnikov formations, hereditary classes, and full formations.
-/

namespace ProCGroups

universe u v w

/-- A class of groups, implemented as an unbundled predicate on group carriers. -/
abbrev GroupClass := ∀ (G : Type u) [Group G], Prop

/--
A finite-group class is a predicate on group carriers together with a certificate that every
member is finite.
-/
structure FiniteGroupClass where
  /-- The membership predicate selecting the group carriers that belong to the class. -/
  pred : GroupClass.{u}
  /-- Membership supplies a `Finite` instance for the selected group. -/
  finite_of_mem : ∀ {G : Type u} [Group G], pred G → Finite G
  /--
  Membership transports forward across a multiplicative equivalence, making the predicate
  independent of the chosen carrier for a finite group.
  -/
  mem_of_mulEquiv :
    ∀ {G H : Type u} [Group G] [Group H], (G ≃* H) → pred G → pred H

/-- A finite group class coerces to its underlying predicate on finite groups. -/
instance instCoeFunFiniteGroupClass : CoeFun FiniteGroupClass (fun _ => GroupClass.{u}) where
  coe C := C.pred

namespace FiniteGroupClass


/-- Members of a bundled finite-group class are finite. -/
theorem finite {C : FiniteGroupClass.{u}} {G : Type u} [Group G] (hG : C G) : Finite G :=
  C.finite_of_mem hG

/-- Cross-universe membership in a finite-group class: `G` belongs when it is multiplicatively
equivalent to a member represented in the carrier universe of `C`. -/
def MemAcrossUniverses (C : FiniteGroupClass.{u}) (G : Type v) [Group G] : Prop :=
  ∃ H : FiniteGrp.{u}, C H ∧ Nonempty (H ≃* G)

/-- Cross-universe membership still certifies that the represented group is finite. -/
theorem finite_of_memAcrossUniverses {C : FiniteGroupClass.{u}}
    {G : Type v} [Group G] (hG : C.MemAcrossUniverses G) : Finite G := by
  rcases hG with ⟨H, _hH, ⟨e⟩⟩
  exact Finite.of_equiv H e.toEquiv

/-- Native membership gives cross-universe membership in the class's own universe. -/
theorem memAcrossUniverses_of_mem {C : FiniteGroupClass.{u}}
    {G : Type u} [Group G] (hG : C G) : C.MemAcrossUniverses G := by
  let : Finite G := C.finite hG
  exact ⟨FiniteGrp.of G, hG, ⟨MulEquiv.refl G⟩⟩

/-- In the class's own universe, cross-universe membership reduces to native membership. -/
theorem mem_of_memAcrossUniverses {C : FiniteGroupClass.{u}}
    {G : Type u} [Group G] (hG : C.MemAcrossUniverses G) : C G := by
  rcases hG with ⟨H, hH, ⟨e⟩⟩
  exact C.mem_of_mulEquiv e hH

/-- Cross-universe membership agrees with the original predicate in the original universe. -/
theorem memAcrossUniverses_iff (C : FiniteGroupClass.{u})
    {G : Type u} [Group G] : C.MemAcrossUniverses G ↔ C G :=
  ⟨mem_of_memAcrossUniverses, memAcrossUniverses_of_mem⟩

/-- Cross-universe membership is invariant under a multiplicative equivalence, even when the two
carriers live in different universes. -/
theorem memAcrossUniverses_iff_of_mulEquiv (C : FiniteGroupClass.{u})
    {G : Type v} {K : Type w} [Group G] [Group K] (e : G ≃* K) :
    C.MemAcrossUniverses G ↔ C.MemAcrossUniverses K := by
  constructor
  · rintro ⟨H, hH, ⟨hHG⟩⟩
    exact ⟨H, hH, ⟨hHG.trans e⟩⟩
  · rintro ⟨H, hH, ⟨hHK⟩⟩
    exact ⟨H, hH, ⟨hHK.trans e.symm⟩⟩

/-- `ULift` does not affect cross-universe membership. This is the preferred public replacement
for ad hoc Type-0 lowering lemmas. -/
theorem memAcrossUniverses_ulift_iff (C : FiniteGroupClass.{u})
    (G : Type v) [Group G] :
    C.MemAcrossUniverses (ULift.{w} G) ↔ C.MemAcrossUniverses G :=
  C.memAcrossUniverses_iff_of_mulEquiv MulEquiv.ulift

/-- In the native universe, `ULift` invariance also holds for the original predicate. -/
theorem ulift_mem_iff (C : FiniteGroupClass.{u}) (G : Type u) [Group G] :
    C (ULift.{u} G) ↔ C G :=
  ⟨fun h => C.mem_of_mulEquiv MulEquiv.ulift h,
    fun h => C.mem_of_mulEquiv MulEquiv.ulift.symm h⟩

/-- The object property represented by `C` on finite groups in any target universe. -/
def objectPropertyAcrossUniverses (C : FiniteGroupClass.{u}) :
    CategoryTheory.ObjectProperty FiniteGrp.{v} :=
  fun G => C.MemAcrossUniverses G

/-- The cross-universe categorical object property is closed under isomorphisms. -/
instance objectPropertyAcrossUniverses_isClosedUnderIsomorphisms
    (C : FiniteGroupClass.{u}) :
    C.objectPropertyAcrossUniverses.IsClosedUnderIsomorphisms where
  of_iso {G H} e hG := by
    let eGrp : G.toGrp ≅ H.toGrp :=
      (CategoryTheory.inducedFunctor FiniteGrp.toGrp).mapIso e
    exact (C.memAcrossUniverses_iff_of_mulEquiv eGrp.groupIsoToMulEquiv).1 hG


/--
The finite-group class contains all trivial groups. This is the class-level form needed when a
construction indexes over quotients and must include the terminal quotient. Formations provide
this automatically via \(\mathrm{Formation.one\_mem}\); users of a formation should not add a
separate hypothesis.
-/
class ContainsTrivialQuotients (C : FiniteGroupClass.{u}) : Prop where
  /-- Every group with at most one element belongs to `C`, regardless of its chosen carrier. -/
  of_subsingleton : ∀ {Q : Type u} [Group Q], Subsingleton Q → C Q

/-- The finite group class is closed under isomorphism. -/
def IsomClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {G H : Type u} [Group G] [Group H], Nonempty (G ≃* H) → C G → C H

/-- Every finite-group class is invariant under multiplicative equivalence by construction. -/
theorem isomClosed (C : FiniteGroupClass.{u}) : IsomClosed C := by
  intro G H _ _ hGH hG
  exact C.mem_of_mulEquiv hGH.some hG

/-- The canonical categorical object property attached to a finite-group class. -/
def objectProperty (C : FiniteGroupClass.{u}) : CategoryTheory.ObjectProperty FiniteGrp.{u} :=
  fun G => C G

/-- The categorical object property of a finite-group class is closed under isomorphisms. -/
instance objectProperty_isClosedUnderIsomorphisms (C : FiniteGroupClass.{u}) :
    C.objectProperty.IsClosedUnderIsomorphisms where
  of_iso {G H} e hG := by
    let eGrp : G.toGrp ≅ H.toGrp :=
      (CategoryTheory.inducedFunctor FiniteGrp.toGrp).mapIso e
    exact C.mem_of_mulEquiv eGrp.groupIsoToMulEquiv hG

/-- The finite group class is closed under taking subgroups. -/
def SubgroupClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {G : Type u} [Group G] (H : Subgroup G), C G → C H

/-- A finite-group class is closed under taking normal subgroups. -/
def NormalSubgroupClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {G : Type u} [Group G] (N : Subgroup G) [N.Normal], C G → C N

/-- The finite group class is closed under quotients. -/
def QuotientClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {G : Type u} [Group G] (N : Subgroup G) [N.Normal], C G → C (G ⧸ N)

/-- Closed under forming finite direct products. -/
def FiniteProductClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {ι : Type u} [Fintype ι] {G : ι → Type u} [∀ i, Group (G i)],
    (∀ i, C (G i)) → C (∀ i, G i)

/--
Closed under forming finite subdirect products. We package a finite subdirect product as an
injective homomorphism into a finite product whose coordinate maps are all surjective.
-/
def FiniteSubdirectProductClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {ι : Type u} [Fintype ι] {G : Type u} [Group G]
    {H : ι → Type u} [∀ i, Group (H i)],
    (f : G →* ∀ i, H i) →
    Function.Injective f →
    (∀ i, Function.Surjective fun g : G => f g i) →
    (∀ i, C (H i)) →
    C G

/-- The finite group class is closed under extensions. -/
def ExtensionClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {E : Type u} [Group E] (N : Subgroup E) [N.Normal],
    C N → C (E ⧸ N) → C E

/--
A formation is a family of finite groups closed under quotients and finite fiber or subdirect
products; the empty finite subdirect product supplies membership of the trivial group.
-/
structure Formation (C : FiniteGroupClass.{u}) : Prop where
  /-- Membership in `C` descends to quotients by arbitrary normal subgroups. -/
  quotientClosed : QuotientClosed C
  /--
  A finite group belongs to `C` when it embeds as a subdirect product of finitely many members
  of `C`.
  -/
  finiteSubdirectProductClosed : FiniteSubdirectProductClosed C

/-- A variety of finite groups. -/
structure Variety (C : FiniteGroupClass.{u}) : Prop where
  /-- Membership in `C` descends to subgroups. -/
  subgroupClosed : SubgroupClosed C
  /-- Membership in `C` descends to quotients by normal subgroups. -/
  quotientClosed : QuotientClosed C
  /-- Finite direct products of members of `C` again belong to `C`. -/
  finiteProductClosed : FiniteProductClosed C

/--
A Melnikov formation includes the underlying formation data directly, so the standard
formulation, including unit membership, is immediately available.
-/
structure MelnikovFormation (C : FiniteGroupClass.{u}) : Prop where
  /-- The quotient and finite-subdirect-product closure axioms of the underlying formation. -/
  formation : Formation C
  /-- Normal subgroups of members of `C` again belong to `C`. -/
  normalSubgroupClosed : NormalSubgroupClosed C
  /--
  A finite group belongs to `C` whenever a normal subgroup and the corresponding quotient both
  belong to `C`.
  -/
  extensionClosed : ExtensionClosed C

/--
A finite-group class is hereditary when it is closed under injective homomorphisms. This is the
form used by finite-quotient comap constructions: a pullback quotient embeds into the target
finite quotient, so membership descends along injections.
-/
structure Hereditary (C : FiniteGroupClass.{u}) : Prop where
  /--
  Membership pulls back along injective homomorphisms: a group embedded in a member of `C`
  itself belongs to `C`.
  -/
  of_injective :
    ∀ {G H : Type u} [Group G] [Group H],
      C H → (f : G →* H) → Function.Injective f → C G

/--
A full formation of finite groups. Equivalently, this is a Melnikov formation whose finite
groups are closed under subgroups. The \(Hereditary\) injective-hom formulation is derived as
FullFormation.hereditary.
-/
structure FullFormation (C : FiniteGroupClass.{u}) : Prop where
  /--
  The formation, normal-subgroup, and extension closure data supplied by a Melnikov formation.
  -/
  melnikovFormation : MelnikovFormation C
  /-- Arbitrary subgroups of members of `C` again belong to `C`. -/
  subgroupClosed : SubgroupClosed C

/-- A formation is closed under isomorphism. -/
theorem Formation.isomClosed {C : FiniteGroupClass.{u}} (_hForm : Formation C) :
    IsomClosed C :=
  C.isomClosed

/-- Every formation is closed under finite direct products. -/
theorem Formation.finiteProductClosed {C : FiniteGroupClass.{u}}
    (hForm : Formation C) : FiniteProductClosed C := by
  classical
  intro ι _ G _ hG
  let f : (∀ i, G i) →* ∀ i, G i := MonoidHom.id _
  refine hForm.finiteSubdirectProductClosed f ?_ ?_ hG
  · intro x y hxy
    simpa [f] using hxy
  · intro i y
    refine ⟨Function.update 1 i y, ?_⟩
    simp only [MonoidHom.id_apply, Function.update_self, f]

/--
Every formation contains the trivial group. This is the standard trivial-object clause. In this
version it is derived from the empty finite subdirect product, so no separate hypothesis
asserting that the trivial group belongs to the class is needed.
-/
theorem Formation.one_mem {C : FiniteGroupClass.{u}} (hForm : Formation C) :
    C PUnit := by
  let G : PEmpty → Type u := fun _ => PUnit
  let e : ((i : PEmpty) → G i) ≃* PUnit := by
    refine
      { toFun := fun _ => PUnit.unit
        invFun := fun _ i => nomatch i
        left_inv := ?_
        right_inv := ?_
        map_mul' := ?_ }
    · intro x
      ext i
    · intro x
      cases x
      rfl
    · intro x y
      rfl
  have hProd : C ((i : PEmpty) → G i) :=
    hForm.finiteProductClosed (ι := PEmpty) (G := G) (fun i => by cases i)
  exact hForm.isomClosed ⟨e⟩ hProd

/--
Use a specified multiplicative equivalence to transport membership in an isomorphism-closed
finite-group class.
-/
theorem IsomClosed.of_mulEquiv {C : FiniteGroupClass.{u}}
    (hIso : IsomClosed C) {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hG : C G) :
    C H :=
  hIso ⟨e⟩ hG

/--
Membership in an isomorphism-closed finite-group class is invariant under a specified
multiplicative equivalence.
-/
theorem IsomClosed.iff_of_mulEquiv {C : FiniteGroupClass.{u}}
    (hIso : IsomClosed C) {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) :
    C G ↔ C H :=
  ⟨hIso.of_mulEquiv e, hIso.of_mulEquiv e.symm⟩

/-- An isomorphism-closed class containing the trivial group contains every trivial group. -/
theorem containsTrivialQuotients_of_isomClosed_one_mem {C : FiniteGroupClass.{u}}
    (hIso : IsomClosed C) (hOne : C PUnit) :
    ContainsTrivialQuotients C := by
  refine ⟨?_⟩
  intro Q _ hQ
  let e : PUnit ≃* Q :=
    { toFun := fun _ => 1
      invFun := fun _ => PUnit.unit
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro q
        exact Subsingleton.elim (h := hQ) _ _
      map_mul' := by
        intro x y
        exact Subsingleton.elim (h := hQ) _ _ }
  exact hIso ⟨e⟩ hOne

/-- A formation contains the trivial quotients required by the pro-\(C\) construction. -/
theorem Formation.containsTrivialQuotients {C : FiniteGroupClass.{u}}
    (hForm : Formation C) :
    ContainsTrivialQuotients C :=
  containsTrivialQuotients_of_isomClosed_one_mem hForm.isomClosed hForm.one_mem

/--
Any isomorphism-closed subgroup-closed class that is closed under finite direct products is also
closed under finite subdirect products.
-/
theorem finiteSubdirectProductClosed_of_isomClosed_subgroupClosed_finiteProductClosed
    {C : FiniteGroupClass.{u}}
    (hIso : IsomClosed C)
    (hSub : SubgroupClosed C)
    (hProd : FiniteProductClosed C) :
    FiniteSubdirectProductClosed C := by
  intro ι _ G _ H _ f hf _hsurj hH
  have hPi : C (∀ i, H i) := hProd hH
  have hRange : C f.range := hSub f.range hPi
  have hRangeRestrictInj : Function.Injective f.rangeRestrict := by
    intro x y hxy
    exact hf (by simpa using congrArg Subtype.val hxy)
  let e : G ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨hRangeRestrictInj, f.rangeRestrict_surjective⟩
  exact hIso ⟨e.symm⟩ hRange

/-- An isomorphism-closed variety contains the trivial group. -/
theorem variety_one_mem_of_isomClosed {C : FiniteGroupClass.{u}}
    (hVar : Variety C) (hIso : IsomClosed C) :
    C PUnit := by
  let G : PEmpty → Type u := fun _ => PUnit
  let e : ((i : PEmpty) → G i) ≃* PUnit := by
    classical
    refine
      { toFun := fun _ => PUnit.unit
        invFun := fun _ i => nomatch i
        left_inv := ?_
        right_inv := ?_
        map_mul' := ?_ }
    · intro x
      ext i
    · intro x
      cases x
      rfl
    · intro x y
      rfl
  have hProd : C ((i : PEmpty) → G i) :=
    hVar.finiteProductClosed (ι := PEmpty) (G := G) (fun i => by cases i)
  exact hIso ⟨e⟩ hProd

/--
Any subgroup-closed, isomorphism-closed class that contains at least one group also contains the
trivial group.
-/
theorem one_mem_of_subgroupClosed_isomClosed {C : FiniteGroupClass.{u}}
    (hSub : SubgroupClosed C) (hIso : IsomClosed C)
    {G : Type u} [Group G] (hG : C G) :
    C PUnit := by
  let eBot : (⊥ : Subgroup G) ≃* PUnit :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => 1
      left_inv := by
        intro x
        exact Subsingleton.elim _ _
      right_inv := by
        intro x
        cases x
        rfl
      map_mul' := by
        intro x y
        rfl }
  exact hIso ⟨eBot⟩ (hSub (⊥ : Subgroup G) hG)

/-- Subgroup- and isomorphism-closure imply the injective-hom hereditary form. -/
theorem Hereditary.of_subgroupClosed_isomClosed {C : FiniteGroupClass.{u}}
    (hSub : SubgroupClosed C) (hIso : IsomClosed C) :
    Hereditary C := by
  refine ⟨?_⟩
  intro G H _ _ hH f hf
  have hRange : C f.range := hSub f.range hH
  let e : G ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨by
      intro x y hxy
      exact hf (by simpa using congrArg Subtype.val hxy),
    f.rangeRestrict_surjective⟩
  exact hIso ⟨e.symm⟩ hRange

/-- The finite group class is closed under taking subgroups. -/
theorem Hereditary.subgroupClosed {C : FiniteGroupClass.{u}}
    (hHer : Hereditary C) :
    SubgroupClosed C := by
  intro G _ H hG
  exact hHer.of_injective hG H.subtype Subtype.val_injective

/--
Use a specified multiplicative equivalence to transport membership in an isomorphism-closed
finite-group class.
-/
theorem Hereditary.of_mulEquiv {C : FiniteGroupClass.{u}}
    (hHer : Hereditary C) {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hH : C H) :
    C G :=
  hHer.of_injective hH e.toMonoidHom e.injective

/--
Membership in an isomorphism-closed finite-group class is invariant under a specified
multiplicative equivalence.
-/
theorem Hereditary.iff_of_mulEquiv {C : FiniteGroupClass.{u}}
    (hHer : Hereditary C) {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) :
    C G ↔ C H :=
  ⟨fun hG => hHer.of_mulEquiv e.symm hG, fun hH => hHer.of_mulEquiv e hH⟩

/-- A Melnikov formation is closed under quotients. -/
theorem MelnikovFormation.quotientClosed {C : FiniteGroupClass.{u}}
    (hC : MelnikovFormation C) : QuotientClosed C :=
  hC.formation.quotientClosed

/--
Every formation contains the trivial group. This is the standard trivial-object clause. In this
version it is derived from the empty finite subdirect product, so no separate hypothesis
asserting that the trivial group belongs to the class is needed.
-/
theorem MelnikovFormation.one_mem {C : FiniteGroupClass.{u}}
    (hC : MelnikovFormation C) : C PUnit :=
  hC.formation.one_mem

/-- A Melnikov formation contains the trivial quotients. -/
theorem MelnikovFormation.containsTrivialQuotients {C : FiniteGroupClass.{u}}
    (hC : MelnikovFormation C) :
    ContainsTrivialQuotients C :=
  hC.formation.containsTrivialQuotients

/-- A Melnikov formation is closed under isomorphism. -/
theorem MelnikovFormation.isomClosed {C : FiniteGroupClass.{u}}
    (hC : MelnikovFormation C) : IsomClosed C :=
  hC.formation.isomClosed


/-- A full formation is closed under quotients. -/
theorem FullFormation.quotientClosed {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) : QuotientClosed C :=
  hC.melnikovFormation.quotientClosed

/--
Every formation contains the trivial group. This is the standard trivial-object clause. In this
version it is derived from the empty finite subdirect product, so no separate hypothesis
asserting that the trivial group belongs to the class is needed.
-/
theorem FullFormation.one_mem {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) : C PUnit :=
  hC.melnikovFormation.one_mem

/-- A full formation contains the trivial quotients. -/
theorem FullFormation.containsTrivialQuotients {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) :
    ContainsTrivialQuotients C :=
  hC.melnikovFormation.containsTrivialQuotients

/-- A full formation is closed under isomorphism. -/
theorem FullFormation.isomClosed {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) : IsomClosed C :=
  hC.melnikovFormation.isomClosed


/-- A full formation is closed under normal subgroups. -/
theorem FullFormation.normalSubgroupClosed {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) : NormalSubgroupClosed C :=
  hC.melnikovFormation.normalSubgroupClosed

/-- A formation is closed under extensions. -/
theorem FullFormation.extensionClosed {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) : ExtensionClosed C :=
  hC.melnikovFormation.extensionClosed

/--
The subgroup-closed part of a full formation, in the injective-hom form used by finite quotient
pullbacks.
-/
theorem FullFormation.hereditary {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) : Hereditary C :=
  Hereditary.of_subgroupClosed_isomClosed hC.subgroupClosed hC.isomClosed

/-- An isomorphism-closed variety is a formation in the unbundled FiniteGroupClass formulation. -/
theorem variety_formation {C : FiniteGroupClass.{u}}
    (hVar : Variety C) (hIso : IsomClosed C) :
    Formation C := by
  refine ⟨hVar.quotientClosed, ?_⟩
  exact finiteSubdirectProductClosed_of_isomClosed_subgroupClosed_finiteProductClosed
    hIso hVar.subgroupClosed hVar.finiteProductClosed

/--
A variety together with extension-closure packages the standard finite-class closure hypotheses
used by the pro-\(C\) formulation.
-/
theorem Variety.closureBundle_of_isomClosed_extensionClosed {C : FiniteGroupClass.{u}}
    (hVar : Variety C)
    (hIso : IsomClosed C)
    (hExt : ExtensionClosed C) :
    Formation C ∧ SubgroupClosed C ∧ IsomClosed C ∧ QuotientClosed C ∧ ExtensionClosed C := by
  exact ⟨variety_formation hVar hIso, hVar.subgroupClosed, hIso, hVar.quotientClosed, hExt⟩

/--
For a Melnikov formation, the quotients by two normal subgroups lying in the class force the
quotient by their intersection to lie in the class as well.
-/
theorem MelnikovFormation.quotient_inf_mem {C : FiniteGroupClass.{u}}
    (hC : MelnikovFormation C)
    {G : Type u} [Group G]
    (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal]
    (h₁ : C (G ⧸ N₁)) (h₂ : C (G ⧸ N₂)) :
    C (G ⧸ (N₁ ⊓ N₂)) := by
  let E : Type u := G ⧸ (N₁ ⊓ N₂)
  let L : Subgroup E := Subgroup.map (QuotientGroup.mk' (N₁ ⊓ N₂)) N₁
  let : L.Normal := by
    dsimp [L]
    exact Subgroup.Normal.map (show N₁.Normal by infer_instance)
      (QuotientGroup.mk' (N₁ ⊓ N₂))
      (QuotientGroup.mk'_surjective (N₁ ⊓ N₂))
  have hQuotL : C (E ⧸ L) := by
    let e : E ⧸ L ≃* G ⧸ N₁ :=
      QuotientGroup.quotientQuotientEquivQuotient (N₁ ⊓ N₂) N₁ inf_le_left
    exact hC.isomClosed ⟨e.symm⟩ h₁
  let K₂ : Subgroup (G ⧸ N₂) := Subgroup.map (QuotientGroup.mk' N₂) N₁
  let : K₂.Normal := by
    dsimp [K₂]
    exact Subgroup.Normal.map (show N₁.Normal by infer_instance)
      (QuotientGroup.mk' N₂)
      (QuotientGroup.mk'_surjective N₂)
  have hK₂ : C K₂ := hC.normalSubgroupClosed K₂ h₂
  let ψ₂ : N₁ →* G ⧸ N₂ := (QuotientGroup.mk' N₂).comp N₁.subtype
  have hψ₂range : ψ₂.range = K₂ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hψ₂ker : ψ₂.ker = N₂.subgroupOf N₁ := by
    ext x
    change QuotientGroup.mk' N₂ x.1 = 1 ↔ x.1 ∈ N₂
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff (N := N₂) x.1]
  have hQuotN₁ : C (N₁ ⧸ N₂.subgroupOf N₁) := by
    let e₀ : N₁ ⧸ N₂.subgroupOf N₁ ≃* N₁ ⧸ ψ₂.ker :=
      QuotientGroup.quotientMulEquivOfEq hψ₂ker.symm
    let e₁ : N₁ ⧸ ψ₂.ker ≃* ψ₂.range := QuotientGroup.quotientKerEquivRange ψ₂
    let e₂ : ψ₂.range ≃* K₂ := MulEquiv.subgroupCongr hψ₂range
    exact hC.isomClosed ⟨((e₀.trans e₁).trans e₂).symm⟩ hK₂
  let ψ₁ : N₁ →* E := (QuotientGroup.mk' (N₁ ⊓ N₂)).comp N₁.subtype
  have hψ₁range : ψ₁.range = L := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hψ₁ker : ψ₁.ker = N₂.subgroupOf N₁ := by
    ext x
    change QuotientGroup.mk' (N₁ ⊓ N₂) x.1 = 1 ↔ x.1 ∈ N₂
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := N₁ ⊓ N₂) x.1).1 hx |>.2
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := N₁ ⊓ N₂) x.1).2 ⟨x.2, hx⟩
  have hL : C L := by
    let e₀ : N₁ ⧸ N₂.subgroupOf N₁ ≃* N₁ ⧸ ψ₁.ker :=
      QuotientGroup.quotientMulEquivOfEq hψ₁ker.symm
    let e₁ : N₁ ⧸ ψ₁.ker ≃* ψ₁.range := QuotientGroup.quotientKerEquivRange ψ₁
    let e₂ : ψ₁.range ≃* L := MulEquiv.subgroupCongr hψ₁range
    exact hC.isomClosed ⟨(e₀.trans e₁).trans e₂⟩ hQuotN₁
  exact hC.extensionClosed L hL hQuotL

/-- A Melnikov formation with subgroup closure gives the standard finite-class closure bundle. -/
theorem MelnikovFormation.closureBundle_of_subgroupClosed {C : FiniteGroupClass.{u}}
    (hC : MelnikovFormation C)
    (hSub : SubgroupClosed C) :
    Formation C ∧ SubgroupClosed C ∧ IsomClosed C ∧ QuotientClosed C ∧ ExtensionClosed C := by
  exact ⟨hC.formation, hSub, hC.isomClosed, hC.quotientClosed, hC.extensionClosed⟩

/--
For a formation, the quotient by the intersection of two normal subgroups whose individual
quotients lie in \(C\) also lies in \(C\). This is the two-factor form of (C4).
-/
theorem Formation.quotient_inf_mem {C : FiniteGroupClass.{u}}
    (hC : Formation C) {G : Type u} [Group G]
    (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal]
    (h₁ : C (G ⧸ N₁)) (h₂ : C (G ⧸ N₂)) :
    C (G ⧸ (N₁ ⊓ N₂)) := by
  classical
  let H : ULift Bool → Type u
    | ⟨false⟩ => G ⧸ N₁
    | ⟨true⟩ => G ⧸ N₂
  let : ∀ b : ULift Bool, Group (H b) := by
    intro b
    cases b with
    | up b =>
        cases b <;> infer_instance
  let f : G ⧸ (N₁ ⊓ N₂) →* ∀ b : ULift Bool, H b :=
    { toFun := fun x b =>
        match b with
        | ⟨false⟩ => QuotientGroup.map (N₁ ⊓ N₂) N₁ (MonoidHom.id G) inf_le_left x
        | ⟨true⟩ => QuotientGroup.map (N₁ ⊓ N₂) N₂ (MonoidHom.id G) inf_le_right x
      map_one' := by
        funext b
        cases b with
        | up b =>
            cases b <;> rfl
      map_mul' := by
        intro x y
        funext b
        cases b with
        | up b =>
            cases b with
            | false =>
                exact (QuotientGroup.map (N₁ ⊓ N₂) N₁ (MonoidHom.id G) inf_le_left).map_mul x y
            | true =>
                exact (QuotientGroup.map (N₁ ⊓ N₂) N₂ (MonoidHom.id G) inf_le_right).map_mul x y }
  have hfalse_eval (g : G) :
      f (QuotientGroup.mk' (N₁ ⊓ N₂) g) ⟨false⟩ = QuotientGroup.mk' N₁ g := by
    change QuotientGroup.map (N₁ ⊓ N₂) N₁ (MonoidHom.id G) inf_le_left
      (QuotientGroup.mk' (N₁ ⊓ N₂) g) = QuotientGroup.mk' N₁ g
    exact QuotientGroup.map_mk' (N₁ ⊓ N₂) N₁ (MonoidHom.id G) inf_le_left g
  have htrue_eval (g : G) :
      f (QuotientGroup.mk' (N₁ ⊓ N₂) g) ⟨true⟩ = QuotientGroup.mk' N₂ g := by
    change QuotientGroup.map (N₁ ⊓ N₂) N₂ (MonoidHom.id G) inf_le_right
      (QuotientGroup.mk' (N₁ ⊓ N₂) g) = QuotientGroup.mk' N₂ g
    exact QuotientGroup.map_mk' (N₁ ⊓ N₂) N₂ (MonoidHom.id G) inf_le_right g
  refine hC.finiteSubdirectProductClosed (ι := ULift Bool) (H := H) f ?_ ?_ ?_
  · intro x y hxy
    rcases QuotientGroup.mk'_surjective (N₁ ⊓ N₂) x with ⟨gx, rfl⟩
    rcases QuotientGroup.mk'_surjective (N₁ ⊓ N₂) y with ⟨gy, rfl⟩
    apply QuotientGroup.eq.2
    constructor
    · have hfalse :
          f (QuotientGroup.mk' (N₁ ⊓ N₂) gx) ⟨false⟩ =
            f (QuotientGroup.mk' (N₁ ⊓ N₂) gy) ⟨false⟩ :=
        congrArg (fun z : ∀ b : ULift Bool, H b => z ⟨false⟩) hxy
      exact QuotientGroup.eq.1
        ((hfalse_eval gx).symm.trans (hfalse.trans (hfalse_eval gy)))
    · have htrue :
          f (QuotientGroup.mk' (N₁ ⊓ N₂) gx) ⟨true⟩ =
            f (QuotientGroup.mk' (N₁ ⊓ N₂) gy) ⟨true⟩ :=
        congrArg (fun z : ∀ b : ULift Bool, H b => z ⟨true⟩) hxy
      exact QuotientGroup.eq.1
        ((htrue_eval gx).symm.trans (htrue.trans (htrue_eval gy)))
  · intro b
    cases b with
    | up b =>
        cases b with
        | false =>
            intro x
            rcases QuotientGroup.mk'_surjective N₁ x with ⟨g, rfl⟩
            refine ⟨QuotientGroup.mk' (N₁ ⊓ N₂) g, ?_⟩
            exact hfalse_eval g
        | true =>
            intro x
            rcases QuotientGroup.mk'_surjective N₂ x with ⟨g, rfl⟩
            refine ⟨QuotientGroup.mk' (N₁ ⊓ N₂) g, ?_⟩
            exact htrue_eval g
  · intro b
    cases b with
    | up b =>
      cases b with
      | false =>
          simpa [H] using h₁
      | true =>
          simpa [H] using h₂

end FiniteGroupClass

end ProCGroups
