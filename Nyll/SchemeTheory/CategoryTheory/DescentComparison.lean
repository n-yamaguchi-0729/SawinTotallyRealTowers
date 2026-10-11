/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729

The descent comparison constructions used here are from Mathlib:

DescentData.lean: Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Sites/Descent/DescentData.lean

DescentDataPrime.lean: Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Sites/Descent/DescentDataPrime.lean
-/

import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Comparison and overlap transport for descent data

Transport the coherence of actual descent morphisms along component equations,
project the existing base-change isomorphism, and compare pullback overlaps
using commuting squares. The coherence comes from `DescentData.Hom.comm`,
`pullFunctorObjHom_eq`, and `pullHom_hom`; the base-change component is projected
from Mathlib's existing `NatIso.ofComponents` / `DescentData.isoMk` construction.
The chosen-overlap isomorphism is constructed using `DescentData'.isoMk` and
`descentDataEquivalence`, with the pseudofunctor kept abstract.
-/

universe t t' v v' u u'

open CategoryTheory Opposite CategoryTheory.Limits
open CategoryTheory.Pseudofunctor

namespace CategoryTheory.Pseudofunctor.DescentComparison

/-- Transport the overlap compatibility of a fixed descent morphism along two
proved component equations. The overlap equation itself comes from φ.comm. -/
theorem comm_of_component_eq
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ k, X k ⟶ S)
    {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂)
    {V : C} (m : V ⟶ S) (i j : ι)
    (r₁ : V ⟶ X i) (r₂ : V ⟶ X j)
    (G₁ : r₁ ≫ f i = m) (G₂ : r₂ ≫ f j = m)
    (a : D₁.obj i ⟶ D₂.obj i) (b : D₁.obj j ⟶ D₂.obj j)
    (ha : φ.hom i = a) (hb : φ.hom j = b) :
    (F.map r₁.op.toLoc).toFunctor.map a ≫ D₂.hom m r₁ r₂ G₁ G₂ =
      D₁.hom m r₁ r₂ G₁ G₂ ≫ (F.map r₂.op.toLoc).toFunctor.map b := by
  subst a
  subst b
  exact φ.comm (i₁ := i) (i₂ := j) m r₁ r₂ G₁ G₂

/-- The component of the existing descent base-change morphism is precisely
its prescribed commutative-square component. -/
theorem baseChange_hom_component
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {ι : Type t} {ι' : Type t'} {S S' : C}
    {X : ι → C} {X' : ι' → C}
    (f : ∀ i, X i ⟶ S) (f' : ∀ j, X' j ⟶ S')
    (p : S' ⟶ S) (α : ι' → ι) (p' : ∀ j, X' j ⟶ X (α j))
    (w : ∀ j, p' j ≫ f (α j) = f' j ≫ p)
    (M : F.obj (.mk (op S))) (j : ι') :
    ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F
      (f := f) (f' := f') (p := p) (p' := p') (α := α) w).hom.app M).hom j =
      ((Cat.Hom.toNatIso
        (F.isoMapOfCommSq (CommSq.mk (w j)).op.toLoc)).symm.app M).hom := by
  rfl

/-- Pulling a descent overlap through two genuinely commuting squares gives
the overlap of the existing pullFunctor, conjugated by its square components. -/
theorem pullback_overlap_square
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {ι : Type t} {ι' : Type t'} {S S' : C}
    {X : ι → C} {X' : ι' → C}
    (f : ∀ i, X i ⟶ S) (f' : ∀ j, X' j ⟶ S')
    (p : S' ⟶ S) (α : ι' → ι) (p' : ∀ j, X' j ⟶ X (α j))
    (w : ∀ j, p' j ≫ f (α j) = f' j ≫ p)
    (D : F.DescentData f)
    {Y V : C} (d : Y ⟶ S) (m : V ⟶ S') (s : V ⟶ Y)
    (i j : ι') (a₁ : Y ⟶ X (α i)) (a₂ : Y ⟶ X (α j))
    (r₁ : V ⟶ X' i) (r₂ : V ⟶ X' j)
    (e₁ : a₁ ≫ f (α i) = d) (e₂ : a₂ ≫ f (α j) = d)
    (G₁ : r₁ ≫ f' i = m) (G₂ : r₂ ≫ f' j = m)
    (E₁ : s ≫ a₁ = r₁ ≫ p' i) (E₂ : s ≫ a₂ = r₂ ≫ p' j)
    (hq : s ≫ d = m ≫ p) :
    let P := (Pseudofunctor.DescentData.pullFunctor F
      (f := f) (f' := f') (p := p) (p' := p') (α := α) w).obj D
    let C₁ := (Cat.Hom.toNatIso
      (F.isoMapOfCommSq (CommSq.mk E₁).op.toLoc)).symm.app (D.obj (α i))
    let C₂ := (Cat.Hom.toNatIso
      (F.isoMapOfCommSq (CommSq.mk E₂).op.toLoc)).symm.app (D.obj (α j))
    (F.map s.op.toLoc).toFunctor.map (D.hom d a₁ a₂ e₁ e₂) ≫ C₂.hom =
      C₁.hom ≫ P.hom m r₁ r₂ G₁ G₂ := by
  intro P C₁ C₂
  let A₁ := (Cat.Hom.toNatIso (F.mapComp' a₁.op.toLoc s.op.toLoc
    (r₁ ≫ p' i).op.toLoc (by rw [← E₁]; rfl))).symm.app (D.obj (α i))
  let A₂ := (Cat.Hom.toNatIso (F.mapComp' a₂.op.toLoc s.op.toLoc
    (r₂ ≫ p' j).op.toLoc (by rw [← E₂]; rfl))).symm.app (D.obj (α j))
  let B₁ := (Cat.Hom.toNatIso (F.mapComp' (p' i).op.toLoc r₁.op.toLoc
    (r₁ ≫ p' i).op.toLoc rfl)).symm.app (D.obj (α i))
  let B₂ := (Cat.Hom.toNatIso (F.mapComp' (p' j).op.toLoc r₂.op.toLoc
    (r₂ ≫ p' j).op.toLoc rfl)).symm.app (D.obj (α j))
  let N := (F.map s.op.toLoc).toFunctor.map (D.hom d a₁ a₂ e₁ e₂)
  have k₁ : (r₁ ≫ p' i) ≫ f (α i) = m ≫ p := by
    rw [Category.assoc, w i, ← Category.assoc, G₁]
  have k₂ : (r₂ ≫ p' j) ≫ f (α j) = m ≫ p := by
    rw [Category.assoc, w j, ← Category.assoc, G₂]
  have hC₁ : C₁ = A₁ ≪≫ B₁.symm := by
    apply Iso.ext
    change (F.isoMapOfCommSq (CommSq.mk E₁).op.toLoc).inv.toNatTrans.app
        (D.obj (α i)) = A₁.hom ≫ B₁.inv
    rw [F.isoMapOfCommSq_eq (CommSq.mk E₁).op.toLoc (r₁ ≫ p' i).op.toLoc rfl]
    rfl
  have hC₂ : C₂ = A₂ ≪≫ B₂.symm := by
    apply Iso.ext
    change (F.isoMapOfCommSq (CommSq.mk E₂).op.toLoc).inv.toNatTrans.app
        (D.obj (α j)) = A₂.hom ≫ B₂.inv
    rw [F.isoMapOfCommSq_eq (CommSq.mk E₂).op.toLoc (r₂ ≫ p' j).op.toLoc rfl]
    rfl
  have hD : A₁.inv ≫ N ≫ A₂.hom =
      D.hom (m ≫ p) (r₁ ≫ p' i) (r₂ ≫ p' j) k₁ k₂ := by
    exact D.pullHom_hom (i₁ := α i) (i₂ := α j)
      s d (m ≫ p) hq a₁ a₂ e₁ e₂ (r₁ ≫ p' i) (r₂ ≫ p' j) E₁ E₂
  have hproj : P.hom m r₁ r₂ G₁ G₂ =
      Pseudofunctor.DescentData.pullFunctorObjHom
        (F := F) (f := f) (f' := f') (p := p) (p' := p') (α := α)
        w D m r₁ r₂ G₁ G₂ := by
    dsimp only [P, Pseudofunctor.DescentData.pullFunctor,
      Pseudofunctor.DescentData.pullFunctorObj]
    simp only [G₁]
  have hPraw := Pseudofunctor.DescentData.pullFunctorObjHom_eq
    (F := F) (f := f) (f' := f') (p := p) (p' := p') (α := α)
    w D (j₁ := i) (j₂ := j) m r₁ r₂
    (m ≫ p) (r₁ ≫ p' i) (r₂ ≫ p' j) G₁ G₂ rfl rfl rfl
  have hP := hproj.trans hPraw
  rw [← hD] at hP
  change N ≫ C₂.hom = C₁.hom ≫ P.hom m r₁ r₂ G₁ G₂
  rw [hC₁, hC₂, hP]
  change N ≫ (A₂.hom ≫ B₂.inv) =
    (A₁.hom ≫ B₁.inv) ≫ (B₁.hom ≫ ((A₁.inv ≫ N ≫ A₂.hom) ≫ B₂.inv))
  have htail :=
    (Category.assoc (obj := F.obj (.mk (op V))) A₁.inv (N ≫ A₂.hom) B₂.inv).trans
      (congrArg
        (fun z : (F.map a₁.op.toLoc ≫ F.map s.op.toLoc).toFunctor.obj (D.obj (α i)) ⟶
            (F.map (p' j).op.toLoc ≫ F.map r₂.op.toLoc).toFunctor.obj (D.obj (α j)) =>
          A₁.inv ≫ z)
        (Category.assoc (obj := F.obj (.mk (op V))) N A₂.hom B₂.inv))
  have hreshape := congrArg
    (fun z : (F.map (r₁ ≫ p' i).op.toLoc).toFunctor.obj (D.obj (α i)) ⟶
        (F.map (p' j).op.toLoc ≫ F.map r₂.op.toLoc).toFunctor.obj (D.obj (α j)) =>
      (A₁.hom ≫ B₁.inv) ≫ B₁.hom ≫ z) htail
  have hB := Iso.inv_hom_id_assoc B₁ (A₁.inv ≫ N ≫ A₂.hom ≫ B₂.inv)
  have hA := Iso.hom_inv_id_assoc A₁ (N ≫ A₂.hom ≫ B₂.inv)
  have hcancel :=
    (Category.assoc (obj := F.obj (.mk (op V))) A₁.hom B₁.inv
      (B₁.hom ≫ A₁.inv ≫ N ≫ A₂.hom ≫ B₂.inv)).trans
      ((congrArg
        (fun z : (F.map (r₁ ≫ p' i).op.toLoc).toFunctor.obj (D.obj (α i)) ⟶
            (F.map (p' j).op.toLoc ≫ F.map r₂.op.toLoc).toFunctor.obj (D.obj (α j)) =>
          A₁.hom ≫ z) hB).trans hA)
  exact (hreshape.trans hcancel).symm

/-- Project the canonical overlap directly, before specializing the fibre. -/
theorem canonical_overlap_hom
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (M : F.obj (.mk (op S))) {Y : C} (q : Y ⟶ S) (i j : ι)
    (a₁ : Y ⟶ X i) (a₂ : Y ⟶ X j)
    (h₁ : a₁ ≫ f i = q) (h₂ : a₂ ≫ f j = q) :
    ((F.toDescentData f).obj M).hom q a₁ a₂ h₁ h₂ =
      (F.mapComp' (f i).op.toLoc a₁.op.toLoc q.op.toLoc
        (by rw [← h₁]; rfl)).inv.toNatTrans.app M ≫
      (F.mapComp' (f j).op.toLoc a₂.op.toLoc q.op.toLoc
        (by rw [← h₂]; rfl)).hom.toNatTrans.app M := by
  rfl

/-- The canonical target overlap cancels against its second comparison leg. -/
theorem canonical_overlap_comp_inverse
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (M : F.obj (.mk (op S)))
    {V : C} (m : V ⟶ S) (i j : ι)
    (r₁ : V ⟶ X i) (r₂ : V ⟶ X j)
    (G₁ : r₁ ≫ f i = m) (G₂ : r₂ ≫ f j = m) :
    ((F.toDescentData f).obj M).hom m r₁ r₂ G₁ G₂ ≫
      (F.mapComp' (f j).op.toLoc r₂.op.toLoc m.op.toLoc
        (by rw [← G₂]; rfl)).inv.toNatTrans.app M =
      (F.mapComp' (f i).op.toLoc r₁.op.toLoc m.op.toLoc
        (by rw [← G₁]; rfl)).inv.toNatTrans.app M := by
  let T₁ := (Cat.Hom.toNatIso (F.mapComp' (f i).op.toLoc r₁.op.toLoc
    m.op.toLoc (by rw [← G₁]; rfl))).symm.app M
  let T₂ := (Cat.Hom.toNatIso (F.mapComp' (f j).op.toLoc r₂.op.toLoc
    m.op.toLoc (by rw [← G₂]; rfl))).symm.app M
  change (T₁.hom ≫ T₂.inv) ≫ T₂.hom = T₁.hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Compose the independently proved source, component, and target equations. -/
theorem assemble_overlap_legs
    {K : Type u} [Category.{v} K]
    {A₁ A₂ B₁ B₂ C₁ C₂ Z : K}
    (N : A₁ ⟶ A₂) (Q : B₁ ⟶ B₂)
    (c₁ : A₁ ⟶ B₁) (c₂ : A₂ ⟶ B₂)
    (k₁ : B₁ ⟶ C₁) (k₂ : B₂ ⟶ C₂)
    (d : C₁ ⟶ C₂) (t₁ : C₁ ⟶ Z) (t₂ : C₂ ⟶ Z)
    (hsource : N ≫ c₂ = c₁ ≫ Q)
    (hcomm : k₁ ≫ d = Q ≫ k₂) (htarget : d ≫ t₂ = t₁) :
    N ≫ (c₂ ≫ k₂ ≫ t₂) = c₁ ≫ k₁ ≫ t₁ := by
  calc
    N ≫ (c₂ ≫ k₂ ≫ t₂) = (N ≫ c₂) ≫ k₂ ≫ t₂ :=
      (Category.assoc N c₂ (k₂ ≫ t₂)).symm
    _ = (c₁ ≫ Q) ≫ k₂ ≫ t₂ :=
      congrArg (fun z : A₁ ⟶ B₂ => z ≫ k₂ ≫ t₂) hsource
    _ = c₁ ≫ (Q ≫ k₂) ≫ t₂ := by simp only [Category.assoc]
    _ = c₁ ≫ (k₁ ≫ d) ≫ t₂ :=
      congrArg (fun z : B₁ ⟶ C₂ => c₁ ≫ z ≫ t₂) hcomm.symm
    _ = c₁ ≫ k₁ ≫ (d ≫ t₂) := by simp only [Category.assoc]
    _ = c₁ ≫ k₁ ≫ t₁ :=
      congrArg (fun z : C₁ ⟶ Z => c₁ ≫ k₁ ≫ z) htarget

noncomputable section

/-- Construct the isomorphism of canonical descent data before specializing the
pseudofunctor. The component and overlap inputs are the ones actually supplied
by the rigidified compatibility proof. -/
def isoOfChosenOverlap
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (M N : F.obj (.mk (Opposite.op S)))
    (e : ∀ i, (F.map (f i).op.toLoc).toFunctor.obj M ≅
      (F.map (f i).op.toLoc).toFunctor.obj N)
    (comm : ∀ i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.map (e i).hom ≫
          ((DescentData'.fromDescentDataFunctor F sq sq₃).obj
            ((F.toDescentData f).obj N)).hom i j =
        ((DescentData'.fromDescentDataFunctor F sq sq₃).obj
          ((F.toDescentData f).obj M)).hom i j ≫
            (F.map (sq i j).p₂.op.toLoc).toFunctor.map (e j).hom) :
    (F.toDescentData f).obj M ≅ (F.toDescentData f).obj N := by
  let e' :
      (DescentData'.fromDescentDataFunctor F sq sq₃).obj
          ((F.toDescentData f).obj M) ≅
        (DescentData'.fromDescentDataFunctor F sq sq₃).obj
          ((F.toDescentData f).obj N) :=
    DescentData'.isoMk (fun i => e i) comm
  exact (DescentData'.descentDataEquivalence F sq sq₃).fullyFaithfulInverse.preimageIso
    (X := (F.toDescentData f).obj M) (Y := (F.toDescentData f).obj N) e'

end

/-- The overlap arrow of the canonical descent datum, after conversion to the
chosen-pullback presentation. Both sides live in the one abstract fibre of F.
The proof unfolds only the constructor/projection chain; F is never specialized.
-/
theorem chosen_canonical_overlap_hom
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (M : F.obj (.mk (op S))) (i j : ι) :
    ((DescentData'.fromDescentDataFunctor F sq sq₃).obj ((F.toDescentData f).obj M)).hom i j =
      (F.mapComp' (f i).op.toLoc (sq i j).p₁.op.toLoc (sq i j).p.op.toLoc
        (by rw [← (sq i j).hp₁]; rfl)).inv.toNatTrans.app M ≫
      (F.mapComp' (f j).op.toLoc (sq i j).p₂.op.toLoc (sq i j).p.op.toLoc
        (by rw [← (sq i j).hp₂]; rfl)).hom.toNatTrans.app M := by
  rfl


/-- The canonical transition pulled through an actual base-change square agrees
with the two canonical legs. The intermediate descent data and its actual κ
commutativity are constructed here, while the pseudofunctor stays abstract. -/
theorem canonical_pullback_leg_relation
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {ι : Type t} {S S' : C} {X X' : ι → C}
    (f : ∀ i, X i ⟶ S) (f' : ∀ i, X' i ⟶ S')
    (p : S' ⟶ S) (p' : ∀ i, X' i ⟶ X i)
    (w : ∀ i, p' i ≫ f i = f' i ≫ p)
    (M : F.obj (.mk (op S)))
    {Y V : C} (d : Y ⟶ S) (m : V ⟶ S') (s : V ⟶ Y)
    (i j : ι) (a₁ : Y ⟶ X i) (a₂ : Y ⟶ X j)
    (r₁ : V ⟶ X' i) (r₂ : V ⟶ X' j)
    (e₁ : a₁ ≫ f i = d) (e₂ : a₂ ≫ f j = d)
    (G₁ : r₁ ≫ f' i = m) (G₂ : r₂ ≫ f' j = m)
    (E₁ : s ≫ a₁ = r₁ ≫ p' i) (E₂ : s ≫ a₂ = r₂ ≫ p' j)
    (hq : s ≫ d = m ≫ p) :
    let N :
        (F.map a₁.op.toLoc ≫ F.map s.op.toLoc).toFunctor.obj
            ((F.map (f i).op.toLoc).toFunctor.obj M) ⟶
          (F.map a₂.op.toLoc ≫ F.map s.op.toLoc).toFunctor.obj
            ((F.map (f j).op.toLoc).toFunctor.obj M) :=
      (F.map s.op.toLoc).toFunctor.map
        ((F.mapComp' (f i).op.toLoc a₁.op.toLoc d.op.toLoc
          (by rw [← e₁]; rfl)).inv.toNatTrans.app M ≫
         (F.mapComp' (f j).op.toLoc a₂.op.toLoc d.op.toLoc
          (by rw [← e₂]; rfl)).hom.toNatTrans.app M)
    let C₁ := (Cat.Hom.toNatIso
      (F.isoMapOfCommSq (CommSq.mk E₁).op.toLoc)).symm.app
        ((F.map (f i).op.toLoc).toFunctor.obj M)
    let C₂ := (Cat.Hom.toNatIso
      (F.isoMapOfCommSq (CommSq.mk E₂).op.toLoc)).symm.app
        ((F.map (f j).op.toLoc).toFunctor.obj M)
    let K₁ := (Cat.Hom.toNatIso
      (F.isoMapOfCommSq (CommSq.mk (w i)).op.toLoc)).symm.app M
    let K₂ := (Cat.Hom.toNatIso
      (F.isoMapOfCommSq (CommSq.mk (w j)).op.toLoc)).symm.app M
    let T₁ := (Cat.Hom.toNatIso (F.mapComp' (f' i).op.toLoc r₁.op.toLoc
      m.op.toLoc (by rw [← G₁]; rfl))).symm.app
        ((F.map p.op.toLoc).toFunctor.obj M)
    let T₂ := (Cat.Hom.toNatIso (F.mapComp' (f' j).op.toLoc r₂.op.toLoc
      m.op.toLoc (by rw [← G₂]; rfl))).symm.app
        ((F.map p.op.toLoc).toFunctor.obj M)
    N ≫ (C₂ ≪≫ (F.map r₂.op.toLoc).toFunctor.mapIso K₂ ≪≫ T₂).hom =
      (C₁ ≪≫ (F.map r₁.op.toLoc).toFunctor.mapIso K₁ ≪≫ T₁).hom := by
  intro N C₁ C₂ K₁ K₂ T₁ T₂
  let D : F.DescentData f := (F.toDescentData f).obj M
  let P : F.DescentData f' :=
    (Pseudofunctor.DescentData.pullFunctor F (f := f) (f' := f')
      (p := p) (p' := p') (α := (fun k : ι => k)) w).obj D
  let Z := (F.map p.op.toLoc).toFunctor.obj M
  let D' : F.DescentData f' := (F.toDescentData f').obj Z
  let κ : F.toDescentData f ⋙
      Pseudofunctor.DescentData.pullFunctor F (f := f) (f' := f')
        (p := p) (p' := p') (α := (fun k : ι => k)) w ≅
      (F.map p.op.toLoc).toFunctor ⋙ F.toDescentData f' :=
    Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F
      (f := f) (f' := f') (p := p) (p' := p') (α := (fun k : ι => k)) w
  let φ : P ⟶ D' := κ.hom.app M
  have hκi := baseChange_hom_component F f f' p (fun k : ι => k) p' w M i
  have hκj := baseChange_hom_component F f f' p (fun k : ι => k) p' w M j
  have hcomm :
      (F.map r₁.op.toLoc).toFunctor.map K₁.hom ≫ D'.hom m r₁ r₂ G₁ G₂ =
        P.hom m r₁ r₂ G₁ G₂ ≫ (F.map r₂.op.toLoc).toFunctor.map K₂.hom :=
    comm_of_component_eq F f' (D₁ := P) (D₂ := D') φ m i j r₁ r₂ G₁ G₂
      K₁.hom K₂.hom hκi hκj
  have hs := pullback_overlap_square F f f' p (fun k : ι => k) p' w D d m s i j
    a₁ a₂ r₁ r₂ e₁ e₂ G₁ G₂ E₁ E₂ hq
  have hc := canonical_overlap_hom F f M d i j a₁ a₂ e₁ e₂
  have hm := congrArg
    (fun γ : (F.map a₁.op.toLoc).toFunctor.obj ((F.map (f i).op.toLoc).toFunctor.obj M) ⟶
        (F.map a₂.op.toLoc).toFunctor.obj ((F.map (f j).op.toLoc).toFunctor.obj M) =>
      (F.map s.op.toLoc).toFunctor.map γ) hc
  have hsource : N ≫ C₂.hom = C₁.hom ≫ P.hom m r₁ r₂ G₁ G₂ :=
    (congrArg
      (fun n : (F.map s.op.toLoc).toFunctor.obj
          ((F.map a₁.op.toLoc).toFunctor.obj ((F.map (f i).op.toLoc).toFunctor.obj M)) ⟶
        (F.map s.op.toLoc).toFunctor.obj
          ((F.map a₂.op.toLoc).toFunctor.obj ((F.map (f j).op.toLoc).toFunctor.obj M)) =>
        n ≫ C₂.hom) hm).symm.trans hs
  have htarget : D'.hom m r₁ r₂ G₁ G₂ ≫ T₂.hom = T₁.hom :=
    canonical_overlap_comp_inverse F f' Z m i j r₁ r₂ G₁ G₂
  change N ≫ (C₂.hom ≫ (F.map r₂.op.toLoc).toFunctor.map K₂.hom ≫ T₂.hom) =
    C₁.hom ≫ (F.map r₁.op.toLoc).toFunctor.map K₁.hom ≫ T₁.hom
  exact assemble_overlap_legs N (P.hom m r₁ r₂ G₁ G₂) C₁.hom C₂.hom
    ((F.map r₁.op.toLoc).toFunctor.map K₁.hom)
    ((F.map r₂.op.toLoc).toFunctor.map K₂.hom)
    (D'.hom m r₁ r₂ G₁ G₂) T₁.hom T₂.hom hsource hcomm htarget


end CategoryTheory.Pseudofunctor.DescentComparison
