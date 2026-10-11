/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CategoryTheory_OverTotalPresheaf.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelSubPicGlue.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Over

/-!
# Total presheaves over a slice category

A presheaf on the slice over S determines a presheaf on the original category by collecting
its values over all arrows to S. Fibrewise transport relates their representations, and the
total presheaf is a sheaf when the slice presheaf is a sheaf for the induced topology.
-/

section OverTotalPresheafImplementation

open CategoryTheory Category Opposite

namespace CategoryTheory.Functor

universe w v u

variable {C : Type u} [Category.{v} C] {S : C} (G : (Over S)ᵒᵖ ⥤ Type w)

/-- The total set of presheaf values over all arrows from T to S. -/
abbrev OverTotal (T : C) : Type (max w v) := Σ t : T ⟶ S, G.obj (op (Over.mk t))

variable {G}

lemma map_op_apply_eq_of_left_eq {A B : Over S} (k k' : A ⟶ B)
    (h : k.left = k'.left) (x : G.obj (op B)) :
    G.map k.op x = G.map k'.op x := by
  rw [Over.OverMorphism.ext h]

lemma map_op_apply_eq_self {A : Over S} (k : A ⟶ A) (h : k.left = 𝟙 _) (x : G.obj (op A)) :
    G.map k.op x = x := by
  rw [show k = 𝟙 A from Over.OverMorphism.ext (by simpa using h), op_id, Functor.map_id_apply]

lemma map_op_map_op_apply {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B') (x : G.obj (op B')) :
    G.map k.op (G.map k'.op x) = G.map (k ≫ k').op x := by
  rw [op_comp, Functor.map_comp_apply]

lemma map_op_map_op_apply_eq_self {A B : Over S} (k : A ⟶ B) (k' : B ⟶ A) (h : (k ≫ k').left = 𝟙 _)
    (x : G.obj (op A)) : G.map k.op (G.map k'.op x) = x := by
  rw [map_op_map_op_apply]
  exact map_op_apply_eq_self _ h x

lemma map_op_map_op_map_op_apply_eq_self {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B') (k'' : B' ⟶ A)
    (h : (k ≫ k' ≫ k'').left = 𝟙 _) (x : G.obj (op A)) :
    G.map k.op (G.map k'.op (G.map k''.op x)) = x := by
  rw [map_op_map_op_apply, map_op_map_op_apply]
  exact map_op_apply_eq_self _ (by rw [assoc]; exact h) x

lemma map_op_map_op_apply_eq {A B B' D : Over S} (k : A ⟶ B) (k' : B ⟶ B') (l : A ⟶ D) (l' : D ⟶ B')
    (h : (k ≫ k').left = (l ≫ l').left) (x : G.obj (op B')) :
    G.map k.op (G.map k'.op x) = G.map l.op (G.map l'.op x) := by
  rw [map_op_map_op_apply, map_op_map_op_apply]
  exact map_op_apply_eq_of_left_eq _ _ h x

lemma OverTotal.ext' {T : C} {a b : G.OverTotal T} (h₁ : a.1 = b.1)
    (h₂ : G.map (Over.homMk (𝟙 T) (by simp [h₁]) : Over.mk b.1 ⟶ Over.mk a.1).op a.2 = b.2) :
    a = b := by
  obtain ⟨t, x⟩ := a
  obtain ⟨t', y⟩ := b
  obtain rfl : t = t' := h₁
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  dsimp only at h₂
  rw [← h₂]
  symm
  exact map_op_apply_eq_self _ (by simp) x

variable (G)

/-- The presheaf on C obtained by taking the total set of values over arrows to S. -/
def overTotal : Cᵒᵖ ⥤ Type (max w v) where
  obj T := G.OverTotal T.unop
  map {T T'} φ := TypeCat.ofHom fun a =>
    ⟨φ.unop ≫ a.1, G.map (Over.homMk φ.unop rfl : Over.mk (φ.unop ≫ a.1) ⟶ Over.mk a.1).op a.2⟩
  map_id T := TypeCat.homEquiv.injective (funext fun a =>
    OverTotal.ext' (by simp) (map_op_map_op_apply_eq_self _ _ (by
      change (𝟙 _) ≫ (𝟙 _) = 𝟙 _
      exact id_comp _) _))
  map_comp {T T' T''} φ ψ := TypeCat.homEquiv.injective (funext fun a =>
    OverTotal.ext' (by simp) (map_op_map_op_apply_eq _ _ _ _ (by
      change (𝟙 _) ≫ (ψ.unop ≫ φ.unop) = ψ.unop ≫ φ.unop
      exact id_comp _) _))

@[simp] lemma overTotal_map_fst {T T' : Cᵒᵖ} (φ : T ⟶ T') (a : G.overTotal.obj T) :
    (G.overTotal.map φ a).1 = φ.unop ≫ a.1 := rfl

variable {G}

/-- Transport a total-presheaf element whose base arrow is T.hom to the fibre G(T). -/
def OverTotal.toFibre (T : Over S) (b : G.OverTotal T.left) (hb : b.1 = T.hom) : G.obj (op T) :=
  G.map (Over.homMk (𝟙 T.left) (by simpa using hb) : T ⟶ Over.mk b.1).op b.2

lemma OverTotal.toFibre_congr (T : Over S) {b b' : G.OverTotal T.left}
    (h : b = b') (hb : b.1 = T.hom)
    (hb' : b'.1 = T.hom) : OverTotal.toFibre T b hb = OverTotal.toFibre T b' hb' := by
  subst h; rfl

/-- Include a section of G(T) in the total presheaf over the arrow T.hom. -/
def OverTotal.ofFibre (T : Over S) (x : G.obj (op T)) : G.OverTotal T.left :=
  ⟨T.hom, G.map (Over.homMk (𝟙 T.left) (by simp) : Over.mk T.hom ⟶ T).op x⟩

@[simp] lemma OverTotal.ofFibre_fst (T : Over S) (x : G.obj (op T)) :
    (OverTotal.ofFibre T x).1 = T.hom := rfl

lemma OverTotal.toFibre_ofFibre (T : Over S) (x : G.obj (op T)) :
    OverTotal.toFibre T (OverTotal.ofFibre T x) rfl = x :=
  map_op_map_op_apply_eq_self _ _ (by
    change (𝟙 _) ≫ (𝟙 _) = 𝟙 _
    exact id_comp _) x

lemma OverTotal.ofFibre_toFibre (T : Over S) (b : G.OverTotal T.left) (hb : b.1 = T.hom) :
    OverTotal.ofFibre T (OverTotal.toFibre T b hb) = b :=
  OverTotal.ext' (by simpa using hb.symm) (map_op_map_op_map_op_apply_eq_self _ _ _ (by
    change (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _) = 𝟙 _
    rw [id_comp, id_comp]) _)

lemma OverTotal.toFibre_naturality {T T' : Over S} (φ : T ⟶ T')
    (b : G.OverTotal T'.left) (hb : b.1 = T'.hom)
    (hb' : (G.overTotal.map φ.left.op b).1 = T.hom) :
    OverTotal.toFibre T (G.overTotal.map φ.left.op b) hb' =
      G.map φ.op (OverTotal.toFibre T' b hb) :=
  map_op_map_op_apply_eq _ _ _ _ (by
    change (𝟙 _) ≫ φ.left = φ.left ≫ (𝟙 _)
    exact (id_comp _).trans (comp_id _).symm) _

namespace RepresentableBy

variable {Y : C} (e : G.overTotal.RepresentableBy Y)

/-- The arrow from the representing object to S determined by its universal
 total-presheaf element. -/
def overTotalBase : Y ⟶ S := (e.homEquiv (𝟙 Y)).1

lemma overTotal_homEquiv_fst {T : C} (k : T ⟶ Y) : (e.homEquiv k).1 = k ≫ e.overTotalBase := by
  have h := e.homEquiv_comp k (𝟙 Y)
  rw [comp_id] at h
  rw [h]
  rfl

/-- A representation of the total presheaf induces a representation of G by the
 representing object over S. -/
noncomputable def ofOverTotal : G.RepresentableBy (Over.mk e.overTotalBase) where
  homEquiv {T} :=
    { toFun := fun g => OverTotal.toFibre T (e.homEquiv g.left)
        (by rw [overTotal_homEquiv_fst]; exact Over.w g)
      invFun := fun x => Over.homMk (e.homEquiv.symm (OverTotal.ofFibre T x)) (by
        have h := e.overTotal_homEquiv_fst (e.homEquiv.symm (OverTotal.ofFibre T x))
        exact h.symm.trans
          (congrArg Sigma.fst (e.homEquiv.apply_symm_apply (OverTotal.ofFibre T x))))
      left_inv := fun g => by
        apply Over.OverMorphism.ext
        simp only [Over.homMk_left]
        apply e.homEquiv.injective
        exact (e.homEquiv.apply_symm_apply _).trans
          (OverTotal.ofFibre_toFibre T (e.homEquiv g.left) _)
      right_inv := fun x =>
        (OverTotal.toFibre_congr T
          (e.homEquiv.apply_symm_apply (OverTotal.ofFibre T x)) _ rfl).trans
          (OverTotal.toFibre_ofFibre T x) }
  homEquiv_comp {T T'} φ g := by
    have hg : (e.homEquiv g.left).1 = T'.hom := by
      rw [overTotal_homEquiv_fst]; exact Over.w g
    have hφg : (e.homEquiv (φ ≫ g).left).1 = T.hom := by
      rw [overTotal_homEquiv_fst]; exact Over.w (φ ≫ g)
    have hb' : (G.overTotal.map φ.left.op (e.homEquiv g.left)).1 = T.hom := by
      rw [overTotal_map_fst, overTotal_homEquiv_fst, Quiver.Hom.unop_op, ← assoc]
      exact Over.w (φ ≫ g)
    calc OverTotal.toFibre T (e.homEquiv (φ ≫ g).left) hφg
        = OverTotal.toFibre T (G.overTotal.map φ.left.op (e.homEquiv g.left)) hb' :=
          OverTotal.toFibre_congr T (e.homEquiv_comp φ.left g.left) hφg hb'
      _ = G.map φ.op (OverTotal.toFibre T' (e.homEquiv g.left) hg) :=
          OverTotal.toFibre_naturality φ _ hg hb'

end RepresentableBy

end CategoryTheory.Functor

end OverTotalPresheafImplementation

universe w v u

namespace CategoryTheory.Functor

open CategoryTheory Category Opposite

variable {C : Type u} [Category.{v} C] {S : C} {G : (Over S)ᵒᵖ ⥤ Type w}

lemma map_op_map_op_apply_eq_map_op {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B') (l : A ⟶ B')
    (h : (k ≫ k').left = l.left) (x : G.obj (op B')) :
    G.map k.op (G.map k'.op x) = G.map l.op x := by
  rw [map_op_map_op_apply]
  exact map_op_apply_eq_of_left_eq _ _ h x

lemma OverTotal.ofFibre_mk {T : C} (s : T ⟶ S) (x : G.obj (op (Over.mk s))) :
    OverTotal.ofFibre (Over.mk s) x = ⟨s, x⟩ :=
  OverTotal.ext' rfl (map_op_map_op_apply_eq_self _ _ (by
      change (𝟙 _) ≫ (𝟙 _) = 𝟙 _
      exact id_comp _) _)

variable (G)

theorem overTotal_isSheaf (J : GrothendieckTopology C) [J.Subcanonical]
    (hG : Presieve.IsSheaf (J.over S) G) : Presieve.IsSheaf J G.overTotal := by
  intro T R hR x hx
  have hS : Presieve.IsSheaf J (yoneda.obj S) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  rw [Presieve.compatible_iff_sieveCompatible] at hx
  let x₁ : Presieve.FamilyOfElements (yoneda.obj S) R.arrows := fun T' f hf => (x f hf).1
  have hx₁ : x₁.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro T' T'' f g hf
    change (x (g ≫ f) _).1 = g ≫ (x f hf).1
    rw [hx f g hf]
    rfl
  obtain ⟨t, ht, ht'⟩ := (hS R hR) x₁ hx₁
  have hfst : ∀ {T' : C} (f : T' ⟶ T) (hf : R f), (x f hf).1 = f ≫ t := fun f hf => (ht f hf).symm
  let R' : Sieve (Over.mk t) := (Sieve.overEquiv (Over.mk t)).symm R
  have hR' : R' ∈ (J.over S) (Over.mk t) := J.overEquiv_symm_mem_over _ _ hR
  let y : Presieve.FamilyOfElements G R'.arrows := fun A g hg =>
    OverTotal.toFibre A (x g.left hg) ((hfst g.left hg).trans (Over.w g))
  have hy : y.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro A A' g k hg
    have hk : (G.overTotal.map k.left.op (x g.left hg)).1 = A'.hom := by
      rw [overTotal_map_fst, Quiver.Hom.unop_op]
      calc
        k.left ≫ (x g.left hg).1 = k.left ≫ (g.left ≫ t) :=
          congrArg (k.left ≫ ·) (hfst g.left hg)
        _ = A'.hom := by rw [← assoc]; exact Over.w (k ≫ g)
    calc OverTotal.toFibre A' (x (k ≫ g).left (R'.downward_closed hg k)) _
        = OverTotal.toFibre A' (G.overTotal.map k.left.op (x g.left hg)) hk :=
          OverTotal.toFibre_congr A' (hx g.left k.left hg) _ _
      _ = G.map k.op (OverTotal.toFibre A (x g.left hg) _) := OverTotal.toFibre_naturality k _ _ hk
  obtain ⟨z, hz, hz'⟩ := (hG R' hR') y hy
  refine ⟨⟨t, z⟩, ?_, ?_⟩
  · intro T' f hf
    have hzg := hz (Over.homMk f rfl : Over.mk (f ≫ t) ⟶ Over.mk t) hf
    rw [show G.overTotal.map f.op ⟨t, z⟩ = OverTotal.ofFibre (Over.mk (f ≫ t))
        (G.map (Over.homMk f rfl : Over.mk (f ≫ t) ⟶ Over.mk t).op z)
          from (OverTotal.ofFibre_mk _ _).symm, hzg]
    exact OverTotal.ofFibre_toFibre _ _ _
  · rintro ⟨t', z'⟩ ha
    obtain rfl : t' = t := ht' t' (fun T' f hf => congrArg Sigma.fst (ha f hf))
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply hz'
    intro A g hg
    have h1 : (G.overTotal.map g.left.op ⟨t', z'⟩).1 = A.hom := by
      change g.left ≫ t' = A.hom
      exact Over.w g
    calc G.map g.op z'
        = OverTotal.toFibre A (G.overTotal.map g.left.op ⟨t', z'⟩) h1 :=
          (map_op_map_op_apply_eq_map_op _ _ _ (by
            change (𝟙 A.left) ≫ g.left = g.left
            simp) _).symm
      _ = y g hg := OverTotal.toFibre_congr A (ha g.left hg) _ _

end CategoryTheory.Functor
