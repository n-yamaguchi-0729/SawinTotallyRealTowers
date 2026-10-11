/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineIntegralLimit
import Nyll.SchemeTheory.Etale.IntegralRefinement
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.Sets.Opens
import Mathlib.Tactic.Choose


/-!
# Descending local factorizations to an affine finite-FP model

A Zariski-local factorization of the actual integral affine limit map
through a locally finitely presented morphism descends to one of its
finite-FP stages. The finite affine cover and its local maps are descended
using the native affine-transition limit owners. No local maps on overlaps
are glued or required to agree.

The local-factorization input is the predicate already constructed by the
integral-refinement theorem. Applying that theorem to a general integral
source still requires its canonical affine iso connection; this file does
not assert the completed finite-FP refinement theorem or a globalization.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Algebra TopologicalSpace

namespace AlgebraicGeometry.AffineIntegralLimit

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  [Algebra.IsIntegral R B]

private theorem descend_open_factor {U : Scheme.{u}}
    (f : U ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    (i : (FinitePresentationModel R B)ᵒᵖ)
    (V : ((diagram R B).obj i).Opens) (hV : IsAffineOpen V)
    (a : (opensCone (diagram R B) (cone R B) i V).pt ⟶ U)
    (ha : a ≫ f = ((cone R B).π.app i ⁻¹ᵁ V).ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    ∃ (j : Over i) (b : (opensDiagram (diagram R B) i V).obj j ⟶ U),
      b ≫ f = (opensDiagramι (diagram R B) i V).app j ≫ (baseMap R B).app j.left := by
  let D := diagram R B
  let c := cone R B
  let t := baseMap R B
  let E := opensDiagram D i V
  let ec := opensCone D c i V
  let et : E ⟶ (Functor.const (Over i)).obj (Spec (CommRingCat.of R)) :=
    opensDiagramι D i V ≫ (Over.forget i).whiskerLeft t
  have (j : Over i) : IsAffine (E.obj j) := hV.preimage (D.map j.hom)
  have hcompat : ec.π ≫ et = (Functor.const (Over i)).map (a ≫ f) := by
    apply NatTrans.ext
    funext j
    let ι : ec.pt ⟶ c.pt := (c.π.app i ⁻¹ᵁ V).ι
    let ιj : E.obj j ⟶ D.obj j.left := (D.map j.hom ⁻¹ᵁ V).ι
    have hres : ec.π.app j ≫ ιj = ι ≫ c.π.app j.left :=
      Scheme.Hom.resLE_comp_ι _ _
    change ec.π.app j ≫ et.app j = a ≫ f
    calc
      ec.π.app j ≫ et.app j = (ec.π.app j ≫ ιj) ≫ t.app j.left :=
        (Category.assoc _ _ _).symm
      _ = (ι ≫ c.π.app j.left) ≫ t.app j.left :=
        congrArg (fun k : ec.pt ⟶ D.obj j.left => k ≫ t.app j.left) hres
      _ = ι ≫ (c.π.app j.left ≫ t.app j.left) := Category.assoc _ _ _
      _ = ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
        congrArg (fun k : c.pt ⟶ Spec (CommRingCat.of R) => ι ≫ k)
          (projection_comp_base R B j.left)
      _ = a ≫ f := ha.symm
  obtain ⟨j, b, _, hb⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    E et f ec (isLimitOpensCone D c (coneIsLimit R B) i V) a hcompat
  exact ⟨j, b, hb⟩

/-- An existing local factorization of the actual integral affine limit map
through an LFP morphism descends to one finite-FP model stage. -/
theorem exists_stage_locally_factors {U : Scheme.{u}}
    (f : U ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    (hlocal : (Spec.map (CommRingCat.ofHom (algebraMap R B))).ZariskiLocallyFactorsThrough f) :
    ∃ i : (FinitePresentationModel R B)ᵒᵖ,
      ((baseMap R B).app i).ZariskiLocallyFactorsThrough f := by
  classical
  let X := Spec (CommRingCat.of B)
  let g : X ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R B))
  let D := diagram R B
  let c := cone R B
  let t := baseMap R B
  have hrefine (x : X) : ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧
      ∃ a : W.toScheme ⟶ U, a ≫ f = W.ι ≫ g := by
    obtain ⟨V, hx, a, ha⟩ := hlocal x
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hx
    refine ⟨W, hW, hxW, X.homOfLE hWV ≫ a, ?_⟩
    calc
      (X.homOfLE hWV ≫ a) ≫ f = X.homOfLE hWV ≫ (a ≫ f) := Category.assoc _ _ _
      _ = X.homOfLE hWV ≫ (V.ι ≫ g) := congrArg (fun k => X.homOfLE hWV ≫ k) ha
      _ = (X.homOfLE hWV ≫ V.ι) ≫ g := (Category.assoc _ _ _).symm
      _ = W.ι ≫ g := congrArg (fun k => k ≫ g) (Scheme.homOfLE_ι X hWV)
  choose W hWA hWmem a ha using hrefine
  have hWcover : IsOpenCover W := by
    apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hWmem x⟩
  obtain ⟨i, s, V, hV, hVcmp⟩ :=
    Scheme.exists_isOpenCover_and_isAffine D c (coneIsLimit R B) W hWcover hWA
  have hdesc (j : s) :
      ∃ (k : Over i) (b : (opensDiagram D i (V j)).obj k ⟶ U),
        b ≫ f = (opensDiagramι D i (V j)).app k ≫ t.app k.left := by
    let e : (opensCone D c i (V j)).pt ⟶ (W j.val).toScheme :=
      X.homOfLE (hVcmp j).2.ge
    let ι : (opensCone D c i (V j)).pt ⟶ X := (c.π.app i ⁻¹ᵁ V j).ι
    let a' : (opensCone D c i (V j)).pt ⟶ U := e ≫ a j.val
    have he : e ≫ (W j.val).ι = ι := Scheme.homOfLE_ι X (hVcmp j).2.ge
    have ha' : a' ≫ f = (c.π.app i ⁻¹ᵁ V j).ι ≫ g := by
      change a' ≫ f = ι ≫ g
      calc
        a' ≫ f = e ≫ (a j.val ≫ f) := Category.assoc _ _ _
        _ = e ≫ ((W j.val).ι ≫ g) :=
          congrArg (fun k : (W j.val).toScheme ⟶ Spec (CommRingCat.of R) => e ≫ k) (ha j.val)
        _ = (e ≫ (W j.val).ι) ≫ g := (Category.assoc _ _ _).symm
        _ = ι ≫ g :=
          congrArg (fun k : (opensCone D c i (V j)).pt ⟶ X => k ≫ g) he
    exact descend_open_factor f i (V j) (hVcmp j).1 a' ha'
  choose k b hb using hdesc
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  let ρ (j : s) : l ⟶ k j :=
    (hl (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)).some
  refine ⟨l.left, ?_⟩
  intro y
  obtain ⟨j, hj⟩ := hV.exists_mem ((D.map l.hom) y)
  let O : (D.obj l.left).Opens := D.map l.hom ⁻¹ᵁ V j
  let E := opensDiagram D i (V j)
  let d : O.toScheme ⟶ E.obj (k j) := E.map (ρ j)
  let r : O.toScheme ⟶ U := d ≫ b j
  have hι : d ≫ (opensDiagramι D i (V j)).app (k j) =
      O.ι ≫ D.map (ρ j).left :=
    (opensDiagramι D i (V j)).naturality (ρ j)
  have ht : D.map (ρ j).left ≫ t.app (k j).left = t.app l.left :=
    (t.naturality (ρ j).left).trans (Category.comp_id _)
  refine ⟨O, hj, r, ?_⟩
  calc
    r ≫ f = d ≫ (b j ≫ f) := Category.assoc _ _ _
    _ = d ≫ ((opensDiagramι D i (V j)).app (k j) ≫ t.app (k j).left) :=
      congrArg (fun m : E.obj (k j) ⟶ Spec (CommRingCat.of R) => d ≫ m) (hb j)
    _ = (d ≫ (opensDiagramι D i (V j)).app (k j)) ≫ t.app (k j).left :=
      (Category.assoc _ _ _).symm
    _ = (O.ι ≫ D.map (ρ j).left) ≫ t.app (k j).left :=
      congrArg (fun m : O.toScheme ⟶ D.obj (k j).left => m ≫ t.app (k j).left) hι
    _ = O.ι ≫ (D.map (ρ j).left ≫ t.app (k j).left) := Category.assoc _ _ _
    _ = O.ι ≫ t.app l.left :=
      congrArg (fun m : D.obj l.left ⟶ Spec (CommRingCat.of R) => O.ι ≫ m) ht

end AlgebraicGeometry.AffineIntegralLimit
