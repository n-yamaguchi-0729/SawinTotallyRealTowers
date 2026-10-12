/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.LocalCover
public import Nyll.SchemeTheory.WeilRestriction.DirectedCover
public import Nyll.SchemeTheory.WeilRestriction.Restriction
public import Nyll.SchemeTheory.WeilRestriction.GluingData
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Nyll.SchemeTheory.Affine.WeilRestriction.Global

/-!
# Gluing finite étale internal Hom candidates

For finite étale `R`-algebras `A` and `B`, refine the principal open cover
carrying local internal Hom representers to a locally directed open cover.
Pulling back the local representers gives representations of the restrictions
of one fixed presheaf. These representations determine the transition maps and
pullback squares, so the local finite étale schemes glue over `Spec R`.

No global freeness assumption on `A` is used. The representing property of the
glued scheme is a separate sheaf-descent step.
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry
open SchemeTheory.WeilRestriction

noncomputable section

universe u

namespace SchemeTheory.Affine

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [Module.Finite R A] [Algebra.Etale R A]
  [Module.Finite R B] [Algebra.Etale R B]

/-- A locally directed refinement of the principal cover carrying local internal Homs. -/
abbrev finiteEtaleInternalHomDirectedCover : (Spec (CommRingCat.of R)).OpenCover :=
  subordinateOpenCover (finiteEtaleInternalHomOpenCover (R := R) (A := A) (B := B))

/-- Pull back a principal-cover representer to a member of the directed refinement. -/
def finiteEtaleInternalHomDirectedRepresenter
    (i : (finiteEtaleInternalHomDirectedCover (R := R) (A := A) (B := B)).I₀) :
    FiniteEtale ((finiteEtaleInternalHomDirectedCover (R := R) (A := A) (B := B)).X i) :=
  (FiniteEtale.pullback (subordinateOpenCoverRefinementMap
    (finiteEtaleInternalHomOpenCover (R := R) (A := A) (B := B)) i)).obj
      (finiteEtaleInternalHomOpenCoverRepresenter (R := R) (A := A) (B := B)
        (subordinateOpenCoverRefinementIndex
          (finiteEtaleInternalHomOpenCover (R := R) (A := A) (B := B)) i))

/-- Each refined local scheme represents the restriction of the fixed internal Hom presheaf. -/
def finiteEtaleInternalHomDirectedRepresentable
    (i : (finiteEtaleInternalHomDirectedCover (R := R) (A := A) (B := B)).I₀) :
    ((Over.map ((finiteEtaleInternalHomDirectedCover
      (R := R) (A := A) (B := B)).f i)).op ⋙
        globalInternalHomFunctor (R := R) (A := A) (B := B)).RepresentableBy
          ((FiniteEtale.forget ((finiteEtaleInternalHomDirectedCover
            (R := R) (A := A) (B := B)).X i)).obj
              (finiteEtaleInternalHomDirectedRepresenter (R := R) (A := A) (B := B) i)) := by
  let 𝒰 : (Spec (CommRingCat.of R)).OpenCover :=
    finiteEtaleInternalHomOpenCover (R := R) (A := A) (B := B)
  let p : 𝒰.I₀ := subordinateOpenCoverRefinementIndex 𝒰 i
  let g : (subordinateOpenCover 𝒰).X i ⟶ 𝒰.X p :=
    subordinateOpenCoverRefinementMap 𝒰 i
  have hcomp : g ≫ 𝒰.f p =
      (finiteEtaleInternalHomDirectedCover (R := R) (A := A) (B := B)).f i :=
    subordinateOpenCoverRefinementMap_comp 𝒰 i
  let h := representableByRestrictionBaseChange (𝒰.f p) g
    (globalInternalHomFunctor (R := R) (A := A) (B := B))
    ((FiniteEtale.forget (𝒰.X p)).obj
      (finiteEtaleInternalHomOpenCoverRepresenter (R := R) (A := A) (B := B) p))
    (finiteEtaleInternalHomOpenCoverRepresentable (R := R) (A := A) (B := B) p)
  change ((Over.map ((finiteEtaleInternalHomDirectedCover
      (R := R) (A := A) (B := B)).f i)).op ⋙
        globalInternalHomFunctor (R := R) (A := A) (B := B)).RepresentableBy
      ((Over.pullback g).obj
        ((FiniteEtale.forget (𝒰.X p)).obj
          (finiteEtaleInternalHomOpenCoverRepresenter (R := R) (A := A) (B := B) p)))
  simpa only [hcomp] using h

/-- The local universal elements determine relative gluing data over the directed cover. -/
def finiteEtaleInternalHomGluingData :
    (finiteEtaleInternalHomDirectedCover (R := R) (A := A) (B := B)).RelativeGluingData :=
  localRepresenterGluingData
    (globalInternalHomFunctor (R := R) (A := A) (B := B))
    (finiteEtaleInternalHomDirectedCover (R := R) (A := A) (B := B))
    (fun i ↦ (FiniteEtale.forget ((finiteEtaleInternalHomDirectedCover
      (R := R) (A := A) (B := B)).X i)).obj
        (finiteEtaleInternalHomDirectedRepresenter (R := R) (A := A) (B := B) i))
    (fun i ↦ finiteEtaleInternalHomDirectedRepresentable (R := R) (A := A) (B := B) i)

/-- The finite étale scheme obtained by gluing the local internal Hom representers. -/
def finiteEtaleInternalHomGlued : FiniteEtale (Spec (CommRingCat.of R)) where
  toComma := Over.mk (finiteEtaleInternalHomGluingData (R := R) (A := A) (B := B)).toBase
  prop := gluedLocalRepresenter_isFiniteEtale
    (globalInternalHomFunctor (R := R) (A := A) (B := B))
    (finiteEtaleInternalHomDirectedCover (R := R) (A := A) (B := B))
    (fun i ↦ (FiniteEtale.forget ((finiteEtaleInternalHomDirectedCover
      (R := R) (A := A) (B := B)).X i)).obj
        (finiteEtaleInternalHomDirectedRepresenter (R := R) (A := A) (B := B) i))
    (fun i ↦ finiteEtaleInternalHomDirectedRepresentable (R := R) (A := A) (B := B) i)
    (fun i ↦ (finiteEtaleInternalHomDirectedRepresenter (R := R) (A := A) (B := B) i).prop)

end SchemeTheory.Affine
