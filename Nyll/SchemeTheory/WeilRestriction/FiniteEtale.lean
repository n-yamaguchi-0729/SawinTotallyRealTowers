/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Nyll.SchemeTheory.WeilRestriction.Affine
public import Nyll.SchemeTheory.WeilRestriction.BaseChange
public import Nyll.SchemeTheory.WeilRestriction.GluedRepresentable
public import Nyll.SchemeTheory.WeilRestriction.GluingData
public import Nyll.SchemeTheory.WeilRestriction.Sheaf
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!
# Finite étale internal Hom over arbitrary schemes

Restrict two finite étale schemes to the directed cover by all affine opens
of the base. The affine internal Hom representers represent the restrictions
of a single sheaf, by the base change comparison. Their canonical transitions
therefore glue to a finite étale representer over the whole base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace SchemeTheory.WeilRestriction

variable (S : Scheme.{u}) (U V : FiniteEtale S)

/-- The finite etale scheme representing the relative internal Hom of U and V on a chart of
the directed affine cover of S. -/
def finiteEtaleInternalHomCoverRepresenter (i : S.directedAffineCover.I₀) :
    FiniteEtale (S.directedAffineCover.X i) := by
  letI : IsAffine (S.directedAffineCover.X i) :=
    i.2
  exact affineFiniteEtaleInternalHomRepresenter (S.directedAffineCover.X i)
    ((FiniteEtale.pullback (S.directedAffineCover.f i)).obj U)
    ((FiniteEtale.pullback (S.directedAffineCover.f i)).obj V)

/-- The representation of the relative internal Hom restricted to an affine-cover chart by
its finite etale local representer. -/
def finiteEtaleInternalHomCoverRepresentable (i : S.directedAffineCover.I₀) :
    ((Over.map (S.directedAffineCover.f i)).op ⋙
      relativeInternalHomFunctor ((FiniteEtale.forget S).obj U)
        ((FiniteEtale.forget S).obj V)).RepresentableBy
          ((FiniteEtale.forget (S.directedAffineCover.X i)).obj
            (finiteEtaleInternalHomCoverRepresenter S U V i)) := by
  letI : IsAffine (S.directedAffineCover.X i) :=
    i.2
  exact (affineFiniteEtaleInternalHomRepresentable (S.directedAffineCover.X i)
    ((FiniteEtale.pullback (S.directedAffineCover.f i)).obj U)
    ((FiniteEtale.pullback (S.directedAffineCover.f i)).obj V)).ofIso
      (relativeInternalHomBaseChangeIso (S.directedAffineCover.f i)
        ((FiniteEtale.forget S).obj U) ((FiniteEtale.forget S).obj V)).symm

/-- The finite étale scheme representing the relative internal Hom of `U` and `V`. -/
def finiteEtaleInternalHomRepresenter : FiniteEtale S where
  toComma := gluedLocalRepresenter
    (relativeInternalHomFunctor ((FiniteEtale.forget S).obj U) ((FiniteEtale.forget S).obj V))
    S.directedAffineCover
    (fun i ↦ (FiniteEtale.forget (S.directedAffineCover.X i)).obj
      (finiteEtaleInternalHomCoverRepresenter S U V i))
    (fun i ↦ finiteEtaleInternalHomCoverRepresentable S U V i)
  prop := gluedLocalRepresenter_isFiniteEtale
    (relativeInternalHomFunctor ((FiniteEtale.forget S).obj U) ((FiniteEtale.forget S).obj V))
    S.directedAffineCover
    (fun i ↦ (FiniteEtale.forget (S.directedAffineCover.X i)).obj
      (finiteEtaleInternalHomCoverRepresenter S U V i))
    (fun i ↦ finiteEtaleInternalHomCoverRepresentable S U V i)
    (fun i ↦ (finiteEtaleInternalHomCoverRepresenter S U V i).prop)

/-- The constructed finite étale scheme represents internal Hom on all schemes over the base. -/
def finiteEtaleInternalHomRepresentable :
    (relativeInternalHomFunctor ((FiniteEtale.forget S).obj U)
      ((FiniteEtale.forget S).obj V)).RepresentableBy
        ((FiniteEtale.forget S).obj (finiteEtaleInternalHomRepresenter S U V)) :=
  gluedLocalRepresentable
    (relativeInternalHomFunctor ((FiniteEtale.forget S).obj U) ((FiniteEtale.forget S).obj V))
    S.directedAffineCover
    (fun i ↦ (FiniteEtale.forget (S.directedAffineCover.X i)).obj
      (finiteEtaleInternalHomCoverRepresenter S U V i))
    (fun i ↦ finiteEtaleInternalHomCoverRepresentable S U V i)
    (relativeInternalHom_isSheaf Scheme.zariskiTopology
      ((FiniteEtale.forget S).obj U) ((FiniteEtale.forget S).obj V))

/-- Pulling back the representing finite étale scheme represents the pulled-back internal Hom. -/
def finiteEtaleInternalHomBaseChangeRepresentable {S T : Scheme.{u}}
    (f : T ⟶ S) (U V : FiniteEtale S) :
    (relativeInternalHomFunctor
      ((FiniteEtale.forget T).obj ((FiniteEtale.pullback f).obj U))
      ((FiniteEtale.forget T).obj ((FiniteEtale.pullback f).obj V))).RepresentableBy
        ((FiniteEtale.forget T).obj ((FiniteEtale.pullback f).obj
          (finiteEtaleInternalHomRepresenter S U V))) :=
  relativeInternalHomRepresentableBaseChange f
    (U := (FiniteEtale.forget S).obj U) (V := (FiniteEtale.forget S).obj V)
    (W := (FiniteEtale.forget S).obj (finiteEtaleInternalHomRepresenter S U V))
    (finiteEtaleInternalHomRepresentable S U V)

end SchemeTheory.WeilRestriction
