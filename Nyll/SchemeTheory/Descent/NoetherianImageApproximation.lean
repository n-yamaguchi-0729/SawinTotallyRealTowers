/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionImageLimit
import Nyll.SchemeTheory.Descent.FGSubalgebra
import Nyll.SchemeTheory.Descent.SubalgebraStages_nonempty_isLimit_cone
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FiniteType

/-!
# Proper Noetherian images of a closed subscheme in a fixed ambient model

A closed subscheme of the base change of a proper scheme over a Noetherian
ring is recovered as the limit of its actual images over finitely generated
subalgebras. Every image is proper over its actual Noetherian stage ring.
No finite-presentation hypothesis is imposed on the closed subscheme.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.NoetherianImageApproximation

universe u

variable (A₀ A : Type u) [CommRing A₀] [CommRing A] [Algebra A₀ A]

/-- The exhaustive ordered family of actual finitely generated subalgebras. -/
@[reducible]
def subalgebras : FGSubalgebra A₀ A →o Subalgebra A₀ A where
  toFun B := B.1
  monotone' _ _ h := h

/-- Every element occurs in its actual singleton-generated subalgebra. -/
theorem exhaustive (a : A) : ∃ B, a ∈ subalgebras A₀ A B := by
  classical
  refine ⟨⟨Algebra.adjoin A₀ (↑({a} : Finset A) : Set A),
    Subalgebra.fg_adjoin_finset {a}⟩, ?_⟩
  exact Algebra.subset_adjoin (Finset.mem_singleton_self a)

variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀))

/-- The actual ambient schemes over the finitely generated subalgebras. -/
abbrev ambientDiagram : (FGSubalgebra A₀ A)ᵒᵖ ⥤ Scheme.{u} :=
  SubalgebraStages.diagram (subalgebras A₀ A) f₀

/-- The actual ambient cone with vertex the base change to `A`. -/
abbrev ambientCone : Cone (ambientDiagram A₀ A f₀) :=
  SubalgebraStages.cone (subalgebras A₀ A) f₀

/-- Exhaustiveness of the ring stages gives the actual ambient limit. -/
def ambientConeIsLimit : IsLimit (ambientCone A₀ A f₀) :=
  (SubalgebraStages.nonempty_isLimit_cone (subalgebras A₀ A)
    (exhaustive A₀ A) f₀).some

variable {Z : Scheme.{u}} (j : Z ⟶ (ambientCone A₀ A f₀).pt)

/-- The proper approximation consists of the actual stage images of `j`. -/
abbrev diagram : (FGSubalgebra A₀ A)ᵒᵖ ⥤ Scheme.{u} :=
  AffineTransitionImage.diagram (ambientDiagram A₀ A f₀) (ambientCone A₀ A f₀) j

/-- The cone whose source is the original closed subscheme. -/
abbrev cone : Cone (diagram A₀ A f₀ j) :=
  AffineTransitionImage.cone (ambientDiagram A₀ A f₀) (ambientCone A₀ A f₀) j

/-- The actual map from a stage image to its finitely generated base ring. -/
def baseMap (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    (diagram A₀ A f₀ j).obj i ⟶ Spec (CommRingCat.of i.unop.1) :=
  AffineTransitionImage.inclusion (ambientDiagram A₀ A f₀)
    (ambientCone A₀ A f₀) j i ≫
      pullback.snd f₀ (SubalgebraStages.specHom (subalgebras A₀ A) i.unop)

/-- The actual stage maps commute with the inclusions of their base rings. -/
lemma transition_baseMap {i k : (FGSubalgebra A₀ A)ᵒᵖ} (f : i ⟶ k) :
    (diagram A₀ A f₀ j).map f ≫ baseMap A₀ A f₀ j k =
      baseMap A₀ A f₀ j i ≫
        (SubalgebraStages.specDiagram (subalgebras A₀ A)).map f := by
  change AffineTransitionImage.transition (ambientDiagram A₀ A f₀)
      (ambientCone A₀ A f₀) j f ≫
        (AffineTransitionImage.inclusion (ambientDiagram A₀ A f₀)
          (ambientCone A₀ A f₀) j k ≫ _) = _
  rw [← Category.assoc, AffineTransitionImage.transition_inclusion,
    Category.assoc, SubalgebraStages.diagram_map_snd, ← Category.assoc]
  rfl

/-- The actual image diagram lies over the diagram of spectra of its stage rings. -/
def baseMaps : diagram A₀ A f₀ j ⟶
    SubalgebraStages.specDiagram (subalgebras A₀ A) where
  app i := baseMap A₀ A f₀ j i
  naturality _ _ f := transition_baseMap A₀ A f₀ j f

instance [IsProper f₀] (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    IsProper (baseMap A₀ A f₀ j i) := by
  dsimp only [baseMap]
  infer_instance

instance [IsProper f₀] (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    CompactSpace ((diagram A₀ A f₀ j).obj i) :=
  QuasiCompact.compactSpace_of_compactSpace (baseMap A₀ A f₀ j i)

instance [IsProper f₀] (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    QuasiSeparatedSpace ((diagram A₀ A f₀ j).obj i) :=
  quasiSeparatedSpace_of_quasiSeparated (baseMap A₀ A f₀ j i)

/-- Every actual ring stage is Noetherian. -/
theorem stageRing_isNoetherian [IsNoetherianRing A₀] (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    IsNoetherianRing i.unop.1 := by
  have : Algebra.FiniteType A₀ i.unop.1 :=
    (Subalgebra.fg_iff_finiteType i.unop.1).mp i.unop.2
  exact Algebra.FiniteType.isNoetherianRing A₀ i.unop.1

/-- Every image stage is an actual proper Noetherian scheme. -/
theorem stage_isNoetherian [IsNoetherianRing A₀] [IsProper f₀]
    (i : (FGSubalgebra A₀ A)ᵒᵖ) : IsNoetherian ((diagram A₀ A f₀ j).obj i) := by
  have : IsNoetherianRing i.unop.1 := stageRing_isNoetherian A₀ A i
  have : IsLocallyNoetherian ((diagram A₀ A f₀ j).obj i) :=
    LocallyOfFiniteType.isLocallyNoetherian (baseMap A₀ A f₀ j i)
  exact {}

/-- The original closed subscheme is the limit of the actual proper image stages. -/
def coneIsLimit [IsProper f₀] [IsClosedImmersion j] :
    IsLimit (cone A₀ A f₀ j) :=
  AffineTransitionImage.coneIsLimit (ambientDiagram A₀ A f₀)
    (ambientCone A₀ A f₀) (ambientConeIsLimit A₀ A f₀) j

@[reassoc]
lemma cone_projection_baseMap (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    (cone A₀ A f₀ j).π.app i ≫ baseMap A₀ A f₀ j i =
      j ≫ pullback.snd f₀ (SubalgebraStages.specHomTop (A₀ := A₀) (A := A)) ≫
        SubalgebraStages.specLeg (subalgebras A₀ A) i.unop := by
  rw [baseMap, ← Category.assoc, AffineTransitionImage.cone_projection_inclusion,
    Category.assoc, SubalgebraStages.cone_π_app_snd]

end AlgebraicGeometry.NoetherianImageApproximation
