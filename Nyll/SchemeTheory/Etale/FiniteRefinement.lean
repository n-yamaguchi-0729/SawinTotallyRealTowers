/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.IntegralRefinement
import Nyll.SchemeTheory.Etale.AffineChartFiniteSubalgebra
import Nyll.SchemeTheory.Modules.DirectImageAlgebraQuasicoherent
import Nyll.SchemeTheory.Modules.GeneratedAlgebraSource
import Nyll.SchemeTheory.Modules.GeneratedAlgebraLocalFactors
import Nyll.SchemeTheory.Modules.GeneratedFiniteAlgebra
import Nyll.SchemeTheory.Modules.FiniteAffineSectionSubmodule
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.Topology.Sets.OpenCover
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite surjective refinements over a qcqs base

Start with the original surjective étale morphism. Its integral refinement
supplies both the actual integral cover and its local factorizations.
On finitely many affine base charts, finite subalgebras inside its actual
direct-image algebra retain these factorizations. The proved finite
quasicoherent submodule theorem contains all these actual section modules
at once. Its generated relative algebra gives the finite model.

The original integral source maps to this model, proving surjectivity.
The literal chart subalgebra inclusions transfer the local factorizations
to the model's native open cover. No finite-presentation conclusion is
asserted or required for this finite refinement.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A surjective étale morphism over a quasi-compact quasi-separated scheme
has a finite surjective refinement which Zariski locally factors through
the original cover. The cover source need not be quasi-compact or separated. -/
theorem Etale.exists_finite_refinement
    {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : U ⟶ X) [Etale f] [Surjective f] :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ X),
      IsFinite q ∧ Surjective q ∧ q.ZariskiLocallyFactorsThrough f := by
  classical
  obtain ⟨T, g, hgIntegral, hgSurjective, hgLocal⟩ := Etale.exists_integral_refinement f
  have : IsIntegralHom g := hgIntegral
  have : Surjective g := hgSurjective
  let A : TopCat.Sheaf CommRingCat.{u} X := Scheme.DirectImageAlgebra.sheaf g
  let α : X.sheaf ⟶ A := Scheme.DirectImageAlgebra.structureMap g
  let F : X.Modules := Scheme.RelativeSpec.underlyingModule α
  have : F.IsQuasicoherent := Scheme.DirectImageAlgebra.isQuasicoherent_underlyingModule g
  have hCover : IsOpenCover (fun W : X.AffineZariskiSite => W.1) :=
    iSup_affineOpens_eq_top X
  obtain ⟨s, hs⟩ := hCover.exists_finite_of_compactSpace
  let V : s → X.AffineZariskiSite := fun i => i.val
  let R (i : s) : CommRingCat.{u} := Γ(X, (V i).1)
  let B (i : s) : CommRingCat.{u} := A.obj.obj (op (V i).1)
  let (i : s) : Algebra (R i) (B i) := (α.hom.app (op (V i).1)).hom.toAlgebra
  have hChart (i : s) :
      ∃ C : Subalgebra (R i) (B i), Module.Finite (R i) C ∧
        (Spec.map (CommRingCat.ofHom (algebraMap (R i) C))).ZariskiLocallyFactorsThrough
          (pullback.snd f (V i).2.fromSpec) :=
    Scheme.Hom.ZariskiLocallyFactorsThrough.exists_finite_subalgebra_on_affine
      g f hgLocal (V i)
  choose C hCFinite hCLocal using hChart
  let K (i : s) : Submodule (X.ringCatSheaf.obj.obj (op (V i).1))
      (F.val.obj (op (V i).1)) := by
    change Submodule (R i) (B i)
    exact (C i).toSubmodule
  have hK (i : s) : (K i).FG := by
    change (C i).toSubmodule.FG
    exact (Module.Finite.iff_fg (N := (C i).toSubmodule)).mp (hCFinite i)
  obtain ⟨N, hNQC, hNFinite, hN⟩ :=
    Scheme.Modules.exists_finite_quasicoherent_submodule_containing_affine_sections
      (show SheafOfModules.{u} X.ringCatSheaf from F) V K hK
  have : (show X.Modules from N.toSheafOfModules).IsQuasicoherent := hNQC
  let Y : Scheme.{u} := Scheme.GeneratedAlgebra.scheme α N
  let q : Y ⟶ X := Scheme.GeneratedAlgebra.toBase α N
  have hIntegral (W : X.AffineZariskiSite) : (α.hom.app (op W.1)).hom.IsIntegral :=
    g.isIntegral_app W.1 W.2
  have hFinite : IsFinite q := Scheme.GeneratedAlgebra.isFinite_toBase α N hIntegral hNFinite
  have hSurjective : Surjective q := Scheme.DirectImageAlgebra.surjective_toBase g N
  have hContained (i : s) : (C i).toSubring ≤
      Scheme.GeneratedAlgebra.sectionSubring α N.toSubmodule (op (V i).1) := by
    apply Scheme.GeneratedAlgebra.subalgebra_le_sectionSubring_of_le_submodule α N (V i) (C i)
    exact hN i
  have hLocal : q.ZariskiLocallyFactorsThrough f :=
    Scheme.GeneratedAlgebra.locallyFactorsThrough_of_chart_subalgebras α N f V hs
      C hContained hCLocal
  exact ⟨Y, q, hFinite, hSurjective, hLocal⟩

end AlgebraicGeometry
