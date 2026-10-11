/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.GeneratedAlgebraLocalization
import Nyll.SchemeTheory.Etale.AffineFiniteSubalgebraRefinement
import Nyll.SchemeTheory.Etale.LocalFactorOpenCover
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Topology.Sets.OpenCover

/-!
# Local factors of the generated model from actual chart subalgebras

An inclusion of an actual chart subalgebra into the generated section ring
gives its literal `Spec` map. The map commutes with the actual coefficient
maps, so the subalgebra's local lifts pull back to the generated chart.

A chosen affine base cover pulls back to an actual open cover by the
corresponding generated charts. Local factors on this cover then supply
local factors of the whole generated model through the original cover.
Only the chosen base charts are used. There is no existence assumption for
a global finite submodule, and no claim that its construction is complete.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.GeneratedAlgebra

variable {X : Scheme.{u}} {A : TopCat.Sheaf CommRingCat.{u} X}
variable (α : X.sheaf ⟶ A)
variable (N : SheafOfModules.Submodule (RelativeSpec.underlyingModule α))

/-- Containment in the actual submodule gives containment in its generated
section algebra. This is the containment supplied by finite QC extension. -/
theorem subalgebra_le_sectionSubring_of_le_submodule (V : X.AffineZariskiSite) :
    let : Algebra Γ(X, V.1) (A.obj.obj (op V.1)) := (α.hom.app (op V.1)).hom.toAlgebra
    ∀ (C : Subalgebra Γ(X, V.1) (A.obj.obj (op V.1))),
      C.toSubmodule ≤ sectionSubmodule α N.toSubmodule (op V.1) →
        C.toSubring ≤ sectionSubring α N.toSubmodule (op V.1) := by
  intro algebra C hC x hx
  exact Subring.subset_closure (Or.inr (hC hx))

variable [(RelativeSpec.underlyingModule α).IsQuasicoherent]
variable [(show X.Modules from N.toSheafOfModules).IsQuasicoherent]

local instance selectedChart_isLocallyDirected :
    ((gluingData α N).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin (gluingData α N)

local instance selectedChart_isOpenImmersion (V : X.AffineZariskiSite) :
    IsOpenImmersion ((gluingData α N).cover.f V) :=
  (gluingData α N).cover.map_prop V

/-- The actual inclusion of a chart subalgebra induces the contravariant
map from the generated chart to its spectrum. -/
def chartToSubalgebra (V : X.AffineZariskiSite) :
    let : Algebra Γ(X, V.1) (A.obj.obj (op V.1)) := (α.hom.app (op V.1)).hom.toAlgebra
    ∀ (C : Subalgebra Γ(X, V.1) (A.obj.obj (op V.1))),
      C.toSubring ≤ sectionSubring α N.toSubmodule (op V.1) →
        ((gluingData α N).functor.obj V ⟶ Spec (CommRingCat.of C)) := by
  intro algebra C hC
  exact Spec.map (CommRingCat.ofHom (Subring.inclusion hC))

/-- The literal inclusion commutes with the original structure coefficients. -/
theorem chartToSubalgebra_comp (V : X.AffineZariskiSite) :
    let : Algebra Γ(X, V.1) (A.obj.obj (op V.1)) := (α.hom.app (op V.1)).hom.toAlgebra
    ∀ (C : Subalgebra Γ(X, V.1) (A.obj.obj (op V.1)))
      (hC : C.toSubring ≤ sectionSubring α N.toSubmodule (op V.1)),
      chartToSubalgebra α N V C hC ≫
          Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) C)) =
        Spec.map ((structureMap α N.toSubmodule).app (op V.1)) := by
  intro algebra C hC
  let R : CommRingCat.{u} := Γ(X, V.1)
  let D : CommRingCat.{u} := (presheaf α N.toSubmodule).obj (op V.1)
  let a : R →+* C := algebraMap R C
  let b : C →+* D := Subring.inclusion hC
  let c : R ⟶ D := (structureMap α N.toSubmodule).app (op V.1)
  have hcomp : b.comp a = c.hom := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    rfl
  have hcat : CommRingCat.ofHom a ≫ CommRingCat.ofHom b = c :=
    CommRingCat.hom_ext hcomp
  exact (Spec.map_comp (CommRingCat.ofHom a) (CommRingCat.ofHom b)).symm.trans
    (congrArg (fun z : R ⟶ D => Spec.map z) hcat)

private theorem chart_toBase (V : X.AffineZariskiSite) :
    (gluingData α N).cover.f V ≫ toBase α N =
      Spec.map ((structureMap α N.toSubmodule).app (op V.1)) ≫ V.2.fromSpec := by
  have h := (gluingData α N).ι_toBase V
  change (gluingData α N).cover.f V ≫ toBase α N =
    (Spec.map ((structureMap α N.toSubmodule).app (op V.1)) ≫ V.2.isoSpec.inv) ≫ V.1.ι at h
  exact h.trans (Category.assoc
    (Spec.map ((structureMap α N.toSubmodule).app (op V.1))) V.2.isoSpec.inv V.1.ι)

/-- Local factors of an actual contained chart subalgebra give local
factors on the generated chart through the original target. -/
theorem chart_locallyFactorsThrough_of_subalgebra
    {U : Scheme.{u}} (f : U ⟶ X) (V : X.AffineZariskiSite) :
    let : Algebra Γ(X, V.1) (A.obj.obj (op V.1)) := (α.hom.app (op V.1)).hom.toAlgebra
    ∀ (C : Subalgebra Γ(X, V.1) (A.obj.obj (op V.1))),
      C.toSubring ≤ sectionSubring α N.toSubmodule (op V.1) →
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) C))).ZariskiLocallyFactorsThrough
          (pullback.snd f V.2.fromSpec) →
        ((gluingData α N).cover.f V ≫ toBase α N).ZariskiLocallyFactorsThrough f := by
  intro algebra C hC hlocal
  let R : CommRingCat.{u} := Γ(X, V.1)
  let D : Scheme.{u} := (gluingData α N).functor.obj V
  let k : Spec R ⟶ X := V.2.fromSpec
  let p : Spec (CommRingCat.of C) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R C))
  let q : D ⟶ Spec R := Spec.map ((structureMap α N.toSubmodule).app (op V.1))
  let m : D ⟶ Spec (CommRingCat.of C) := chartToSubalgebra α N V C hC
  have hmp : m ≫ p = q := chartToSubalgebra_comp α N V C hC
  have hq : q.ZariskiLocallyFactorsThrough (pullback.snd f k) :=
    Eq.mp (congrArg (fun z : D ⟶ Spec R =>
      z.ZariskiLocallyFactorsThrough (pullback.snd f k)) hmp) (hlocal.precomp m)
  have hforget : (q ≫ k).ZariskiLocallyFactorsThrough f :=
    Scheme.Hom.ZariskiLocallyFactorsThrough.of_pullback_snd q f k hq
  have hchart : (gluingData α N).cover.f V ≫ toBase α N = q ≫ k := chart_toBase α N V
  exact Eq.mp (congrArg (fun z : D ⟶ X => z.ZariskiLocallyFactorsThrough f) hchart.symm) hforget

private theorem chart_opensRange (V : X.AffineZariskiSite) :
    toBase α N ⁻¹ᵁ V.1 = ((gluingData α N).cover.f V).opensRange := by
  have h : toBase α N ⁻¹ᵁ V.1.ι.opensRange = ((gluingData α N).cover.f V).opensRange :=
    (gluingData α N).toBase_preimage_eq_opensRange_ι V
  exact (congrArg (fun W : X.Opens => toBase α N ⁻¹ᵁ W)
    (Opens.opensRange_ι V.1)).symm.trans h

/-- A chosen affine base cover gives an actual open cover of the generated
model by exactly its chosen affine charts. -/
def selectedChartCover {ι : Type v} (V : ι → X.AffineZariskiSite)
    (hV : IsOpenCover (fun i : ι => (V i).1)) : Scheme.OpenCover.{v} (scheme α N) where
  I₀ := ι
  X i := (gluingData α N).cover.X (V i)
  f i := (gluingData α N).cover.f (V i)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun i => (gluingData α N).cover.map_prop (V i)⟩
    intro y
    obtain ⟨i, hi⟩ := hV.exists_mem (toBase α N y)
    have hy : y ∈ toBase α N ⁻¹ᵁ (V i).1 := hi
    have hmem : y ∈ ((gluingData α N).cover.f (V i)).opensRange :=
      Eq.mp (congrArg (fun W : (scheme α N).Opens => y ∈ W)
        (chart_opensRange α N (V i))) hy
    obtain ⟨z, hz⟩ := hmem
    exact ⟨i, z, hz⟩

/-- Concrete subalgebras on the chosen affine base cover transfer their
local factors to the whole generated model. A finite QC extension supplies
the actual `N` and the individual containments; their existence is not
assumed by a separate model or effectivity package. -/
theorem locallyFactorsThrough_of_chart_subalgebras
    {U : Scheme.{u}} (f : U ⟶ X) {ι : Type v}
    (V : ι → X.AffineZariskiSite) (hV : IsOpenCover (fun i : ι => (V i).1))
    (C : ∀ i : ι,
      let : Algebra Γ(X, (V i).1) (A.obj.obj (op (V i).1)) :=
        (α.hom.app (op (V i).1)).hom.toAlgebra
      Subalgebra Γ(X, (V i).1) (A.obj.obj (op (V i).1)))
    (hC : ∀ i : ι,
      let : Algebra Γ(X, (V i).1) (A.obj.obj (op (V i).1)) :=
        (α.hom.app (op (V i).1)).hom.toAlgebra
      let D : Subalgebra Γ(X, (V i).1) (A.obj.obj (op (V i).1)) := C i
      D.toSubring ≤ sectionSubring α N.toSubmodule (op (V i).1))
    (hlocal : ∀ i : ι,
      let : Algebra Γ(X, (V i).1) (A.obj.obj (op (V i).1)) :=
        (α.hom.app (op (V i).1)).hom.toAlgebra
      let D : Subalgebra Γ(X, (V i).1) (A.obj.obj (op (V i).1)) := C i
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, (V i).1) D))).ZariskiLocallyFactorsThrough
        (pullback.snd f (V i).2.fromSpec)) :
    (toBase α N).ZariskiLocallyFactorsThrough f :=
  Scheme.Hom.ZariskiLocallyFactorsThrough.of_openCover (toBase α N) f
    (selectedChartCover α N V hV)
    (fun i => chart_locallyFactorsThrough_of_subalgebra α N f (V i) (C i) (hC i) (hlocal i))

end AlgebraicGeometry.Scheme.GeneratedAlgebra
