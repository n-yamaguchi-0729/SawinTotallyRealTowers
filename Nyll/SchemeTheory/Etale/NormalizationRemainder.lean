/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback


/-!
# The étale complement of the normalization graph

For a quasi-compact separated étale morphism `f : U ⟶ X`, Zariski's main
theorem embeds `U` as an open subscheme of its relative normalization `Y`.
The graph of this embedding in `U ×[X] Y` is both open and closed. Its
complement therefore gives an actual étale scheme over `Y`.

If `f` is surjective, the image of this complementary scheme contains
every point of `Y` outside `U`. This supplies the geometric complement
used in the induction of Stacks, Tag 09Z0:
https://stacks.math.columbia.edu/tag/09Z0

Uniform bounds on geometric fibers, their decrease under specialization,
and finite-stage descent are separate inputs. No finite refinement theorem
or bound is assumed or asserted here.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {U X : Scheme.{u}} (f : U ⟶ X) [QuasiCompact f] [IsSeparated f]

/-- The graph of the canonical map into the relative normalization. -/
def normalizationEtaleGraph : U ⟶ pullback f f.fromNormalization :=
  pullback.lift (𝟙 U) f.toNormalization
    ((Category.id_comp f).trans f.toNormalization_fromNormalization.symm)

/-- The first projection retracts the normalization graph. -/
lemma normalizationEtaleGraph_fst :
    normalizationEtaleGraph f ≫ pullback.fst f f.fromNormalization = 𝟙 U :=
  pullback.lift_fst _ _ _

/-- The second projection of the graph is the canonical normalization map. -/
lemma normalizationEtaleGraph_snd :
    normalizationEtaleGraph f ≫ pullback.snd f f.fromNormalization = f.toNormalization :=
  pullback.lift_snd _ _ _

variable [Etale f]

private theorem isClopen_range_normalizationEtaleGraph :
    IsClopen (Set.range (normalizationEtaleGraph f)) := by
  have : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType f
  have : Etale (normalizationEtaleGraph f ≫ pullback.snd f f.fromNormalization) := by
    rw [normalizationEtaleGraph_snd]
    infer_instance
  have : Etale (normalizationEtaleGraph f) :=
    Etale.of_comp (normalizationEtaleGraph f) (pullback.snd f f.fromNormalization)
  have : IsSplitMono (normalizationEtaleGraph f) :=
    IsSplitMono.mk' ⟨pullback.fst f f.fromNormalization, normalizationEtaleGraph_fst f⟩
  have : IsOpenImmersion (normalizationEtaleGraph f) :=
    IsOpenImmersion.of_flat_of_mono (normalizationEtaleGraph f)
  have : IsClosedImmersion (normalizationEtaleGraph f ≫ pullback.fst f f.fromNormalization) := by
    rw [normalizationEtaleGraph_fst]
    infer_instance
  have : IsClosedImmersion (normalizationEtaleGraph f) :=
    IsClosedImmersion.of_comp (normalizationEtaleGraph f) (pullback.fst f f.fromNormalization)
  exact ⟨(normalizationEtaleGraph f).isClosedEmbedding.isClosed_range,
    IsOpenImmersion.isOpen_range (normalizationEtaleGraph f)⟩

/-- The open complement of the normalization graph. Composing its inclusion
with the second projection is étale by the existing base-change and
composition instances. -/
def etaleNormalizationRemainder : (pullback f f.fromNormalization).Opens :=
  ⟨(Set.range (normalizationEtaleGraph f))ᶜ,
    (isClopen_range_normalizationEtaleGraph f).isClosed.isOpen_compl⟩

/-- The normalization remainder is also closed in the base-changed cover. -/
theorem etaleNormalizationRemainder_isClosed :
    IsClosed (etaleNormalizationRemainder f : Set (pullback f f.fromNormalization : Scheme.{u})) :=
  (isClopen_range_normalizationEtaleGraph f).isOpen.isClosed_compl

/-- The normalization remainder covers the entire boundary of the original
étale source in its normalization. The cover need not be finite étale. -/
theorem normalization_boundary_subset_remainder_image [Surjective f] :
    (Set.range f.toNormalization)ᶜ ⊆
      Set.range ((etaleNormalizationRemainder f).ι ≫ pullback.snd f f.fromNormalization) := by
  intro y hy
  obtain ⟨t, ht⟩ := (pullback.snd f f.fromNormalization).surjective y
  have htV : t ∈ etaleNormalizationRemainder f := by
    rintro ⟨a, ha⟩
    apply hy
    refine ⟨a, ?_⟩
    have hgraph : pullback.snd f f.fromNormalization (normalizationEtaleGraph f a) =
        f.toNormalization a :=
      (Scheme.Hom.comp_apply _ _ a).symm.trans
        (congrArg (fun k : U ⟶ f.normalization => k a) (normalizationEtaleGraph_snd f))
    exact hgraph.symm.trans ((congrArg (pullback.snd f f.fromNormalization) ha).trans ht)
  refine ⟨⟨t, htV⟩, ?_⟩
  exact (Scheme.Hom.comp_apply (etaleNormalizationRemainder f).ι
    (pullback.snd f f.fromNormalization) ⟨t, htV⟩).trans ht

end AlgebraicGeometry.Scheme.Hom
