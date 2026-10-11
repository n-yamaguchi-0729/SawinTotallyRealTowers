/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.CommAlgRingMap
import Nyll.SchemeTheory.RingTheory.Ramification.NativeResidueAction
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Topology.Algebra.MulAction

/-!
# The native residue epimorphism from an actual algebra object

The coefficient map and its action are those stored in the native algebra
object. Coefficient fixedness, fixed-element descent, and open stabilizers
supply the actual compact residue-lift theorem. Its surjectivity proves a
categorical epimorphism; none of these conclusions are input data.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory CategoryTheory

universe u v

/-- The ordinary group-category implication, with coercions confined to groups. -/
theorem nativeGroupMorphism_epi_of_surjective {D H : GrpCat.{v}}
    (f : GrpCat.Hom D H) (hf : Function.Surjective f.hom'.toFun) :
    Epi (C := GrpCat.{v}) (X := D) (Y := H) f :=
  (GrpCat.epi_iff_surjective f).mpr hf

/-- The converse uses the existing native group-category theorem. -/
theorem nativeGroupMorphism_surjective_of_epi {D H : GrpCat.{v}}
    (f : GrpCat.Hom D H) [Epi (C := GrpCat.{v}) (X := D) (Y := H) f] :
    Function.Surjective f.hom'.toFun :=
  GrpCat.surjective_of_epi f

private theorem coefficientFixed_smulCommClass
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A)
    (G : Type v) [Group G] [MulSemiringAction G R]
    (hbase : ∀ g : G, (MulSemiringAction.toRingHom G R g).comp
      (commAlgCoefficientMap R) = commAlgCoefficientMap R) : SMulCommClass G A R := by
  constructor
  intro g a b
  have hg : g • algebraMap A R a = algebraMap A R a :=
    congrArg (fun f : A →+* R => f.toFun a) (hbase g)
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hg]

private theorem fixedCoefficient_isInvariant
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A)
    (G : Type v) [Group G] [MulSemiringAction G R]
    (hinv : ∀ b : R, (∀ g : G, g • b = b) →
      ∃ a : A, (commAlgCoefficientMap R).toFun a = b) : Algebra.IsInvariant A R G := by
  constructor
  intro b hb
  exact hinv b hb

private theorem fixedSet_continuousSMul
    {G X : Type v} [Group G] [MulAction G X]
    [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [DiscreteTopology X]
    (hopen : ∀ x : X, IsOpen (fun g : G => g • x = x)) : ContinuousSMul G X :=
  continuousSMul_iff_stabilizer_isOpen.mpr hopen

/-- The actual contraction along the stored native coefficient map. -/
def nativeAlgebraResidueBaseIdeal {A : Type u} [CommRing A]
    (R : CommAlgCat.{v} A) (q : Ideal R) : Ideal A := q.under A

private theorem nativeAlgebraResidueBaseIdeal_liesOver
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A) (q : Ideal R) :
    q.LiesOver (nativeAlgebraResidueBaseIdeal R q) := by
  change q.LiesOver (q.under A)
  infer_instance

/-- The actual quotient-algebra automorphism group over the contracted prime. -/
def nativeAlgebraResidueAutomorphisms {A : Type u} [CommRing A]
    (R : CommAlgCat.{v} A) (q : Ideal R) : GrpCat.{v} := by
  have : q.LiesOver (nativeAlgebraResidueBaseIdeal R q) :=
    nativeAlgebraResidueBaseIdeal_liesOver R q
  exact nativeResidueAutomorphisms A R (nativeAlgebraResidueBaseIdeal R q) q

/-- The literal native residue-action map for the stored coefficient action. -/
def nativeAlgebraResidueMorphism {A : Type u} [CommRing A]
    (R : CommAlgCat.{v} A) (G : Type v) [Group G] [MulSemiringAction G R]
    (q : Ideal R)
    (hbase : ∀ g : G, (MulSemiringAction.toRingHom G R g).comp
      (commAlgCoefficientMap R) = commAlgCoefficientMap R) :
    GrpCat.Hom (nativeResidueStabilizer R G q) (nativeAlgebraResidueAutomorphisms R q) := by
  have : SMulCommClass G A R := coefficientFixed_smulCommClass R G hbase
  have : q.LiesOver (nativeAlgebraResidueBaseIdeal R q) :=
    nativeAlgebraResidueBaseIdeal_liesOver R q
  exact nativeResidueStabilizerMorphism A R G (nativeAlgebraResidueBaseIdeal R q) q

/-- The actual residue map is epic, by the proved compact residue lift. -/
theorem nativeAlgebraResidueMorphism_epi
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A)
    (G : Type v) [Group G] [MulSemiringAction G R]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup G] (q : Ideal R) [q.IsPrime]
    (hbase : ∀ g : G, (MulSemiringAction.toRingHom G R g).comp
      (commAlgCoefficientMap R) = commAlgCoefficientMap R)
    (hinv : ∀ b : R, (∀ g : G, g • b = b) →
      ∃ a : A, (commAlgCoefficientMap R).toFun a = b)
    (hopen : ∀ b : R, IsOpen (fun g : G => g • b = b)) :
    Epi (C := GrpCat.{v}) (X := nativeResidueStabilizer R G q)
      (Y := nativeAlgebraResidueAutomorphisms R q)
      (nativeAlgebraResidueMorphism R G q hbase) := by
  have : SMulCommClass G A R := coefficientFixed_smulCommClass R G hbase
  have : Algebra.IsInvariant A R G := fixedCoefficient_isInvariant R G hinv
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have : ContinuousSMul G R := fixedSet_continuousSMul hopen
  have : q.LiesOver (nativeAlgebraResidueBaseIdeal R q) :=
    nativeAlgebraResidueBaseIdeal_liesOver R q
  apply nativeGroupMorphism_epi_of_surjective
  change Function.Surjective
    (nativeResidueStabilizerHom A R G (nativeAlgebraResidueBaseIdeal R q) q).toFun
  exact nativeResidueStabilizerHom_surjective A R G (nativeAlgebraResidueBaseIdeal R q) q

/-- The image in the original group of the actual residue-map kernel. -/
def nativeAlgebraResidueKernelImage
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A)
    (G : Type v) [Group G] [MulSemiringAction G R] (q : Ideal R)
    (hbase : ∀ g : G, (MulSemiringAction.toRingHom G R g).comp
      (commAlgCoefficientMap R) = commAlgCoefficientMap R) : Subgroup G :=
  (nativeAlgebraResidueMorphism R G q hbase).hom'.ker.map
    (nativeResidueStabilizerInclusion R G q)

/-- The computed kernel image is the literal native inertia subgroup. -/
theorem nativeAlgebraResidueKernelImage_eq_inertia
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A)
    (G : Type v) [Group G] [MulSemiringAction G R] (q : Ideal R)
    (hbase : ∀ g : G, (MulSemiringAction.toRingHom G R g).comp
      (commAlgCoefficientMap R) = commAlgCoefficientMap R) :
    nativeAlgebraResidueKernelImage R G q hbase = q.inertia G := by
  have : SMulCommClass G A R := coefficientFixed_smulCommClass R G hbase
  have : q.LiesOver (nativeAlgebraResidueBaseIdeal R q) :=
    nativeAlgebraResidueBaseIdeal_liesOver R q
  exact nativeResidueStabilizerHom_map_ker A R G (nativeAlgebraResidueBaseIdeal R q) q

end EtaleFundamentalGroups.Inertia
