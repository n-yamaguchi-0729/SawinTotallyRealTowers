import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FiniteCyclicLocalUnitsH2
import GaloisCohomology.GroupTheory.PGroupGaloisTower
import GaloisCohomology.Kummer.FiniteGaloisUnitsH2Inflation
import GaloisCohomology.Kummer.FiniteGaloisUnitsCohomologyTransport
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

/-!
# Finite unit cohomology in local Galois p-extensions

Induction on the actual extension degree uses a central prime-order subgroup
of the Galois group. The resulting upper extension is cyclic, so local
reciprocity computes its unit H². The lower extension has smaller degree.
Middle exactness then bounds the cardinality by the product of these two
degrees and proves finiteness at the same time.
-/

open CategoryTheory Module

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology LocalFieldTheory

private theorem finite_natCard_le_mul_of_ker_le_range
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C) (h : g.ker ≤ f.range)
    [Finite A] [Finite C] :
    Finite B ∧ Nat.card B ≤ Nat.card A * Nat.card C := by
  have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have : Finite g.ker := Finite.of_injective
    (AddSubgroup.inclusion h) (AddSubgroup.inclusion_injective h)
  have hFinite : Finite B := g.finite_iff_finite_ker_range.mpr
    ⟨inferInstance, inferInstance⟩
  have hKer : Nat.card g.ker ≤ Nat.card A :=
    (Nat.card_le_card_of_injective (AddSubgroup.inclusion h)
      (AddSubgroup.inclusion_injective h)).trans
      (Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hRange : Nat.card g.range ≤ Nat.card C :=
    Nat.card_le_card_of_injective (fun x : g.range ↦ (x : C)) Subtype.val_injective
  refine ⟨hFinite, ?_⟩
  rw [← g.ker.card_mul_index, AddSubgroup.index_ker]
  exact Nat.mul_le_mul hKer hRange

private theorem finiteCyclicLocalUnitsH2_finite_card
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) = finrank K L := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let e : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ≃+
      Additive Gal(L/K) := finiteCyclicLocalUnitsH2AddEquivGalois K L g hg
  exact ⟨Finite.of_equiv (Additive Gal(L/K)) e.symm.toEquiv,
    (Nat.card_congr e.toEquiv).trans
      ((Nat.card_congr (Additive.toMul : Additive Gal(L/K) ≃ Gal(L/K))).trans
        (IsGalois.card_aut_eq_finrank K L))⟩

/-- Unit-coefficient H² of a finite local Galois p-extension is finite,
with cardinality at most the actual extension degree. -/
theorem finitePGroupLocalUnitsH2_finite_natCard_le_finrank
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hP : IsPGroup p Gal(L/K)) :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ≤ finrank K L := by
  generalize hn : finrank K L = n
  induction n using Nat.strong_induction_on generalizing L with
  | h n ih =>
    rcases subsingleton_or_nontrivial Gal(L/K) with hTrivial | hNontrivial
    · have : Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (isZero_groupCohomology_succ_of_subsingleton
            (Rep.ofAlgebraAutOnUnits K L) 1)
      refine ⟨inferInstance, ?_⟩
      rw [Nat.card_unique, ← hn]
      exact finrank_pos
    · obtain ⟨E, hBaseGalois, _, hBaseP, hCyclic, _, hSmaller, _⟩ :=
        IsGalois.exists_intermediateField_prime_degree_of_isPGroup K L p hP
      obtain ⟨hFiniteBase, hBoundBase⟩ :=
        ih (finrank K E) (hn ▸ hSmaller) E hBaseP rfl
      have hUpper : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits E L) 2) ∧
          Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits E L) 2) = finrank E L := by
        let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
        let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
        have : IsNonarchimedeanLocalField E :=
          finiteExtensionSpectralIsNonarchimedeanLocalField K E
        exact finiteCyclicLocalUnitsH2_finite_card E L
      have : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits E L) 2) := hUpper.1
      let f : groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2 →+
          groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 :=
        (finiteGaloisUnitsH2Inflation K L E).hom.toAddMonoidHom
      let g : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 →+
          groupCohomology (Rep.ofAlgebraAutOnUnits E L) 2 :=
        (finiteGaloisUnitsH2Restriction K L E).hom.toAddMonoidHom
      have hExact : g.ker ≤ f.range :=
        finiteGaloisUnitsH2Restriction_ker_le_inflation_range K L E
      obtain ⟨hFinite, hBound⟩ := finite_natCard_le_mul_of_ker_le_range f g hExact
      refine ⟨hFinite, ?_⟩
      calc
        Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ≤
            Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2) *
              Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits E L) 2) := hBound
        _ ≤ finrank K E * finrank E L := Nat.mul_le_mul hBoundBase hUpper.2.le
        _ = n := (finrank_mul_finrank K E L).trans hn

end ClassFieldTower.Martinet.Shafarevich
