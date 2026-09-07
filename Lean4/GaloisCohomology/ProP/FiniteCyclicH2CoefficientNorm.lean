import GaloisCohomology.ProP.FiniteCyclicCarryCoefficientNorm
import GaloisCohomology.ProP.FiniteCyclicBarPeriodicH2Comparison
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Homology.ShortComplex.Homology
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Rep.Basic

set_option autoImplicit false

/-!
# Norm preimages kill a cyclic H² coefficient map

Every even cyclic cohomology class has a generator-fixed representative.
If the coefficient image of every such representative has an actual norm
preimage, the entire induced degree-two map vanishes.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

universe u

/-- Every cyclic degree-two cohomology class has a generator-fixed
representative under the periodic quotient map. -/
theorem finiteCyclicGroupH2_piEven_surjective
    {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
    (A : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Function.Surjective
      (Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 (by decide)) := by
  let S : ShortComplex (ModuleCat R) := Rep.FiniteCyclicGroup.normHomCompSub A g
  let e : groupCohomology A 2 ≅ S.homology :=
    Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 (by decide)
  have hπ : Function.Surjective S.homologyπ :=
    (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance
  intro x
  obtain ⟨y, hy⟩ := hπ (e.hom x)
  refine ⟨S.moduleCatCyclesIso.hom y, ?_⟩
  change e.inv
    (S.homologyπ (S.moduleCatCyclesIso.inv (S.moduleCatCyclesIso.hom y))) = x
  have hCycles : S.moduleCatCyclesIso.inv (S.moduleCatCyclesIso.hom y) = y :=
    S.moduleCatCyclesIso.toLinearEquiv.symm_apply_apply y
  exact (congrArg (fun z : S.cycles ↦ e.inv (S.homologyπ z)) hCycles).trans
    ((congrArg (fun z : S.homology ↦ e.inv z) hy).trans
      (e.toLinearEquiv.symm_apply_apply x))

/-- Actual norm preimages for generator-fixed elements make the entire
degree-two coefficient map zero. -/
theorem finiteCyclicH2_coefficientMap_eq_zero_of_norm
    {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
    (A B : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (φ : A ⟶ B)
    (hNorm : ∀ a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap,
      ∃ b : B, B.norm.hom b = φ.hom a.1) :
    groupCohomology.map (MonoidHom.id G) φ 2 = 0 := by
  ext x
  obtain ⟨a, rfl⟩ := finiteCyclicGroupH2_piEven_surjective A g hg x
  obtain ⟨b, hb⟩ := hNorm a
  rw [← H2π_finiteCyclicCarryTwoCocycle A g hg a]
  exact finiteCyclicCarry_coefficientMap_eq_zero_of_norm A B g hg φ a b hb

end ClassFieldTower.Cohomology
