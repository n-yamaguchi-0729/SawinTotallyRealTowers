import GaloisCohomology.Cyclic.TateComparison
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

set_option autoImplicit false
/-!
# Degree-two cohomology and degree-zero Tate cohomology for a finite cyclic group

For a chosen generator of a finite cyclic group, Mathlib computes positive
even group cohomology and degree-zero Tate cohomology by the same periodic
short complex.  This file records the resulting comparison in degree two.

The comparison is normalized by the supplied generator.  No
choice-independence assertion is made here.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

private theorem finiteCyclicH2IsCyclicOfGenerator
    {G : Type u} [Group G] (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    IsCyclic G := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨g, ?_⟩
  ext x
  constructor
  · intro _
    exact Subgroup.mem_top x
  · intro _
    exact hg x

/-- For a finite cyclic group with a specified generator, ordinary
degree-two group cohomology is the degree-zero Tate cohomology object.

Both legs use the same standard short complex
`A --N--> A --(ρ(g)-1)--> A`.
-/
noncomputable def finiteCyclicGroupH2IsoTateHZero
    {R G : Type u} [CommRing R] [Group G] [Fintype G]
    (A : Rep R G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    groupCohomology A 2 ≅ tateCohomology A 0 := by
  letI : IsCyclic G := finiteCyclicH2IsCyclicOfGenerator g hg
  letI : CommGroup G := IsCyclic.commGroup
  exact
    Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 (by decide) ≪≫
      (TateCohomology.isoFiniteCyclicZero A g hg).symm

/-- The finite-cyclic `H² ≅ Tate H⁰` comparison sends the periodic
quotient class represented by a generator-fixed coefficient to the same
representative in the Tate short complex. -/
@[simp]
theorem finiteCyclicGroupH2IsoTateHZero_groupCohomologyπEven
    {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
    (A : Rep R G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker
      (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    (finiteCyclicGroupH2IsoTateHZero A g hg).hom
        (Rep.FiniteCyclicGroup.groupCohomologyπEven
          A g hg 2 (by decide) a) =
      (TateCohomology.isoFiniteCyclicZero A g hg).inv
        ((Rep.FiniteCyclicGroup.normHomCompSub A g).homologyπ
          ((Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatCyclesIso.inv
            a)) := by
  let e := Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 (by decide)
  let z := (Rep.FiniteCyclicGroup.normHomCompSub A g).homologyπ
    ((Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatCyclesIso.inv a)
  change (TateCohomology.isoFiniteCyclicZero A g hg).inv (e.hom (e.inv z)) =
    (TateCohomology.isoFiniteCyclicZero A g hg).inv z
  exact congrArg (fun x => (TateCohomology.isoFiniteCyclicZero A g hg).inv x)
    (CategoryTheory.Iso.inv_hom_id_apply e z)

end

end ClassFieldTower.Cohomology
