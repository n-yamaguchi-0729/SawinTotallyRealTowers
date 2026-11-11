/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Logic.Function.ULift
public import Mathlib.RepresentationTheory.Homological.FiniteCyclic
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology
public import Nyll.GaloisCohomology.Cyclic.NormKernelVanishing
public import Nyll.GaloisCohomology.Cyclic.TateComparison
public import Nyll.GaloisCohomology.GroupTheory.RepresentationUniverseLift

/-!
# Integral Tate vanishing and the original cyclic norm

The acting group and the integer coefficient carrier may have independent universes.
The actual native Tate complex of their common lift supplies the cyclic norm calculations.
Removing the carrier lift gives the original action, norm and witnesses. The extensionwise
vanishing condition is compared with the original literal integer Tate condition in universe zero.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace IntegralGroupCohomology.Universe

/-- A generator of the original group generates its explicit universe lift. -/
theorem ulift_generator {G : Type u} [Group G] (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    ∀ x : ULift.{v} G, x ∈ Subgroup.zpowers (ULift.up g) := by
  intro x
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg x.down)
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  apply (MulEquiv.ulift : ULift.{v} G ≃* G).injective
  rw [map_zpow]
  exact hn

/-- Tate vanishing in degree minus one gives a coboundary for each original norm-zero element. -/
theorem normKernel_of_tate_isZero {G : Type u} [Group G] [Fintype G]
    (A : Rep.{v} ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hzero : Limits.IsZero (tate A (-1))) :
    ∀ x : A, A.norm.asHom.hom x = 0 → ∃ y : A, A.ρ g y - y = x := by
  let B : Rep.{max u v} ℤ (ULift.{v} G) := (Rep.universeLiftFunctor ℤ G).obj A
  have hzeroB : Limits.IsZero (IntegralGroupCohomology.tate B (-1)) := hzero
  intro x hx
  have hxB : B.norm.asHom.hom (ULift.up x) = 0 := by
    apply ULift.down_injective
    exact (Rep.universeLiftFunctor_norm_down A x).trans hx
  obtain ⟨y, hy⟩ := IntegralGroupCohomology.normKernel_of_tate_isZero B (ULift.up g)
    (ulift_generator g hg) hzeroB (ULift.up x) hxB
  exact ⟨y.down, congrArg (fun z : B => z.down) hy⟩

/-- Tate vanishing in degree zero makes every element fixed by the generator an original norm. -/
theorem exists_norm_eq_of_tate_isZero {G : Type u} [Group G] [Fintype G]
    (A : Rep.{v} ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hzero : Limits.IsZero (tate A 0)) :
    ∀ x : A, A.ρ g x = x → ∃ y : A, A.norm.asHom.hom y = x := by
  let M := (nativeFunctor G).obj A
  have hg' : ∀ x : ULift.{v} G, x ∈ Subgroup.zpowers (ULift.up g) :=
    ulift_generator g hg
  let : IsCyclic (ULift.{v} G) := CyclicCohomology.isCyclic_of_generator (ULift.up g) hg'
  let : CommGroup (ULift.{v} G) := IsCyclic.commGroup (α := ULift.{v} G)
  let : Subsingleton (tateCohomology M 0) :=
    ModuleCat.subsingleton_of_isZero (M := tate A 0) hzero
  have hnative : Limits.IsZero (tateCohomology M 0) := ModuleCat.isZero_of_subsingleton _
  let S := Rep.FiniteCyclicGroup.normHomCompSub M (ULift.up g)
  have hSzero : Limits.IsZero S.homology :=
    Limits.IsZero.of_iso hnative (TateCohomology.isoFiniteCyclicZero M (ULift.up g) hg').symm
  have hS : S.Exact := S.exact_iff_isZero_homology.mpr hSzero
  intro x hx
  have hxker : S.g (ULift.up x) = 0 := by
    let xM : M := ULift.up x
    change M.ρ (ULift.up g) xM - xM = 0
    apply sub_eq_zero.mpr
    apply ULift.down_injective
    exact (nativeFunctor_ρ_down A g x).trans hx
  obtain ⟨y, hy⟩ := S.moduleCat_exact_iff.mp hS (ULift.up x) hxker
  have hy' : M.norm.asHom.hom y = ULift.up x := hy
  exact ⟨y.down, (nativeFunctor_norm_down A y.down).symm.trans
    (congrArg (fun z : M => z.down) hy')⟩

end IntegralGroupCohomology.Universe

namespace CyclicCohomology

/-- The actual integral Tate vanishing condition for every finite cyclic abstract extension,
with independent universes for the ambient group and the coefficient carrier. -/
def SatisfiesIntegralCyclicNormKernelVanishing {G : Type u} [Group G]
    [TopologicalSpace G] (A : Rep.{v} ℤ G) : Prop :=
  ∀ (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (_hg : ∀ x, x ∈ Subgroup.zpowers g),
      let := hnormal
      let := hfinite
      let := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
      Limits.IsZero
        (IntegralGroupCohomology.Universe.tate
          (extensionFixedRepresentation A K L hLK hnormal) (-1))

/-- In universe zero the integral extensionwise predicate is exactly the original Tate condition. -/
theorem satisfiesIntegralCyclicNormKernelVanishing_iff_original
    {G : Type} [Group G] [TopologicalSpace G] (A : Rep.{0} ℤ G) :
    SatisfiesIntegralCyclicNormKernelVanishing A ↔ SatisfiesCyclicNormKernelVanishing A := by
  constructor
  · intro h K L hLK hnormal hfinite g hg
    let : Fintype (K.toSubgroup ⧸ extensionSubgroup K L hLK) := Fintype.ofFinite _
    exact (IntegralGroupCohomology.Universe.isZero_tate_iff_original
      (extensionFixedRepresentation A K L hLK hnormal) (-1)).mp
        (h K L hLK hnormal hfinite g hg)
  · intro h K L hLK hnormal hfinite g hg sharedNormal sharedFinite sharedFintype
    exact (IntegralGroupCohomology.Universe.isZero_tate_iff_original
      (extensionFixedRepresentation A K L hLK hnormal) (-1)).mpr
        (h K L hLK hnormal hfinite g hg)

end CyclicCohomology
