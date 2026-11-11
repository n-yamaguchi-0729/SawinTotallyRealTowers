/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.Herbrand.Induced
public import Nyll.GaloisCohomology.Cyclic.IntegralShapiro
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseShapiro
public import Nyll.GaloisCohomology.Cyclic.IntegralShapiroComparison
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Shapiro for the multiplicative induced local blocks

The concrete equivariant-function module used by the local idele block
decomposition has exactly Mathlib's coinduced action after applying
`Additive`.  This file supplies the representation isomorphism and hence
Shapiro in all degrees, for arbitrary ambient groups and subgroups.
-/

@[expose] public section

open CategoryTheory

noncomputable section

namespace ClassFieldTower.Cohomology

open CyclicCohomology

universe u v

section Representation

variable {G : Type u} [Group G] (H : Subgroup G)
variable (B : Type v) [CommGroup B] [MulDistribMulAction H B]

/-- The multiplicative equivariant-function induced module used by the
local idele blocks is Mathlib's coinduced additive representation. -/
noncomputable def multiplicativeInducedRepIsoCoind :
    Rep.ofMulDistribMulAction G (InducedModule (B := B) H) ≅
      Rep.coind H.subtype (Rep.ofMulDistribMulAction H B) := by
  let e : Additive (InducedModule (B := B) H) ≃+
      Rep.coind H.subtype (Rep.ofMulDistribMulAction H B) :=
    { toFun := fun f ↦ ⟨fun x ↦ Additive.ofMul (f.toMul.1 x), by
        intro h x
        exact congrArg Additive.ofMul (f.toMul.2 h x)⟩
      invFun := fun f ↦ Additive.ofMul ⟨fun x ↦ (f.1 x).toMul, by
        intro h x
        exact congrArg Additive.toMul (f.2 h x)⟩
      left_inv := fun f ↦ by
        apply Additive.toMul.injective
        apply Subtype.ext
        rfl
      right_inv := fun f ↦ by
        apply Subtype.ext
        rfl
      map_add' := fun f g ↦ by
        apply Subtype.ext
        rfl }
  exact Rep.mkIso (Representation.Equiv.mk e.toIntLinearEquiv (by
    intro g
    ext f x
    rfl))

end Representation

section Integral

variable {G : Type u} [Group G] (H : Subgroup G)
variable (B : Type v) [CommGroup B] [MulDistribMulAction H B]

/-- Native Shapiro for the original induced module with independent group and carrier. -/
def multiplicativeInducedIntegralCohomologyIso (i : ℕ) :
    IntegralGroupCohomology.Universe.cohomology
        (Rep.ofMulDistribMulAction G (InducedModule (B := B) H)) i ≅
      IntegralGroupCohomology.Universe.cohomology (Rep.ofMulDistribMulAction H B) i :=
  (IntegralGroupCohomology.Universe.cohomologyFunctor G i).mapIso
      (multiplicativeInducedRepIsoCoind H B) ≪≫
    IntegralGroupCohomology.Universe.coindIso (Rep.ofMulDistribMulAction H B) i

/-- Integral cohomology vanishing passes through the actual induced-module comparison. -/
theorem multiplicativeInducedIntegralCohomology_subsingleton (i : ℕ)
    [Subsingleton (IntegralGroupCohomology.Universe.cohomology (Rep.ofMulDistribMulAction H B) i)] :
    Subsingleton (IntegralGroupCohomology.Universe.cohomology
      (Rep.ofMulDistribMulAction G (InducedModule (B := B) H)) i) :=
  Function.Injective.subsingleton
    (multiplicativeInducedIntegralCohomologyIso H B i).toLinearEquiv.injective

end Integral

section Original

variable {G : Type} [Group G] (H : Subgroup G)
variable (B : Type) [CommGroup B] [MulDistribMulAction H B]

/-- Shapiro's lemma for the actual multiplicative induced module used
in the finite-place idele decomposition, in every cohomological degree. -/
noncomputable def multiplicativeInducedCohomologyIso (i : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction G (InducedModule (B := B) H)) i ≅
      groupCohomology (Rep.ofMulDistribMulAction H B) i :=
  (groupCohomology.functor ℤ G i).mapIso (multiplicativeInducedRepIsoCoind H B) ≪≫
    groupCohomology.coindIso (Rep.ofMulDistribMulAction H B) i

/-- The existing independent-universe Shapiro map recovers the original selected induced map. -/
theorem multiplicativeInducedIntegralCohomologyIso_cohomologyIsoOriginal (i : ℕ) :
    (multiplicativeInducedIntegralCohomologyIso H B i).hom ≫
        (IntegralGroupCohomology.Universe.cohomologyIsoOriginal
          (Rep.ofMulDistribMulAction H B) i).hom =
      (IntegralGroupCohomology.Universe.cohomologyIsoOriginal
        (Rep.ofMulDistribMulAction G (InducedModule (B := B) H)) i).hom ≫
          (multiplicativeInducedCohomologyIso H B i).hom := by
  let M := Rep.ofMulDistribMulAction G (InducedModule (B := B) H)
  let A := Rep.ofMulDistribMulAction H B
  let E := multiplicativeInducedRepIsoCoind H B
  change ((IntegralGroupCohomology.Universe.cohomologyFunctor G i).map E.hom ≫
      (IntegralGroupCohomology.Universe.coindIso A i).hom) ≫
        (IntegralGroupCohomology.Universe.cohomologyIsoOriginal A i).hom =
    (IntegralGroupCohomology.Universe.cohomologyIsoOriginal M i).hom ≫
      ((groupCohomology.functor ℤ G i).map E.hom ≫ (groupCohomology.coindIso A i).hom)
  rw [Category.assoc, IntegralGroupCohomology.Universe.coindIso_cohomologyIsoOriginal,
    ← Category.assoc, IntegralGroupCohomology.Universe.cohomologyIsoOriginal_naturality]
  exact Category.assoc
    (IntegralGroupCohomology.Universe.cohomologyIsoOriginal M i).hom
    ((groupCohomology.functor ℤ G i).map E.hom) (groupCohomology.coindIso A i).hom

/-- Transporting the existing lifted induced Shapiro back gives exactly the original isomorphism. -/
theorem multiplicativeInducedIntegralCohomologyIso_eq_original (i : ℕ) :
    (IntegralGroupCohomology.Universe.cohomologyIsoOriginal
      (Rep.ofMulDistribMulAction G (InducedModule (B := B) H)) i).symm ≪≫
        multiplicativeInducedIntegralCohomologyIso H B i ≪≫
          IntegralGroupCohomology.Universe.cohomologyIsoOriginal
            (Rep.ofMulDistribMulAction H B) i = multiplicativeInducedCohomologyIso H B i := by
  apply Iso.ext
  change (IntegralGroupCohomology.Universe.cohomologyIsoOriginal
      (Rep.ofMulDistribMulAction G (InducedModule (B := B) H)) i).inv ≫
      ((multiplicativeInducedIntegralCohomologyIso H B i).hom ≫
        (IntegralGroupCohomology.Universe.cohomologyIsoOriginal
          (Rep.ofMulDistribMulAction H B) i).hom) =
    (multiplicativeInducedCohomologyIso H B i).hom
  rw [multiplicativeInducedIntegralCohomologyIso_cohomologyIsoOriginal,
    Iso.inv_hom_id_assoc]

/-- Vanishing passes from a subgroup representation to its concrete
multiplicative induced module via the proved Shapiro isomorphism. -/
theorem multiplicativeInducedCohomology_subsingleton (i : ℕ)
    [Subsingleton (groupCohomology (Rep.ofMulDistribMulAction H B) i)] :
    Subsingleton
      (groupCohomology (Rep.ofMulDistribMulAction G (InducedModule (B := B) H)) i) := by
  let e :=
    (IntegralGroupCohomology.Universe.cohomologyIsoOriginal
      (Rep.ofMulDistribMulAction G (InducedModule (B := B) H)) i).symm ≪≫
      multiplicativeInducedIntegralCohomologyIso H B i ≪≫
        IntegralGroupCohomology.Universe.cohomologyIsoOriginal (Rep.ofMulDistribMulAction H B) i
  exact Function.Injective.subsingleton e.toLinearEquiv.injective

end Original

end ClassFieldTower.Cohomology
