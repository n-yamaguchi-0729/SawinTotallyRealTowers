/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.GroupRing
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

/-!
# Fox differential: discrete — kernel boundary — identity augmentation

The principal declarations in this module are:

- `coinvariantsLEquivOfSubsingleton`
  For a representation of a subsingleton monoid, taking coinvariants does not change the underlying
  module.
- `rightRegularRepresentation`
  The right-regular \(\mathbb{Z}\)-linear representation on \(\mathbb{Z}[H]\), given by right
  multiplication by \(g^{-1}\). This is the representation whose low-degree group homology matches
  the identity-case Crowell relations.
- `rightRegularRepresentation_apply_single`
  The right-regular representation sends a single group element to the corresponding basis action.
- `rightRegularRepresentation_apply_of`
  The right-regular representation has the displayed value on a representative.
-/

namespace FoxDifferential

noncomputable section

open CategoryTheory Limits Representation Rep TensorProduct
open scoped TensorProduct


variable (H : Type) [Group H] [DecidableEq H]

/--
For a representation of a subsingleton monoid, taking coinvariants does not change the
underlying module.
-/
def coinvariantsLEquivOfSubsingleton
    {k G V : Type*} [CommRing k] [Monoid G] [Subsingleton G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    Representation.Coinvariants ρ ≃ₗ[k] V := by
  refine LinearEquiv.ofLinearMap
    (Representation.Coinvariants.lift ρ LinearMap.id ?_)
    (Representation.Coinvariants.mk ρ)
    ?_ ?_
  · intro g
    ext x
    have : g = (1 : G) := Subsingleton.elim _ _
    subst this
    simp only [map_one, LinearMap.id_comp, Module.End.one_apply, LinearMap.id_coe, id_eq]
  · ext x
    simp only [Coinvariants.lift_comp_mk, LinearMap.id_coe, id_eq]
  · apply Representation.Coinvariants.hom_ext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Coinvariants.lift_mk, LinearMap.id_coe,
        id_eq,
  LinearMap.id_comp]

/--
The right-regular \(\mathbb{Z}\)-linear representation on \(\mathbb{Z}[H]\), given by right
multiplication by \(g^{-1}\). This is the representation whose low-degree group homology matches
the identity-case Crowell relations.
-/
def rightRegularRepresentation : Representation ℤ H (GroupRing H) where
  toFun g :=
    { toFun := fun x => x * MonoidAlgebra.of ℤ H g⁻¹
      map_add' := by
        intro x y
        simp only [MonoidAlgebra.of_apply, add_mul]
      map_smul' := by
        intro n x
        simpa using smul_mul_assoc n x (MonoidAlgebra.of ℤ H g⁻¹) }
  map_one' := by
    ext x
    simp only [inv_one, MonoidAlgebra.of_apply, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
  Function.comp_apply, MonoidAlgebra.lsingle_apply, MonoidAlgebra.single_mul_single, mul_one,
      Module.End.one_apply]
  map_mul' g₁ g₂ := by
    ext x
    simp only [mul_inv_rev, MonoidAlgebra.of_apply, LinearMap.coe_comp, LinearMap.coe_mk,
        AddHom.coe_mk,
  Function.comp_apply, MonoidAlgebra.lsingle_apply, MonoidAlgebra.single_mul_single, mul_one,
      Module.End.mul_apply,
  mul_assoc]

omit [DecidableEq H] in
/--
The right-regular representation sends a single group element to the corresponding basis action.
-/
@[simp]
theorem rightRegularRepresentation_apply_single (g h : H) (n : ℤ) :
    rightRegularRepresentation H g (MonoidAlgebra.single h n) =
      MonoidAlgebra.single (h * g⁻¹) n := by
  ext a
  simp only [rightRegularRepresentation, MonoidAlgebra.of_apply, MonoidHom.coe_mk, OneHom.coe_mk,
  LinearMap.coe_mk, AddHom.coe_mk, MonoidAlgebra.single_mul_single, mul_one]

omit [DecidableEq H] in
/-- The right-regular representation has the displayed value on a representative. -/
@[simp]
theorem rightRegularRepresentation_apply_of (g h : H) :
    rightRegularRepresentation H g (MonoidAlgebra.of ℤ H h : GroupRing H) =
      MonoidAlgebra.of ℤ H (h * g⁻¹) := by
  exact rightRegularRepresentation_apply_single (H := H) g h (1 : ℤ)

/-- The right-regular representation as an object of Rep \(\mathbb{Z}\) H. -/
abbrev rightRegularRep : Rep ℤ H := Rep.of (rightRegularRepresentation H)

omit [DecidableEq H] in
/--
The Crowell identity relations are precisely the \(d_{21}\)-images of the right-regular
representation, on basis elements.
-/
theorem rightRegular_d₂₁_single (g₁ g₂ : H) (r : GroupRing H) :
    groupHomology.d₂₁ (rightRegularRep H) (Finsupp.single (g₁, g₂) r) =
      (-r) • relationElement (MonoidHom.id H) g₁ g₂ := by
  rw [groupHomology.d₂₁_single]
  simp only [rightRegularRepresentation, MonoidAlgebra.of_apply, MonoidHom.coe_mk,
      OneHom.coe_mk, inv_inv,
  LinearMap.coe_mk, AddHom.coe_mk, sub_eq_add_neg, add_comm, relationElement,
      MonoidHom.id_apply, Finsupp.smul_single,
  smul_eq_mul, mul_one, neg_add_rev, add_left_comm, smul_add, smul_neg, neg_smul, neg_neg,
      add_assoc]

omit [DecidableEq H] in
/-- Rewriting the right-regular boundary identity in the Crowell direction. -/
theorem relationElement_eq_rightRegular_d₂₁_single (g₁ g₂ : H) (r : GroupRing H) :
    r • relationElement (MonoidHom.id H) g₁ g₂ =
      groupHomology.d₂₁ (rightRegularRep H) (Finsupp.single (g₁, g₂) (-r)) := by
  rw [rightRegular_d₂₁_single]
  simp only [relationElement_eq_crossedDifferentialRelationElement, neg_neg]

omit [DecidableEq H] in
/-- Every right-regular 1-boundary is a Crowell relation in the identity differential module. -/
theorem rightRegular_d₂₁_mem_relationSubmodule (x : H × H →₀ GroupRing H) :
    groupHomology.d₂₁ (rightRegularRep H) x ∈ relationSubmodule (MonoidHom.id H) := by
  induction x using Finsupp.induction with
  | zero =>
      simp only [relationSubmodule_eq_crossedDifferentialRelationSubmodule, map_zero, zero_mem]
  | single_add g r x hg hx ih =>
      have hs :
          groupHomology.d₂₁ (rightRegularRep H) (Finsupp.single g r) ∈
            relationSubmodule (MonoidHom.id H) := by
        rw [rightRegular_d₂₁_single]
        exact (relationSubmodule (MonoidHom.id H)).smul_mem _
          (relationElement_mem (MonoidHom.id H) g.1 g.2)
      simpa [map_add] using (relationSubmodule (MonoidHom.id H)).add_mem hs ih

omit [DecidableEq H] in
/-- The scalar-multiplication formula for \(d_{21}\) holds on singleton generators. -/
@[simp]
theorem rightRegular_d₂₁_smul_single (r : GroupRing H) (g : H × H) (a : GroupRing H) :
    groupHomology.d₂₁ (rightRegularRep H) (r • Finsupp.single g a) =
      r • groupHomology.d₂₁ (rightRegularRep H) (Finsupp.single g a) := by
  calc
    groupHomology.d₂₁ (rightRegularRep H) (r • Finsupp.single g a)
        = groupHomology.d₂₁ (rightRegularRep H) (Finsupp.single g (r * a)) := by
            simp only [Finsupp.smul_single, smul_eq_mul]
    _ = (-(r * a)) • relationElement (MonoidHom.id H) g.1 g.2 := by
          rw [rightRegular_d₂₁_single]
    _ = r • ((-a) • relationElement (MonoidHom.id H) g.1 g.2) := by
          simp only [relationElement_eq_crossedDifferentialRelationElement, neg_smul, smul_neg,
              smul_smul]
    _ = r • groupHomology.d₂₁ (rightRegularRep H) (Finsupp.single g a) := by
          rw [rightRegular_d₂₁_single]

omit [DecidableEq H] in
/-- The right-regular \(d_{21}\) map is compatible with scalar multiplication. -/
theorem rightRegular_d₂₁_smul (r : GroupRing H) (x : H × H →₀ GroupRing H) :
    groupHomology.d₂₁ (rightRegularRep H) (r • x) =
      r • groupHomology.d₂₁ (rightRegularRep H) x := by
  induction x using Finsupp.induction with
  | zero =>
      simp only [smul_zero, map_zero]
  | single_add g a x hg hx ih =>
      rw [smul_add, map_add, ih, rightRegular_d₂₁_smul_single]
      simp only [map_add, smul_add]

/--
The degree-1 boundaries for the right-regular representation, regarded as a
\(\mathbb{Z}[H]\)-submodule of the free pre-module.
-/
def rightRegularBoundariesSubmodule : Submodule (GroupRing H) (DifferentialPreModule H H) where
  carrier := groupHomology.boundaries₁ (rightRegularRep H)
  zero_mem' := by
    exact ⟨0, by simp only [map_zero]⟩
  add_mem' := by
    intro x y hx hy
    exact (groupHomology.boundaries₁ (rightRegularRep H)).add_mem hx hy
  smul_mem' := by
    intro r x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨r • y, rightRegular_d₂₁_smul (H := H) r y⟩

variable {H} in
omit [DecidableEq H] in
/-- The displayed right-regular boundary lies in the right-regular boundary submodule. -/
@[simp]
theorem mem_rightRegularBoundariesSubmodule {x : DifferentialPreModule H H} :
    x ∈ rightRegularBoundariesSubmodule H ↔ x ∈ groupHomology.boundaries₁ (rightRegularRep H) :=
  Iff.rfl

omit [DecidableEq H] in
/-- Each identity-Crowell relation already lies in the right-regular boundary submodule. -/
theorem relationElement_mem_rightRegularBoundariesSubmodule (g₁ g₂ : H) :
    relationElement (MonoidHom.id H) g₁ g₂ ∈ rightRegularBoundariesSubmodule H := by
  refine ⟨Finsupp.single (g₁, g₂) (-1), ?_⟩
  simpa using
    (relationElement_eq_rightRegular_d₂₁_single (H := H) g₁ g₂ (1 : GroupRing H)).symm

omit [DecidableEq H] in
/-- The identity Crowell relation submodule is contained in the right-regular boundary submodule. -/
theorem relationSubmodule_le_rightRegularBoundariesSubmodule :
    relationSubmodule (MonoidHom.id H) ≤ rightRegularBoundariesSubmodule H := by
  rw [relationSubmodule]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨g₁, g₂⟩, rfl⟩
  exact relationElement_mem_rightRegularBoundariesSubmodule (H := H) g₁ g₂

omit [DecidableEq H] in
/--
The degree-1 boundaries for the right-regular representation lie in the Crowell relation
submodule.
-/
theorem rightRegular_boundaries₁_le_relationSubmodule :
    groupHomology.boundaries₁ (rightRegularRep H) ≤
      (relationSubmodule (MonoidHom.id H)).restrictScalars ℤ := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact rightRegular_d₂₁_mem_relationSubmodule (H := H) y

omit [DecidableEq H] in
/-- The right-regular boundary submodule is contained in the relation submodule. -/
theorem rightRegularBoundariesSubmodule_le_relationSubmodule :
    rightRegularBoundariesSubmodule H ≤ relationSubmodule (MonoidHom.id H) := by
  intro x hx
  exact rightRegular_boundaries₁_le_relationSubmodule (H := H) hx

omit [DecidableEq H] in
/-- The identity Crowell relations are exactly the right-regular degree-1 boundaries. -/
theorem relationSubmodule_eq_rightRegularBoundariesSubmodule :
    relationSubmodule (MonoidHom.id H) = rightRegularBoundariesSubmodule H := by
  exact le_antisymm
    (relationSubmodule_le_rightRegularBoundariesSubmodule (H := H))
    (rightRegularBoundariesSubmodule_le_relationSubmodule (H := H))

omit [DecidableEq H] in
/--
The lifted linear identity-boundary map has the stated value on a single group-ring generator.
-/
@[simp]
theorem liftLinear_groupRingBoundary_id_single (g : H) (r : GroupRing H) :
    liftLinear (H := H) (G := H) (A := GroupRing H)
        (groupRingBoundary (MonoidHom.id H)) (Finsupp.single g r) =
      r * augmentationGenerator H g := by
  simp only [liftLinear, Finsupp.linearCombination_single, groupRingBoundary, MonoidHom.id_apply,
  MonoidAlgebra.of_apply, smul_eq_mul, mul_sub, mul_one, augmentationGenerator]

omit [DecidableEq H] in
/-- The pre-boundary map for the identity case lands in the augmentation ideal. -/
theorem liftLinear_groupRingBoundary_id_mem_augmentationIdeal (x : DifferentialPreModule H H) :
    liftLinear (H := H) (G := H) (A := GroupRing H)
        (groupRingBoundary (MonoidHom.id H)) x ∈ augmentationIdeal H := by
  rw [liftLinear, Finsupp.linearCombination_apply]
  exact Submodule.sum_mem (augmentationIdeal H) fun g _ =>
    (augmentationIdeal H).smul_mem _ <|
      groupRingBoundary_mem_augmentationIdeal (H := H) (MonoidHom.id H) g

omit [DecidableEq H] in
/--
The standard generator \(h-1\) of the augmentation ideal lies in the image of the identity
pre-boundary map.
-/
theorem augmentationGenerator_mem_range_liftLinear_groupRingBoundary_id (h : H) :
    augmentationGenerator H h ∈
      LinearMap.range (liftLinear (H := H) (G := H) (A := GroupRing H)
        (groupRingBoundary (MonoidHom.id H))) := by
  refine ⟨Finsupp.single h 1, ?_⟩
  simp only [liftLinear_single, groupRingBoundary, MonoidHom.id_apply, MonoidAlgebra.of_apply,
      smul_eq_mul,
  one_mul, augmentationGenerator]

omit [DecidableEq H] in
/-- The augmentation ideal is generated by the image of the identity pre-boundary map. -/
theorem augmentationIdeal_le_range_liftLinear_groupRingBoundary_id :
    (augmentationIdeal H : Submodule (GroupRing H) (GroupRing H)) ≤
      LinearMap.range (liftLinear (H := H) (G := H) (A := GroupRing H)
        (groupRingBoundary (MonoidHom.id H))) := by
  have hgen :
      (augmentationGeneratorIdeal H : Submodule (GroupRing H) (GroupRing H)) ≤
        LinearMap.range (liftLinear (H := H) (G := H) (A := GroupRing H)
          (groupRingBoundary (MonoidHom.id H))) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact augmentationGenerator_mem_range_liftLinear_groupRingBoundary_id (H := H) h
  simpa [congrArg
      (fun I : Ideal (GroupRing H) => (I : Submodule (GroupRing H) (GroupRing H)))
      (augmentationGeneratorIdeal_eq_augmentationIdeal (H := H))] using hgen

omit [DecidableEq H] in
/--
For the identity homomorphism, the lifted group-ring boundary equals the degree-one differential
for the right-regular representation.
-/
theorem liftLinear_groupRingBoundary_id_eq_d₁₀ :
    (liftLinear (H := H) (G := H) (A := GroupRing H)
        (groupRingBoundary (MonoidHom.id H))).restrictScalars ℤ =
      (groupHomology.d₁₀ (rightRegularRep H)).hom := by
  apply Finsupp.lhom_ext
  intro g r
  rw [groupHomology.d₁₀_single]
  simp only [liftLinear, LinearMap.coe_restrictScalars, Finsupp.linearCombination_single,
      groupRingBoundary,
  MonoidHom.id_apply, MonoidAlgebra.of_apply, sub_eq_add_neg, smul_eq_mul, mul_add, mul_neg,
      mul_one,
  rightRegularRepresentation, MonoidHom.coe_mk, OneHom.coe_mk, inv_inv, LinearMap.coe_mk,
      AddHom.coe_mk]

omit [DecidableEq H] in
/--
The identity group-ring boundary lift is evaluated on canonical generators and then extended
linearly.
-/
theorem liftLinear_groupRingBoundary_id_apply (x : DifferentialPreModule H H) :
    liftLinear (H := H) (G := H) (A := GroupRing H)
        (groupRingBoundary (MonoidHom.id H)) x =
      groupHomology.d₁₀ (rightRegularRep H) x := by
  exact congrArg (fun f : DifferentialPreModule H H →ₗ[ℤ] GroupRing H => f x)
    (liftLinear_groupRingBoundary_id_eq_d₁₀ H)

omit [DecidableEq H] in
/-- The right-regular degree-0 differential lands in the augmentation ideal. -/
theorem rightRegular_d₁₀_mem_augmentationIdeal (x : DifferentialPreModule H H) :
    groupHomology.d₁₀ (rightRegularRep H) x ∈ augmentationIdeal H := by
  simpa [liftLinear_groupRingBoundary_id_apply] using
    liftLinear_groupRingBoundary_id_mem_augmentationIdeal (H := H) x

omit [DecidableEq H] in
/-- The canonical augmentation ideal is the kernel of the ordinary group-ring augmentation map. -/
theorem rightRegular_d₁₀_range_eq_augmentationIdeal :
    LinearMap.range (groupHomology.d₁₀ (rightRegularRep H)).hom =
      (augmentationIdeal H).restrictScalars ℤ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact rightRegular_d₁₀_mem_augmentationIdeal (H := H) x
  · intro hy
    rcases augmentationIdeal_le_range_liftLinear_groupRingBoundary_id (H := H) hy with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← LinearMap.congr_fun (liftLinear_groupRingBoundary_id_eq_d₁₀ (H := H)) x]
    exact hx

/--
The trivial representation of the trivial subgroup of \(H\). Shapiro identifies its induced
representation with the right-regular representation.
-/
abbrev bottomTrivialRep : Rep ℤ (⊥ : Subgroup H) :=
  Rep.trivial ℤ (⊥ : Subgroup H) ℤ

/-- The induced module from the trivial subgroup is just the group ring. -/
def indBottomTrivialUnderlyingEquiv :
    Representation.IndV (⊥ : Subgroup H).subtype (bottomTrivialRep H).ρ ≃ₗ[ℤ] GroupRing H := by
  let ρt : Representation ℤ (⊥ : Subgroup H) (TensorProduct ℤ (GroupRing H) ℤ) :=
    Representation.tprod
      (((Rep.leftRegular ℤ H).ρ.comp (⊥ : Subgroup H).subtype))
      (bottomTrivialRep H).ρ
  let e1 : Representation.Coinvariants ρt ≃ₗ[ℤ] TensorProduct ℤ (GroupRing H) ℤ :=
    coinvariantsLEquivOfSubsingleton ρt
  exact e1.trans (TensorProduct.rid ℤ (GroupRing H))

omit [DecidableEq H] in
/--
The bottom-trivial induced-module equivalence sends the induced representative with element
\(h\) and coefficient \(n\) to the singleton group-ring element at \(h\) with coefficient \(n\).
-/
@[simp 900]
theorem indBottomTrivialUnderlyingEquiv_mk (h : H) (n : ℤ) :
    indBottomTrivialUnderlyingEquiv H
      (Representation.IndV.mk (⊥ : Subgroup H).subtype (bottomTrivialRep H).ρ h n) =
        MonoidAlgebra.single h n := by
  change (TensorProduct.rid ℤ (GroupRing H))
      ((Representation.Coinvariants.lift
          (Representation.tprod (((Rep.leftRegular ℤ H).ρ.comp (⊥ : Subgroup H).subtype))
            (bottomTrivialRep H).ρ)
          LinearMap.id
          (fun x => by
            ext y
            have : x = (1 : (⊥ : Subgroup H)) := Subsingleton.elim _ _
            subst this
            simp only [map_one, LinearMap.id_comp, Module.End.one_apply, LinearMap.id_coe,
              id_eq]))
        (Representation.Coinvariants.mk _ (MonoidAlgebra.single h 1 ⊗ₜ[ℤ] n))) = _
  rw [Representation.Coinvariants.lift_mk]
  simp only [LinearMap.id_coe, id_eq, rid_tmul, MonoidAlgebra.smul_single, Int.zsmul_eq_mul,
      mul_one]

/--
Shapiro's lemma identifies the induced trivial representation of the trivial subgroup with the
right-regular representation.
-/
def indBottomTrivialIsoRightRegular :
    Rep.ind (⊥ : Subgroup H).subtype (bottomTrivialRep H) ≅ rightRegularRep H := by
  refine Rep.mkIso
    (Representation.Equiv.mk (indBottomTrivialUnderlyingEquiv H) ?_)
  intro g
  apply Representation.IndV.hom_ext
  intro h
  apply LinearMap.ext
  intro n
  change (indBottomTrivialUnderlyingEquiv H)
      (((Rep.ind (⊥ : Subgroup H).subtype (bottomTrivialRep H)).ρ g)
        ((Representation.IndV.mk (⊥ : Subgroup H).subtype (bottomTrivialRep H).ρ h) n)) =
    (rightRegularRepresentation H g
      (indBottomTrivialUnderlyingEquiv H
        ((Representation.IndV.mk (⊥ : Subgroup H).subtype (bottomTrivialRep H).ρ h) n)))
  have hind :
      (((Rep.ind (⊥ : Subgroup H).subtype (bottomTrivialRep H)).ρ g)
        ((Representation.IndV.mk (⊥ : Subgroup H).subtype (bottomTrivialRep H).ρ h) n)) =
      (Representation.IndV.mk (⊥ : Subgroup H).subtype (bottomTrivialRep H).ρ (h * g⁻¹))
        n := by
    exact Representation.ind_mk
      (φ := (⊥ : Subgroup H).subtype) (ρ := (bottomTrivialRep H).ρ) g h n
  rw [hind, indBottomTrivialUnderlyingEquiv_mk, indBottomTrivialUnderlyingEquiv_mk]
  simp only [rightRegularRepresentation_apply_single]

/-- Group homology respects isomorphic representations. -/
def groupHomologyIsoOfRepIso {A B : Rep ℤ H} (e : A ≅ B) (n : ℕ) :
    groupHomology A n ≅ groupHomology B n where
  hom := groupHomology.map (MonoidHom.id H) e.hom n
  inv := groupHomology.map (MonoidHom.id H) e.inv n
  hom_inv_id := by
    have h := groupHomology.map_id_comp (φ := e.hom) (ψ := e.inv) (n := n)
    rw [e.hom_inv_id, groupHomology.map_id] at h
    simpa using h.symm
  inv_hom_id := by
    have h := groupHomology.map_id_comp (φ := e.inv) (ψ := e.hom) (n := n)
    rw [e.inv_hom_id, groupHomology.map_id] at h
    simpa using h.symm

/--
The first homology of the right-regular representation is identified with the first homology of
the trivial subgroup.
-/
def rightRegularH1IsoBottom :
    groupHomology (rightRegularRep H) 1 ≅ groupHomology (bottomTrivialRep H) 1 := by
  exact (groupHomologyIsoOfRepIso H (indBottomTrivialIsoRightRegular H).symm 1) ≪≫
    groupHomology.indIso (⊥ : Subgroup H) (bottomTrivialRep H) 1

omit [DecidableEq H] in
/-- The first homology of the right-regular representation vanishes. -/
theorem rightRegular_H1_isZero : Limits.IsZero (groupHomology (rightRegularRep H) 1) := by
  classical
  let hbot : Limits.IsZero (groupHomology (bottomTrivialRep H) 1) := by
    simpa using (isZero_groupHomology_succ_of_subsingleton (A := bottomTrivialRep H) 0)
  exact hbot.of_iso (rightRegularH1IsoBottom H)

omit [DecidableEq H] in
/-- In degree 1, right-regular cycles are exactly right-regular boundaries. -/
theorem rightRegular_cycles₁_eq_boundaries₁ :
    groupHomology.cycles₁ (rightRegularRep H) = groupHomology.boundaries₁ (rightRegularRep H) := by
  classical
  apply le_antisymm
  · intro x hx
    let hzero := rightRegular_H1_isZero H
    have : Subsingleton (groupHomology (rightRegularRep H) 1) :=
      ModuleCat.subsingleton_of_isZero hzero
    let z : groupHomology.cycles₁ (rightRegularRep H) := ⟨x, hx⟩
    exact (groupHomology.H1π_eq_zero_iff (A := rightRegularRep H) z).1 (Subsingleton.elim _ _)
  · exact groupHomology.boundaries₁_le_cycles₁ (rightRegularRep H)

/--
For the right-regular representation, a 1-chain is a boundary exactly when its degree-0
differential vanishes.
-/
theorem mem_rightRegularBoundariesSubmodule_iff_d₁₀_eq_zero
    {H : Type} [Group H] {x : DifferentialPreModule H H} :
    x ∈ rightRegularBoundariesSubmodule H ↔ groupHomology.d₁₀ (rightRegularRep H) x = 0 := by
  constructor
  · intro hx
    have hx' : x ∈ groupHomology.boundaries₁ (rightRegularRep H) := hx
    have hcycle := groupHomology.mem_cycles₁_of_mem_boundaries₁ (A := rightRegularRep H) x hx'
    simpa [groupHomology.cycles₁, LinearMap.mem_ker] using hcycle
  · intro hx
    have hcycle : x ∈ groupHomology.cycles₁ (rightRegularRep H) := by
      simpa [groupHomology.cycles₁, LinearMap.mem_ker] using hx
    have hbound : x ∈ groupHomology.boundaries₁ (rightRegularRep H) := by
      simpa [rightRegular_cycles₁_eq_boundaries₁ (H := H)] using hcycle
    exact hbound

/--
The quotient of the free pre-module by right-regular degree-1 boundaries is the identity Crowell
differential module.
-/
def rightRegularBoundariesQuotientEquivIdentityDifferentialModule :
    (DifferentialPreModule H H ⧸ (rightRegularBoundariesSubmodule H)) ≃ₗ[GroupRing H]
      DifferentialModule (MonoidHom.id H) :=
  Submodule.quotEquivOfEq (rightRegularBoundariesSubmodule H)
    (relationSubmodule (MonoidHom.id H))
    (relationSubmodule_eq_rightRegularBoundariesSubmodule (H := H)).symm

omit [DecidableEq H] in
/--
The equivalence from the quotient by right-regular boundaries to the identity differential
module sends a quotient class to the corresponding relation-submodule quotient class.
-/
@[simp]
theorem rightRegularBoundariesQuotientEquivIdentityDifferentialModule_mk
    (x : DifferentialPreModule H H) :
    rightRegularBoundariesQuotientEquivIdentityDifferentialModule H
      (Submodule.Quotient.mk x) =
        (relationSubmodule (MonoidHom.id H)).mkQ x := by
  rw [rightRegularBoundariesQuotientEquivIdentityDifferentialModule,
    Submodule.quotEquivOfEq_mk]
  rfl

/-- The quotient by right-regular boundaries maps onto the augmentation ideal. -/
def rightRegularBoundariesQuotientToAugmentationIdeal :
    (DifferentialPreModule H H ⧸ (rightRegularBoundariesSubmodule H)) →ₗ[GroupRing H]
      augmentationIdeal H :=
  { toFun := fun x =>
      toAugmentationIdeal (H := H) (MonoidHom.id H)
        (rightRegularBoundariesQuotientEquivIdentityDifferentialModule H x)
    map_add' := by
      intro x y
      simp only [map_add]
    map_smul' := by
      intro r x
      simp only [map_smul, RingHom.id_apply]}

omit [DecidableEq H] in
/--
The quotient map from right-regular boundaries to the augmentation ideal sends a single
generator to the corresponding augmentation generator.
-/
@[simp]
theorem rightRegularBoundariesQuotientToAugmentationIdeal_mk_single (h : H) :
    rightRegularBoundariesQuotientToAugmentationIdeal H
      (Submodule.Quotient.mk (Finsupp.single h 1)) =
        augmentationGeneratorSubtype (H := H) h := by
  change toAugmentationIdeal (H := H) (MonoidHom.id H)
      ((relationSubmodule (MonoidHom.id H)).mkQ (Finsupp.single h 1)) =
    augmentationGeneratorSubtype (H := H) h
  exact toAugmentationIdeal_d (H := H) (MonoidHom.id H) h

omit [DecidableEq H] in
/-- The quotient by right-regular boundaries surjects onto the augmentation ideal. -/
theorem rightRegularBoundariesQuotientToAugmentationIdeal_surjective :
    Function.Surjective (rightRegularBoundariesQuotientToAugmentationIdeal H) := by
  intro y
  rcases toAugmentationIdeal_surjective (H := H) (MonoidHom.id H) (fun h => ⟨h, rfl⟩) y with
    ⟨x, hx⟩
  refine ⟨(rightRegularBoundariesQuotientEquivIdentityDifferentialModule H).symm x, ?_⟩
  simpa [rightRegularBoundariesQuotientToAugmentationIdeal] using hx

/-- The quotient-to-augmentation map has trivial kernel. -/
theorem rightRegularBoundariesQuotientToAugmentationIdeal_eq_zero_iff
    {H : Type} [Group H]
    {q : DifferentialPreModule H H ⧸ (rightRegularBoundariesSubmodule H)} :
    rightRegularBoundariesQuotientToAugmentationIdeal H q = 0 ↔ q = 0 := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro x
  constructor
  · intro hx
    have hx' : groupHomology.d₁₀ (rightRegularRep H) x = 0 := by
      have hxval := congrArg Subtype.val hx
      change toGroupRing (MonoidHom.id H)
          ((rightRegularBoundariesQuotientEquivIdentityDifferentialModule H)
            (Submodule.Quotient.mk x)) = 0 at hxval
      rw [rightRegularBoundariesQuotientEquivIdentityDifferentialModule_mk] at hxval
      change liftLinear (H := H) (G := H) (A := GroupRing H)
          (groupRingBoundary (MonoidHom.id H)) x = 0 at hxval
      simpa [liftLinear_groupRingBoundary_id_apply] using hxval
    have hmem : x ∈ rightRegularBoundariesSubmodule H := by
      exact (mem_rightRegularBoundariesSubmodule_iff_d₁₀_eq_zero (H := H) (x := x)).2 hx'
    exact (Submodule.Quotient.mk_eq_zero (p := rightRegularBoundariesSubmodule H) (x := x)).2 hmem
  · intro hq
    simp only [hq, map_zero]

omit [DecidableEq H] in
/--
The map from the quotient of right-regular boundaries to the ordinary augmentation ideal is
injective.
-/
theorem rightRegularBoundariesQuotientToAugmentationIdeal_injective :
    Function.Injective (rightRegularBoundariesQuotientToAugmentationIdeal H) := by
  intro x y hxy
  apply sub_eq_zero.mp
  refine (rightRegularBoundariesQuotientToAugmentationIdeal_eq_zero_iff (H := H) (q := x - y)).1 ?_
  simpa [LinearMap.map_sub] using sub_eq_zero.mpr hxy

/-- The right-regular boundary quotient is exactly the augmentation ideal. -/
def rightRegularBoundariesQuotientEquivAugmentationIdeal :
    (DifferentialPreModule H H ⧸ (rightRegularBoundariesSubmodule H)) ≃ₗ[GroupRing H]
      augmentationIdeal H :=
  LinearEquiv.ofBijective (rightRegularBoundariesQuotientToAugmentationIdeal H)
    ⟨rightRegularBoundariesQuotientToAugmentationIdeal_injective (H := H),
      rightRegularBoundariesQuotientToAugmentationIdeal_surjective (H := H)⟩

omit [DecidableEq H] in
/--
Under the identity differential module equivalence, the universal differential \(d(h)\)
corresponds to the augmentation generator \(h-1\).
-/
@[simp]
theorem identityDifferentialModuleEquivAugmentationIdeal_d (h : H) :
    identityDifferentialModuleEquivAugmentationIdeal (H := H)
        (universalDifferential (MonoidHom.id H) h) =
      augmentationGeneratorSubtype (H := H) h := by
  change
    (identityDifferentialModuleEquivAugmentationIdeal (H := H)).toLinearMap
      (universalDifferential (MonoidHom.id H) h) =
        augmentationGeneratorSubtype (H := H) h
  rw [identityDifferentialModuleEquivAugmentationIdeal_toLinearMap]
  rw [toAugmentationIdeal_d]
  apply Subtype.ext
  rfl


end

end FoxDifferential
