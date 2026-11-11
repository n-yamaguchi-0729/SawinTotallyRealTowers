/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Nyll.GaloisCohomology.Cyclic.NormKernelVanishing
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingHomologyEquivalence
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingConnectingMap

/-!
# Integral cohomology in the acting group's universe

An integer representation with group and carrier in `Type u` is transported along
`ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ`. Mathlib's actual native cohomology,
homology and Tate functors then apply in universe `u`. Restricting the resulting
scalar action back to integers retains their underlying additive groups.

This construction does not shrink the group or add a comparison hypothesis.
The action, equivariant maps and norm have their original values. In universe
zero, the proved coefficient complex comparisons identify these objects with
the original integer-coefficient APIs. Connecting maps and their naturality
are inherited from the same native complexes and short exact sequences.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace IntegralGroupCohomology

/-- The original integer representation over lifted integers, with unchanged carrier and action. -/
def coefficientFunctor (G : Type u) [Group G] :
    Rep.{u} ℤ G ⥤ Rep.{u} (ULift.{u} ℤ) G :=
  (Rep.coefficientRingEquivalence (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) G).functor

/-- Recover the integer scalar action without changing the additive coefficient group. -/
def integerScalars : ModuleCat.{u} (ULift.{u} ℤ) ⥤ ModuleCat.{u} ℤ :=
  ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.toRingHom

/-- Coefficient transport inherits additivity from the same representation equivalence. -/
instance coefficientFunctor_additive (G : Type u) [Group G] :
    (coefficientFunctor G).Additive := by
  dsimp only [coefficientFunctor]
  infer_instance

/-- The coefficient equivalence preserves finite limits. -/
instance coefficientFunctor_preservesFiniteLimits (G : Type u) [Group G] :
    Limits.PreservesFiniteLimits (coefficientFunctor G) := by
  dsimp only [coefficientFunctor]
  infer_instance

/-- The coefficient equivalence preserves finite colimits. -/
instance coefficientFunctor_preservesFiniteColimits (G : Type u) [Group G] :
    Limits.PreservesFiniteColimits (coefficientFunctor G) := by
  dsimp only [coefficientFunctor]
  infer_instance

/-- The existing scalar-restriction functor is additive. -/
instance integerScalars_additive : integerScalars.{u}.Additive := by
  dsimp only [integerScalars]
  infer_instance

/-- The same restriction of scalars preserves finite limits. -/
instance integerScalars_preservesFiniteLimits :
    Limits.PreservesFiniteLimits integerScalars.{u} := by
  dsimp only [integerScalars]
  infer_instance

/-- The same restriction of scalars preserves finite colimits. -/
instance integerScalars_preservesFiniteColimits :
    Limits.PreservesFiniteColimits integerScalars.{u} := by
  dsimp only [integerScalars]
  infer_instance

variable {G : Type u} [Group G]

/-- The transported representation has the original group action. -/
theorem coefficientFunctor_obj_ρ_apply (A : Rep.{u} ℤ G) (g : G) (a : A) :
    ((coefficientFunctor G).obj A).ρ g a = A.ρ g a := rfl

/-- Coefficient transport retains every equivariant map. -/
theorem coefficientFunctor_map_apply {A B : Rep.{u} ℤ G} (f : A ⟶ B) (a : A) :
    (coefficientFunctor G).map f a = f a := rfl

/-- Restriction of the acting group commutes with the same coefficient transport. -/
theorem coefficientFunctor_res_obj {H : Type u} [Group H] (q : H →* G)
    (A : Rep.{u} ℤ G) :
    (coefficientFunctor H).obj (Rep.res q A) =
      Rep.res q ((coefficientFunctor G).obj A) := rfl

/-- The native degree-one coboundary uses the original integer representation action. -/
theorem coefficientFunctor_d₁₂_apply (A : Rep.{u} ℤ G) (f : G → A) (g h : G) :
    groupCohomology.d₁₂ ((coefficientFunctor G).obj A) f (g, h) =
      A.ρ g (f h) - f (g * h) + f g := rfl

/-- Integral group cohomology from the actual native lifted-coefficient functor. -/
def cohomologyFunctor (G : Type u) [Group G] (n : ℕ) :
    Rep.{u} ℤ G ⥤ ModuleCat.{u} ℤ :=
  coefficientFunctor G ⋙ groupCohomology.functor (ULift.{u} ℤ) G n ⋙ integerScalars

/-- The composite cohomology functor retains the native zero maps. -/
instance cohomologyFunctor_preservesZeroMorphisms (G : Type u) [Group G] (n : ℕ) :
    (cohomologyFunctor G n).PreservesZeroMorphisms := by
  dsimp only [cohomologyFunctor]
  infer_instance

/-- Integral group homology from the actual native lifted-coefficient functor. -/
def homologyFunctor (G : Type u) [Group G] (n : ℕ) :
    Rep.{u} ℤ G ⥤ ModuleCat.{u} ℤ :=
  coefficientFunctor G ⋙ groupHomology.functor (ULift.{u} ℤ) G n ⋙ integerScalars

/-- The actual integral cohomology object in the acting group's universe. -/
abbrev cohomology (A : Rep.{u} ℤ G) (n : ℕ) : ModuleCat.{u} ℤ :=
  (cohomologyFunctor G n).obj A

/-- The actual integral homology object in the acting group's universe. -/
abbrev homology (A : Rep.{u} ℤ G) (n : ℕ) : ModuleCat.{u} ℤ :=
  (homologyFunctor G n).obj A

/-- A short exact sequence remains the same exact sequence after coefficient transport. -/
theorem coefficient_shortExact {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact) :
    (S.map (coefficientFunctor G)).ShortExact :=
  hS.map_of_exact (coefficientFunctor G)

/-- The connecting map is the native connecting map with its scalars restricted to integers. -/
def δ {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) : cohomology S.X₃ i ⟶ cohomology S.X₁ j := by
  let T : ShortComplex (Rep.{u} (ULift.{u} ℤ) G) := S.map (coefficientFunctor G)
  have hT : T.ShortExact := coefficient_shortExact hS
  let d : groupCohomology T.X₃ i ⟶ groupCohomology T.X₁ j :=
    groupCohomology.δ (k := ULift.{u} ℤ) (G := G) (X := T) hT i j hij
  exact integerScalars.map d

/-- Naturality of the actual integral connecting map. -/
theorem δ_naturality {S T : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hS i j hij ≫ (cohomologyFunctor G j).map f.τ₁ =
      (cohomologyFunctor G i).map f.τ₃ ≫ δ hT i j hij := by
  let S' : ShortComplex (Rep.{u} (ULift.{u} ℤ) G) := S.map (coefficientFunctor G)
  let T' : ShortComplex (Rep.{u} (ULift.{u} ℤ) G) := T.map (coefficientFunctor G)
  let f' : S' ⟶ T' := (coefficientFunctor G).mapShortComplex.map f
  have hS' : S'.ShortExact := coefficient_shortExact hS
  have hT' : T'.ShortExact := coefficient_shortExact hT
  let dS : groupCohomology S'.X₃ i ⟶ groupCohomology S'.X₁ j :=
    groupCohomology.δ hS' i j hij
  let dT : groupCohomology T'.X₃ i ⟶ groupCohomology T'.X₁ j :=
    groupCohomology.δ hT' i j hij
  let f₁ : groupCohomology S'.X₁ j ⟶ groupCohomology T'.X₁ j :=
    groupCohomology.map (MonoidHom.id G) f'.τ₁ j
  let f₃ : groupCohomology S'.X₃ i ⟶ groupCohomology T'.X₃ i :=
    groupCohomology.map (MonoidHom.id G) f'.τ₃ i
  have hn : dS ≫ f₁ = f₃ ≫ dT :=
    groupCohomology.δ_naturality hS' hT' f' i j hij
  exact (integerScalars.map_comp dS f₁).symm.trans
    ((congrArg (fun m : groupCohomology S'.X₃ i ⟶ groupCohomology T'.X₁ j =>
        integerScalars.map m) hn).trans (integerScalars.map_comp f₃ dT))

/-- Exactness at the middle coefficient object in each integral cohomology degree. -/
theorem cohomology_exact₂ {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact) (i : ℕ) :
    (S.map (cohomologyFunctor G i)).Exact :=
  (groupCohomology.mapShortComplex₂_exact (coefficient_shortExact hS) i).map integerScalars

/-- Exactness after the native connecting map, with the original integer scalar action. -/
theorem cohomology_exact₁ {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact)
    {i j : ℕ} (hij : i + 1 = j) :
    ((groupCohomology.mapShortComplex₁ (coefficient_shortExact hS) hij).map integerScalars).Exact :=
  (groupCohomology.mapShortComplex₁_exact (coefficient_shortExact hS) hij).map integerScalars

/-- Exactness before the native connecting map, with the original integer scalar action. -/
theorem cohomology_exact₃ {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact)
    {i j : ℕ} (hij : i + 1 = j) :
    ((groupCohomology.mapShortComplex₃ (coefficient_shortExact hS) hij).map integerScalars).Exact :=
  (groupCohomology.mapShortComplex₃_exact (coefficient_shortExact hS) hij).map integerScalars

section Finite

variable [Fintype G]

/-- The finite norm has the original value, before and after coefficient transport. -/
theorem coefficientFunctor_norm_apply (A : Rep.{u} ℤ G) (a : A) :
    ((coefficientFunctor G).obj A).norm.asHom.hom a = A.norm.asHom.hom a :=
  Rep.coefficientRingEquivalence_obj_norm_apply
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) G A a

/-- Integral Tate cohomology from the actual native Tate complex. -/
def tateFunctor (G : Type u) [Group G] [Fintype G] (n : ℤ) :
    Rep.{u} ℤ G ⥤ ModuleCat.{u} ℤ :=
  coefficientFunctor G ⋙ tateCohomologyFunctor n ⋙ integerScalars

/-- The actual integral Tate cohomology object in the acting group's universe. -/
abbrev tate (A : Rep.{u} ℤ G) (n : ℤ) : ModuleCat.{u} ℤ :=
  (tateFunctor G n).obj A

/-- The Tate connecting map from the transported original short exact sequence. -/
def tateδ {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact) (i : ℤ) :
    tate S.X₃ i ⟶ tate S.X₁ (i + 1) := by
  let T : ShortComplex (Rep.{u} (ULift.{u} ℤ) G) := S.map (coefficientFunctor G)
  have hT : T.ShortExact := coefficient_shortExact hS
  let d : tateCohomology T.X₃ i ⟶ tateCohomology T.X₁ (i + 1) :=
    TateCohomology.δ (R := ULift.{u} ℤ) (G := G) (S := T) hT i
  exact integerScalars.map d

/-- Naturality of the actual integral Tate connecting map. -/
theorem tateδ_naturality {S T : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) (i : ℤ) :
    tateδ hS i ≫ (tateFunctor G (i + 1)).map f.τ₁ =
      (tateFunctor G i).map f.τ₃ ≫ tateδ hT i := by
  change integerScalars.map _ ≫ integerScalars.map _ =
    integerScalars.map _ ≫ integerScalars.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun f => integerScalars.map f)
    (TateCohomology.δ_naturality (coefficient_shortExact hS)
      (coefficient_shortExact hT) ((coefficientFunctor G).mapShortComplex.map f) i)

/-- The native finite-cyclic calculation applies to integer representations in every universe. -/
def cyclicH1IsoTateMinusOne (A : Rep.{u} ℤ G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) : cohomology A 1 ≅ tate A (-1) :=
  integerScalars.mapIso
    (CyclicCohomology.finiteCyclicH1IsoTateHMinusOne ((coefficientFunctor G).obj A) g hg)

/-- Norm-zero elements are extracted from the actual Tate vanishing statement in every universe. -/
theorem normKernel_of_tate_isZero (A : Rep.{u} ℤ G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hzero : Limits.IsZero (tate A (-1))) :
    ∀ x : A, A.norm.asHom.hom x = 0 → ∃ y : A, A.ρ g y - y = x := by
  let : Subsingleton (tateCohomology ((coefficientFunctor G).obj A) (-1)) :=
    ModuleCat.subsingleton_of_isZero (M := tate A (-1)) hzero
  have hnative : Limits.IsZero (tateCohomology ((coefficientFunctor G).obj A) (-1)) :=
    ModuleCat.isZero_of_subsingleton _
  intro x hx
  exact CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
    ((coefficientFunctor G).obj A) g hg hnative x
    ((coefficientFunctor_norm_apply A x).trans hx)

end Finite

section Original

variable {H : Type} [Group H] (A : Rep.{0} ℤ H)

/-- In universe zero, actual cochain comparison recovers the original integer cohomology. -/
def cohomologyIsoOriginal (n : ℕ) : cohomology A n ≅ groupCohomology A n :=
  integerScalars.mapIso
      (groupCohomology.coefficientRingIso (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ) A n).symm ≪≫
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ)).unitIso.app (groupCohomology A n)).symm

/-- In universe zero this is the original integer group homology, via actual chain comparison. -/
def homologyIsoOriginal (n : ℕ) : homology A n ≅ groupHomology A n :=
  integerScalars.mapIso
      (groupHomology.coefficientRingIso (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ) A n).symm ≪≫
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ)).unitIso.app (groupHomology A n)).symm

/-- In universe zero the existing integral comparison preserves the original connecting map. -/
theorem δ_cohomologyIsoOriginal {X : ShortComplex (Rep.{0} ℤ H)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ (cohomologyIsoOriginal X.X₁ j).hom =
      (cohomologyIsoOriginal X.X₃ i).hom ≫ groupCohomology.δ hX i j hij := by
  let e : ULift.{0} ℤ ≃+* ℤ := ULift.ringEquiv
  let Q : ModuleCat.{0} ℤ ≌ ModuleCat.{0} (ULift.{0} ℤ) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let F : ModuleCat.{0} (ULift.{0} ℤ) ⥤ ModuleCat.{0} ℤ := integerScalars
  let T : ShortComplex (Rep.{0} (ULift.{0} ℤ) H) := X.map (coefficientFunctor H)
  let c₁ : Q.functor.obj (groupCohomology X.X₁ j) ≅ groupCohomology T.X₁ j :=
    groupCohomology.coefficientRingIso e X.X₁ j
  let c₃ : Q.functor.obj (groupCohomology X.X₃ i) ≅ groupCohomology T.X₃ i :=
    groupCohomology.coefficientRingIso e X.X₃ i
  let d : groupCohomology X.X₃ i ⟶ groupCohomology X.X₁ j :=
    groupCohomology.δ hX i j hij
  let d' : groupCohomology T.X₃ i ⟶ groupCohomology T.X₁ j :=
    groupCohomology.δ (coefficient_shortExact hX) i j hij
  let a₁ : F.obj (Q.functor.obj (groupCohomology X.X₁ j)) ⟶
      groupCohomology X.X₁ j := (Q.unitIso.app (groupCohomology X.X₁ j)).inv
  let a₃ : F.obj (Q.functor.obj (groupCohomology X.X₃ i)) ⟶
      groupCohomology X.X₃ i := (Q.unitIso.app (groupCohomology X.X₃ i)).inv
  have hc : d' ≫ c₁.inv = c₃.inv ≫ Q.functor.map d :=
    groupCohomology.δ_coefficientRingIso_inv e hX i j hij
  have hm : F.map d' ≫ F.map c₁.inv = F.map c₃.inv ≫ F.map (Q.functor.map d) :=
    (F.map_comp d' c₁.inv).symm.trans
      ((congrArg (fun f : groupCohomology T.X₃ i ⟶ Q.functor.obj (groupCohomology X.X₁ j) =>
          F.map f) hc).trans (F.map_comp c₃.inv (Q.functor.map d)))
  have hu : F.map (Q.functor.map d) ≫ a₁ = a₃ ≫ d := Q.unitIso.inv.naturality d
  change F.map d' ≫ (F.map c₁.inv ≫ a₁) = (F.map c₃.inv ≫ a₃) ≫ d
  exact (Category.assoc (F.map d') (F.map c₁.inv) a₁).symm.trans
    ((congrArg (fun f => f ≫ a₁) hm).trans
      ((Category.assoc (F.map c₃.inv) (F.map (Q.functor.map d)) a₁).trans
        ((congrArg (fun f => F.map c₃.inv ≫ f) hu).trans
          (Category.assoc (F.map c₃.inv) a₃ d).symm)))

variable [Fintype H]

/-- In universe zero this is the original integer Tate cohomology, including boundary degrees. -/
def tateIsoOriginal (n : ℤ) : tate A n ≅ tateCohomology A n :=
  integerScalars.mapIso
      (TateCohomology.coefficientRingIso (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ) A n).symm ≪≫
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ)).unitIso.app (tateCohomology A n)).symm

/-- The original Tate vanishing condition is equivalent to the transported condition. -/
theorem isZero_tate_iff_original (n : ℤ) :
    Limits.IsZero (tate A n) ↔ Limits.IsZero (tateCohomology A n) :=
  ⟨fun h => Limits.IsZero.of_iso h (tateIsoOriginal A n).symm,
    fun h => Limits.IsZero.of_iso h (tateIsoOriginal A n)⟩

/-- The existing universe-zero Tate comparison preserves the original connecting map. -/
theorem tateδ_tateIsoOriginal {X : ShortComplex (Rep.{0} ℤ H)} (hX : X.ShortExact)
    (i : ℤ) :
    tateδ hX i ≫ (tateIsoOriginal X.X₁ (i + 1)).hom =
      (tateIsoOriginal X.X₃ i).hom ≫ TateCohomology.δ hX i := by
  let e : ULift.{0} ℤ ≃+* ℤ := ULift.ringEquiv
  let Q : ModuleCat.{0} ℤ ≌ ModuleCat.{0} (ULift.{0} ℤ) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let F : ModuleCat.{0} (ULift.{0} ℤ) ⥤ ModuleCat.{0} ℤ := integerScalars
  let T : ShortComplex (Rep.{0} (ULift.{0} ℤ) H) := X.map (coefficientFunctor H)
  let c₁ : Q.functor.obj (tateCohomology X.X₁ (i + 1)) ≅ tateCohomology T.X₁ (i + 1) :=
    TateCohomology.coefficientRingIso e X.X₁ (i + 1)
  let c₃ : Q.functor.obj (tateCohomology X.X₃ i) ≅ tateCohomology T.X₃ i :=
    TateCohomology.coefficientRingIso e X.X₃ i
  let d : tateCohomology X.X₃ i ⟶ tateCohomology X.X₁ (i + 1) :=
    TateCohomology.δ hX i
  let d' : tateCohomology T.X₃ i ⟶ tateCohomology T.X₁ (i + 1) :=
    TateCohomology.δ (coefficient_shortExact hX) i
  let a₁ : F.obj (Q.functor.obj (tateCohomology X.X₁ (i + 1))) ⟶
      tateCohomology X.X₁ (i + 1) := (Q.unitIso.app (tateCohomology X.X₁ (i + 1))).inv
  let a₃ : F.obj (Q.functor.obj (tateCohomology X.X₃ i)) ⟶
      tateCohomology X.X₃ i := (Q.unitIso.app (tateCohomology X.X₃ i)).inv
  have hc : d' ≫ c₁.inv = c₃.inv ≫ Q.functor.map d :=
    TateCohomology.δ_coefficientRingIso_inv e hX i
  have hm : F.map d' ≫ F.map c₁.inv = F.map c₃.inv ≫ F.map (Q.functor.map d) :=
    (F.map_comp d' c₁.inv).symm.trans
      ((congrArg (fun f : tateCohomology T.X₃ i ⟶ Q.functor.obj (tateCohomology X.X₁ (i + 1)) =>
          F.map f) hc).trans (F.map_comp c₃.inv (Q.functor.map d)))
  have hu : F.map (Q.functor.map d) ≫ a₁ = a₃ ≫ d := Q.unitIso.inv.naturality d
  change F.map d' ≫ (F.map c₁.inv ≫ a₁) = (F.map c₃.inv ≫ a₃) ≫ d
  exact (Category.assoc (F.map d') (F.map c₁.inv) a₁).symm.trans
    ((congrArg (fun f => f ≫ a₁) hm).trans
      ((Category.assoc (F.map c₃.inv) (F.map (Q.functor.map d)) a₁).trans
        ((congrArg (fun f => F.map c₃.inv ≫ f) hu).trans
          (Category.assoc (F.map c₃.inv) a₃ d).symm)))

end Original

end IntegralGroupCohomology
