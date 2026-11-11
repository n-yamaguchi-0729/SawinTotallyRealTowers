/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Nyll.GaloisCohomology.Cyclic.IntegralCoefficientCohomology
public import Nyll.GaloisCohomology.GroupTheory.GroupEquivComplexComparison
public import Nyll.GaloisCohomology.GroupTheory.RepresentationUniverseLift
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Integral cohomology for independent group and carrier universes

For `G : Type u` and `A : Rep.{v} ℤ G`, the existing representation lift puts the acting group
and carrier in `Type (max u v)`. The existing integer coefficient transport then supplies
Mathlib's native cohomology, homology and Tate functors in precisely that working universe.

The action and norm retain their original values. When the original group and carrier already
share a universe, explicit group/coefficient complex comparisons identify these objects with
the existing integral owner. In universe zero the resulting comparisons recover the original
literal integer APIs, including finite cardinalities and Tate vanishing conditions.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace IntegralGroupCohomology.Universe

/-- The actual lifted representation over lifted integers in the necessary working universe. -/
def nativeFunctor (G : Type u) [Group G] :
    Rep.{v} ℤ G ⥤ Rep.{max u v} (ULift.{max u v} ℤ) (ULift.{v} G) :=
  Rep.universeLiftFunctor ℤ G ⋙ IntegralGroupCohomology.coefficientFunctor (ULift.{v} G)

/-- The actual lift and coefficient composite inherits additivity from its two functors. -/
instance nativeFunctor_additive (G : Type u) [Group G] :
    (nativeFunctor.{u, v} G).Additive := by
  dsimp only [nativeFunctor]
  infer_instance

/-- Cohomology of the original integer representation with independent group and carrier. -/
def cohomologyFunctor (G : Type u) [Group G] (n : ℕ) :
    Rep.{v} ℤ G ⥤ ModuleCat.{max u v} ℤ :=
  nativeFunctor G ⋙ groupCohomology.functor (ULift.{max u v} ℤ) (ULift.{v} G) n ⋙
    IntegralGroupCohomology.integerScalars

/-- Homology of the same actual lifted representation. -/
def homologyFunctor (G : Type u) [Group G] (n : ℕ) :
    Rep.{v} ℤ G ⥤ ModuleCat.{max u v} ℤ :=
  nativeFunctor G ⋙ groupHomology.functor (ULift.{max u v} ℤ) (ULift.{v} G) n ⋙
    IntegralGroupCohomology.integerScalars

variable {G : Type u} [Group G]

/-- Integral cohomology without imposing equality of group and carrier universes. -/
abbrev cohomology (A : Rep.{v} ℤ G) (n : ℕ) : ModuleCat.{max u v} ℤ :=
  (cohomologyFunctor G n).obj A

/-- Integral homology without imposing equality of group and carrier universes. -/
abbrev homology (A : Rep.{v} ℤ G) (n : ℕ) : ModuleCat.{max u v} ℤ :=
  (homologyFunctor G n).obj A

/-- The native action is the original action under the explicit carrier lift. -/
theorem nativeFunctor_ρ_down (A : Rep.{v} ℤ G) (g : G) (a : A) :
    (((nativeFunctor G).obj A).ρ (ULift.up g) (ULift.up a)).down = A.ρ g a := rfl

/-- Every equivariant morphism has its original underlying value after removing the lift. -/
theorem nativeFunctor_map_down {A B : Rep.{v} ℤ G} (f : A ⟶ B) (a : A) :
    ((nativeFunctor G).map f (ULift.up a)).down = f a := rfl

/-- The actual native degree-one coboundary uses the original action and original signs. -/
theorem nativeFunctor_d₁₂_down (A : Rep.{v} ℤ G)
    (f : ULift.{v} G → (nativeFunctor G).obj A) (g h : G) :
    (groupCohomology.d₁₂ ((nativeFunctor G).obj A) f (ULift.up g, ULift.up h)).down =
      A.ρ g (f (ULift.up h)).down -
        (show A from (f (ULift.up (g * h))).down) +
        (show A from (f (ULift.up g)).down) := rfl

/-- The connecting map is the native map of the lifted original short exact sequence. -/
def δ {S : ShortComplex (Rep.{v} ℤ G)} (hS : S.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) : cohomology S.X₃ i ⟶ cohomology S.X₁ j :=
  IntegralGroupCohomology.δ (Rep.universeLiftFunctor_shortExact ℤ G hS) i j hij

/-- Naturality uses the original morphism of short exact sequences through its actual lift. -/
theorem δ_naturality {S T : ShortComplex (Rep.{v} ℤ G)}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hS i j hij ≫ (cohomologyFunctor G j).map f.τ₁ =
      (cohomologyFunctor G i).map f.τ₃ ≫ δ hT i j hij :=
  IntegralGroupCohomology.δ_naturality
    (Rep.universeLiftFunctor_shortExact ℤ G hS)
    (Rep.universeLiftFunctor_shortExact ℤ G hT)
    ((Rep.universeLiftFunctor ℤ G).mapShortComplex.map f) i j hij

section Finite

variable [Fintype G]

/-- Tate cohomology of the same original representation in the required working universe. -/
def tateFunctor (G : Type u) [Group G] [Fintype G] (n : ℤ) :
    Rep.{v} ℤ G ⥤ ModuleCat.{max u v} ℤ :=
  nativeFunctor G ⋙ tateCohomologyFunctor n ⋙ IntegralGroupCohomology.integerScalars

/-- Actual integral Tate cohomology for independent acting group and carrier universes. -/
abbrev tate (A : Rep.{v} ℤ G) (n : ℤ) : ModuleCat.{max u v} ℤ :=
  (tateFunctor G n).obj A

/-- The finite norm remains the original sum of the original actions. -/
theorem nativeFunctor_norm_down (A : Rep.{v} ℤ G) (a : A) :
    (((nativeFunctor G).obj A).norm.asHom.hom (ULift.up a)).down =
      A.norm.asHom.hom a := by
  let B : Rep.{max u v} ℤ (ULift.{v} G) := (Rep.universeLiftFunctor ℤ G).obj A
  let down : B → A := fun x => (show ULift.{u} A from x).down
  exact (congrArg down
    (IntegralGroupCohomology.coefficientFunctor_norm_apply B (ULift.up a))).trans
      (Rep.universeLiftFunctor_norm_down A a)

/-- The actual Tate connecting map of the lifted original short exact sequence. -/
def tateδ {S : ShortComplex (Rep.{v} ℤ G)} (hS : S.ShortExact) (i : ℤ) :
    tate S.X₃ i ⟶ tate S.X₁ (i + 1) :=
  IntegralGroupCohomology.tateδ (Rep.universeLiftFunctor_shortExact ℤ G hS) i

/-- Naturality of the actual Tate connecting map with independent input universes. -/
theorem tateδ_naturality {S T : ShortComplex (Rep.{v} ℤ G)}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) (i : ℤ) :
    tateδ hS i ≫ (tateFunctor G (i + 1)).map f.τ₁ =
      (tateFunctor G i).map f.τ₃ ≫ tateδ hT i :=
  IntegralGroupCohomology.tateδ_naturality
    (Rep.universeLiftFunctor_shortExact ℤ G hS)
    (Rep.universeLiftFunctor_shortExact ℤ G hT)
    ((Rep.universeLiftFunctor ℤ G).mapShortComplex.map f) i

end Finite

section Common

/-- The original coefficient carrier is recovered from the same native lift. -/
def nativeCarrierEquiv (A : Rep.{u} ℤ G) :
    ((nativeFunctor G).obj A).V ≃ₗ[ULift.{u} ℤ]
      ((IntegralGroupCohomology.coefficientFunctor G).obj A).V where
  toFun := ULift.down
  invFun := ULift.up
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- The coefficient carrier comparison intertwines exactly the original group action. -/
theorem nativeCarrierEquiv_comm (A : Rep.{u} ℤ G) (g : ULift.{u} G) :
    (nativeCarrierEquiv A).toLinearMap ∘ₗ ((nativeFunctor G).obj A).ρ g =
      ((IntegralGroupCohomology.coefficientFunctor G).obj A).ρ g.down ∘ₗ
        (nativeCarrierEquiv A).toLinearMap := by
  apply LinearMap.ext
  intro a
  rfl

/-- In a common universe this is the existing integral cohomology owner via actual cochains. -/
def cohomologyIsoCommon (A : Rep.{u} ℤ G) (n : ℕ) :
    cohomology A n ≅ IntegralGroupCohomology.cohomology A n :=
  IntegralGroupCohomology.integerScalars.mapIso
    (groupCohomology.mapIso (MulEquiv.ulift : ULift.{u} G ≃* G)
      (nativeCarrierEquiv A) (nativeCarrierEquiv_comm A) n)

/-- In a common universe this is the existing integral homology owner via actual chains. -/
def homologyIsoCommon (A : Rep.{u} ℤ G) (n : ℕ) :
    homology A n ≅ IntegralGroupCohomology.homology A n :=
  IntegralGroupCohomology.integerScalars.mapIso
    (groupHomology.mapIso (MulEquiv.ulift : ULift.{u} G ≃* G)
      (nativeCarrierEquiv A) (nativeCarrierEquiv_comm A) n)

variable [Fintype G]

/-- In a common universe the entire Tate comparison includes the actual connecting norm. -/
def tateIsoCommon (A : Rep.{u} ℤ G) (n : ℤ) :
    tate A n ≅ IntegralGroupCohomology.tate A n :=
  IntegralGroupCohomology.integerScalars.mapIso
    (TateCohomology.groupEquivIso (MulEquiv.ulift : ULift.{u} G ≃* G)
      (nativeCarrierEquiv A) (nativeCarrierEquiv_comm A) n)

end Common

section Original

variable {H : Type} [Group H] (A : Rep.{0} ℤ H)

/-- Universe-zero cohomology recovers the original literal integer API. -/
def cohomologyIsoOriginal (n : ℕ) : cohomology A n ≅ groupCohomology A n :=
  cohomologyIsoCommon A n ≪≫ IntegralGroupCohomology.cohomologyIsoOriginal A n

/-- Universe-zero homology recovers the original literal integer API. -/
def homologyIsoOriginal (n : ℕ) : homology A n ≅ groupHomology A n :=
  homologyIsoCommon A n ≪≫ IntegralGroupCohomology.homologyIsoOriginal A n

variable [Fintype H]

/-- Universe-zero Tate cohomology recovers the original literal API in every degree. -/
def tateIsoOriginal (n : ℤ) : tate A n ≅ tateCohomology A n :=
  tateIsoCommon A n ≪≫ IntegralGroupCohomology.tateIsoOriginal A n

/-- Tate finiteness is exactly the original finiteness condition in universe zero. -/
theorem finite_tate_iff_original (n : ℤ) :
    Finite (tate A n) ↔ Finite (tateCohomology A n) := by
  constructor
  · intro h
    let : Finite (tate A n) := h
    exact Finite.of_equiv _ (tateIsoOriginal A n).toLinearEquiv.toEquiv
  · intro h
    let : Finite (tateCohomology A n) := h
    exact Finite.of_equiv _ (tateIsoOriginal A n).symm.toLinearEquiv.toEquiv

/-- The natural-valued Tate cardinality retains its original meaning. -/
theorem card_tate_eq_original (n : ℤ) :
    Nat.card (tate A n) = Nat.card (tateCohomology A n) :=
  Nat.card_congr (tateIsoOriginal A n).toLinearEquiv.toEquiv

/-- The Tate vanishing proposition retains its original meaning. -/
theorem isZero_tate_iff_original (n : ℤ) :
    Limits.IsZero (tate A n) ↔ Limits.IsZero (tateCohomology A n) :=
  ⟨fun h => Limits.IsZero.of_iso h (tateIsoOriginal A n).symm,
    fun h => Limits.IsZero.of_iso h (tateIsoOriginal A n)⟩

end Original

end IntegralGroupCohomology.Universe
