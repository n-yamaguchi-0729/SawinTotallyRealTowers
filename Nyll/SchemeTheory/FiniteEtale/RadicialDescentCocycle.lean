/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.RadicialDescentIso
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The cocycle for the canonical radicial comparison

The threefold fiber product is viewed as two copies of `X ×[Y] X` with
their first coordinates identified. Its small diagonal is the composite of
two diagonals. Both are surjective closed immersions for a separated
universally injective morphism. Faithfulness along this small diagonal
detects the cocycle equation.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteEtale

variable {X Y T : Scheme.{u}}

/-- The threefold fiber product, with the first coordinate shared by the two pairs. -/
def radicialTriple (f : X ⟶ Y) : Scheme.{u} :=
  Limits.pullback (Limits.pullback.fst f f) (Limits.pullback.fst f f)

/-- The small diagonal in the chosen threefold fiber product. -/
def radicialTripleDiagonal (f : X ⟶ Y) : X ⟶ radicialTriple f :=
  Limits.pullback.diagonal f ≫ Limits.pullback.diagonal (Limits.pullback.fst f f)

/-- The small diagonal is a closed immersion when the original map is separated. -/
instance (f : X ⟶ Y) [IsSeparated f] : IsClosedImmersion (radicialTripleDiagonal f) := by
  let : IsSeparated (Limits.pullback.fst f f) :=
    MorphismProperty.of_isPullback
      (P := (@IsSeparated : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f f).flip inferInstance
  let : IsClosedImmersion (Limits.pullback.diagonal f) := inferInstance
  let : IsClosedImmersion (Limits.pullback.diagonal (Limits.pullback.fst f f)) :=
    inferInstance
  dsimp only [radicialTripleDiagonal]
  exact IsClosedImmersion.comp (Limits.pullback.diagonal f)
    (Limits.pullback.diagonal (Limits.pullback.fst f f))

/-- Universal injectivity makes the small diagonal surjective. -/
instance (f : X ⟶ Y) [UniversallyInjective f] : Surjective (radicialTripleDiagonal f) := by
  let : Surjective (Limits.pullback.diagonal f) :=
    (UniversallyInjective.iff_diagonal f).mp inferInstance
  let : UniversallyInjective (Limits.pullback.fst f f) :=
    MorphismProperty.of_isPullback
      (P := (@UniversallyInjective : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f f).flip inferInstance
  let : Surjective (Limits.pullback.diagonal (Limits.pullback.fst f f)) :=
    (UniversallyInjective.iff_diagonal (Limits.pullback.fst f f)).mp inferInstance
  dsimp only [radicialTripleDiagonal]
  exact ⟨(Limits.pullback.diagonal (Limits.pullback.fst f f)).surjective.comp
    (Limits.pullback.diagonal f).surjective⟩

/-- The map from the pullback of V along a to its pullback along the first projection of the
fiber product, induced by the pair a and b over Y. -/
def pairLift (f : X ⟶ Y) (V : Over X)
    (a b : T ⟶ X) (w : a ≫ f = b ≫ f) :
    ((Over.pullback a).obj V).left ⟶
      ((Over.pullback (Limits.pullback.fst f f)).obj V).left :=
  Limits.pullback.lift (Limits.pullback.fst V.hom a)
    (Limits.pullback.snd V.hom a ≫ Limits.pullback.lift a b w) (by
      rw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.condition])

@[reassoc]
lemma pairLift_fst (f : X ⟶ Y) (V : Over X)
    (a b : T ⟶ X) (w : a ≫ f = b ≫ f) :
    pairLift f V a b w ≫ Limits.pullback.fst V.hom (Limits.pullback.fst f f) =
      Limits.pullback.fst V.hom a :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
lemma pairLift_snd (f : X ⟶ Y) (V : Over X)
    (a b : T ⟶ X) (w : a ≫ f = b ≫ f) :
    pairLift f V a b w ≫ Limits.pullback.snd V.hom (Limits.pullback.fst f f) =
      Limits.pullback.snd V.hom a ≫ Limits.pullback.lift a b w :=
  Limits.pullback.lift_snd _ _ _

/-- Reindex a morphism between the two pullbacks to a pair of maps with the
same composite to the base. This uses the actual universal pullback maps. -/
def pairHom (f : X ⟶ Y) (V : Over X)
    (η : (Over.pullback (Limits.pullback.fst f f)).obj V ⟶
      (Over.pullback (Limits.pullback.snd f f)).obj V)
    (a b : T ⟶ X) (w : a ≫ f = b ≫ f) :
    (Over.pullback a).obj V ⟶ (Over.pullback b).obj V :=
  Over.homMk (Limits.pullback.lift
    (pairLift f V a b w ≫ η.left ≫
      Limits.pullback.fst V.hom (Limits.pullback.snd f f))
    (Limits.pullback.snd V.hom a) (by
      have hη : η.left ≫ Limits.pullback.snd V.hom (Limits.pullback.snd f f) =
          Limits.pullback.snd V.hom (Limits.pullback.fst f f) := by
        simpa only [Over.pullback_obj_hom] using Over.w η
      calc
        _ = pairLift f V a b w ≫ η.left ≫
            Limits.pullback.snd V.hom (Limits.pullback.snd f f) ≫
            Limits.pullback.snd f f := by
          simp only [Category.assoc, Limits.pullback.condition]
        _ = pairLift f V a b w ≫
            Limits.pullback.snd V.hom (Limits.pullback.fst f f) ≫
            Limits.pullback.snd f f := by
          simp only [← Category.assoc, hη]
        _ = Limits.pullback.snd V.hom a ≫ Limits.pullback.lift a b w ≫
            Limits.pullback.snd f f := by
          rw [← Category.assoc, pairLift_snd]
          simp only [Category.assoc]
        _ = _ := by simp only [Limits.pullback.lift_snd]))
    (Limits.pullback.lift_snd _ _ _)

@[reassoc]
private lemma pairHom_fst (f : X ⟶ Y) (V : Over X)
    (η : (Over.pullback (Limits.pullback.fst f f)).obj V ⟶
      (Over.pullback (Limits.pullback.snd f f)).obj V)
    (a b : T ⟶ X) (w : a ≫ f = b ≫ f) :
    (pairHom f V η a b w).left ≫ Limits.pullback.fst V.hom b =
      pairLift f V a b w ≫ η.left ≫
        Limits.pullback.fst V.hom (Limits.pullback.snd f f) :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
private lemma pairHom_snd (f : X ⟶ Y) (V : Over X)
    (η : (Over.pullback (Limits.pullback.fst f f)).obj V ⟶
      (Over.pullback (Limits.pullback.snd f f)).obj V)
    (a b : T ⟶ X) (w : a ≫ f = b ≫ f) :
    (pairHom f V η a b w).left ≫ Limits.pullback.snd V.hom b =
      Limits.pullback.snd V.hom a :=
  Limits.pullback.lift_snd _ _ _

/-- The canonical comparison on any pair of maps into `X` over `Y`. -/
def radicialDescentHom (f : X ⟶ Y) [IsSeparated f] [UniversallyInjective f]
    (V : finiteEtaleProperty.Over ⊤ X) (a b : T ⟶ X) (w : a ≫ f = b ≫ f) :
    (Over.pullback a).obj V.toComma ⟶ (Over.pullback b).obj V.toComma :=
  pairHom f V.toComma ((radicialDescentIso f).hom.app V).hom a b w

private def restrictionSection (V : Over X) (d : X ⟶ T) (a : T ⟶ X)
    (ha : d ≫ a = 𝟙 X) : V.left ⟶ ((Over.pullback a).obj V).left :=
  Limits.pullback.lift (𝟙 V.left) (V.hom ≫ d) (by
    simp only [Category.id_comp, Category.assoc, ha, Category.comp_id])

@[reassoc]
private lemma restrictionSection_fst (V : Over X) (d : X ⟶ T) (a : T ⟶ X)
    (ha : d ≫ a = 𝟙 X) :
    restrictionSection V d a ha ≫ Limits.pullback.fst V.hom a = 𝟙 V.left :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
private lemma restrictionSection_snd (V : Over X) (d : X ⟶ T) (a : T ⟶ X)
    (ha : d ≫ a = 𝟙 X) :
    restrictionSection V d a ha ≫ Limits.pullback.snd V.hom a = V.hom ≫ d :=
  Limits.pullback.lift_snd _ _ _

private lemma restrictionSection_pairLift (f : X ⟶ Y) (V : Over X)
    (d : X ⟶ T) (a b : T ⟶ X) (w : a ≫ f = b ≫ f)
    (ha : d ≫ a = 𝟙 X) (hb : d ≫ b = 𝟙 X) :
    restrictionSection V d a ha ≫ pairLift f V a b w =
      restrictionSection V (Limits.pullback.diagonal f) (Limits.pullback.fst f f)
        (Limits.pullback.diagonal_fst f) := by
  have hpair : d ≫ Limits.pullback.lift a b w = Limits.pullback.diagonal f := by
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, Limits.pullback.lift_fst, ha, Limits.pullback.diagonal_fst]
    · simp only [Category.assoc, Limits.pullback.lift_snd, hb, Limits.pullback.diagonal_snd]
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, pairLift_fst, restrictionSection_fst]
  · simp only [Category.assoc, pairLift_snd, restrictionSection_snd_assoc,
      hpair, restrictionSection_snd]

private lemma pairHom_restrictionSection (f : X ⟶ Y) (V : Over X)
    (η : (Over.pullback (Limits.pullback.fst f f)).obj V ⟶
      (Over.pullback (Limits.pullback.snd f f)).obj V)
    (hη : restrictionSection V (Limits.pullback.diagonal f) (Limits.pullback.fst f f)
        (Limits.pullback.diagonal_fst f) ≫ η.left =
      restrictionSection V (Limits.pullback.diagonal f) (Limits.pullback.snd f f)
        (Limits.pullback.diagonal_snd f))
    (d : X ⟶ T) (a b : T ⟶ X) (w : a ≫ f = b ≫ f)
    (ha : d ≫ a = 𝟙 X) (hb : d ≫ b = 𝟙 X) :
    restrictionSection V d a ha ≫ (pairHom f V η a b w).left =
      restrictionSection V d b hb := by
  have hL := restrictionSection_pairLift f V d a b w ha hb
  apply Limits.pullback.hom_ext
  · calc
      _ = (restrictionSection V d a ha ≫ pairLift f V a b w) ≫ η.left ≫
          Limits.pullback.fst V.hom (Limits.pullback.snd f f) := by
        simp only [Category.assoc, pairHom_fst]
      _ = (restrictionSection V (Limits.pullback.diagonal f) (Limits.pullback.fst f f)
          (Limits.pullback.diagonal_fst f) ≫ η.left) ≫
          Limits.pullback.fst V.hom (Limits.pullback.snd f f) := by
        rw [hL, Category.assoc]
      _ = 𝟙 V.left := by rw [hη, restrictionSection_fst]
      _ = _ := (restrictionSection_fst V d b hb).symm
  · simp only [Category.assoc, pairHom_snd, restrictionSection_snd]

private lemma hom_ext_of_restrictionSection (V : finiteEtaleProperty.Over ⊤ X)
    (d : X ⟶ T) [IsClosedImmersion d] [Surjective d]
    (a b : T ⟶ X) (ha : d ≫ a = 𝟙 X)
    (g h : (Over.pullback a).obj V.toComma ⟶ (Over.pullback b).obj V.toComma)
    (hgh : restrictionSection V.toComma d a ha ≫ g.left =
      restrictionSection V.toComma d a ha ≫ h.left) : g = h := by
  let : IsFinite V.hom := V.prop.1
  let : Etale V.hom := V.prop.2
  let k := Limits.pullback.fst (Limits.pullback.snd V.hom a) d
  let r := k ≫ Limits.pullback.fst V.hom a
  have hr : r ≫ V.hom = Limits.pullback.snd (Limits.pullback.snd V.hom a) d := by
    dsimp only [r, k]
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
      Limits.pullback.condition, Category.assoc, ha, Category.comp_id]
  have hfactor : r ≫ restrictionSection V.toComma d a ha = k := by
    apply Limits.pullback.hom_ext
    · change r ≫ restrictionSection V.toComma d a ha ≫
          Limits.pullback.fst V.hom a = k ≫ Limits.pullback.fst V.hom a
      simp only [restrictionSection_fst]
      change (k ≫ Limits.pullback.fst V.hom a) ≫ 𝟙 V.left =
        k ≫ Limits.pullback.fst V.hom a
      exact Category.comp_id _
    · rw [Category.assoc, restrictionSection_snd, ← Category.assoc, hr]
      exact Limits.pullback.condition.symm
  let : IsFinite ((Over.pullback a).obj V.toComma).hom := by
    simpa only [Over.pullback_obj_hom] using
      (inferInstance : IsFinite (Limits.pullback.snd V.hom a))
  let : IsFinite ((Over.pullback b).obj V.toComma).hom := by
    simpa only [Over.pullback_obj_hom] using
      (inferInstance : IsFinite (Limits.pullback.snd V.hom b))
  let : Etale ((Over.pullback a).obj V.toComma).hom := by
    simpa only [Over.pullback_obj_hom] using
      (inferInstance : Etale (Limits.pullback.snd V.hom a))
  let : Etale ((Over.pullback b).obj V.toComma).hom := by
    simpa only [Over.pullback_obj_hom] using
      (inferInstance : Etale (Limits.pullback.snd V.hom b))
  apply (pullback_map_bijective_to_finiteEtale d
    ((Over.pullback a).obj V.toComma) ((Over.pullback b).obj V.toComma)).1
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · simp only [Over.pullback_map_left, Limits.pullback.lift_fst]
    change k ≫ g.left = k ≫ h.left
    rw [← hfactor]
    simp only [Category.assoc, hgh]
  · simp only [Over.pullback_map_left, Limits.pullback.lift_snd]

/-- On the universal pair, reindexing recovers the original comparison. -/
theorem radicialDescentHom_projections
    (f : X ⟶ Y) [IsSeparated f] [UniversallyInjective f] (V : finiteEtaleProperty.Over ⊤ X) :
    radicialDescentHom f V (Limits.pullback.fst f f) (Limits.pullback.snd f f)
        Limits.pullback.condition = ((radicialDescentIso f).hom.app V).hom := by
  have hL : pairLift f V.toComma (Limits.pullback.fst f f) (Limits.pullback.snd f f)
      Limits.pullback.condition = 𝟙 _ := by
    apply Limits.pullback.hom_ext
    · simp [pairLift]
    · simp [pairLift]
  let η : (Over.pullback (Limits.pullback.fst f f)).obj V.toComma ⟶
      (Over.pullback (Limits.pullback.snd f f)).obj V.toComma :=
    ((radicialDescentIso f).hom.app V).hom
  change pairHom f V.toComma η _ _ _ = η
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · rw [pairHom_fst, hL, Category.id_comp]
  · rw [pairHom_snd]
    exact (Over.w η).symm

private lemma radicialDescentHom_restrictionSection
    (f : X ⟶ Y) [IsSeparated f] [UniversallyInjective f] (V : finiteEtaleProperty.Over ⊤ X)
    (d : X ⟶ T) (a b : T ⟶ X) (w : a ≫ f = b ≫ f)
    (ha : d ≫ a = 𝟙 X) (hb : d ≫ b = 𝟙 X) :
    restrictionSection V.toComma d a ha ≫ (radicialDescentHom f V a b w).left =
      restrictionSection V.toComma d b hb :=
  pairHom_restrictionSection f V.toComma ((radicialDescentIso f).hom.app V).hom
    (radicialDescentIso_diagonal_section f V) d a b w ha hb

/-- Comparisons satisfy the cocycle whenever a surjective closed section
simultaneously identifies the three coordinates with `X`. -/
theorem radicialDescentHom_cocycle_of_section
    (f : X ⟶ Y) [IsSeparated f] [UniversallyInjective f] (V : finiteEtaleProperty.Over ⊤ X)
    (d : X ⟶ T) [IsClosedImmersion d] [Surjective d]
    (a b c : T ⟶ X) (wab : a ≫ f = b ≫ f) (wbc : b ≫ f = c ≫ f)
    (ha : d ≫ a = 𝟙 X) (hb : d ≫ b = 𝟙 X) (hc : d ≫ c = 𝟙 X) :
    radicialDescentHom f V a b wab ≫ radicialDescentHom f V b c wbc =
      radicialDescentHom f V a c (wab.trans wbc) := by
  apply hom_ext_of_restrictionSection V d a c ha
  change restrictionSection V.toComma d a ha ≫
      ((radicialDescentHom f V a b wab).left ≫
        (radicialDescentHom f V b c wbc).left) = _
  rw [← Category.assoc, radicialDescentHom_restrictionSection f V d a b wab ha hb,
    radicialDescentHom_restrictionSection f V d b c wbc hb hc,
    radicialDescentHom_restrictionSection f V d a c (wab.trans wbc) ha hc]

/-- The first coordinate of the threefold fiber product. -/
def radicialTripleFirst (f : X ⟶ Y) : radicialTriple f ⟶ X :=
  Limits.pullback.fst (Limits.pullback.fst f f) (Limits.pullback.fst f f) ≫
    Limits.pullback.fst f f

/-- The second coordinate of the threefold fiber product. -/
def radicialTripleSecond (f : X ⟶ Y) : radicialTriple f ⟶ X :=
  Limits.pullback.fst (Limits.pullback.fst f f) (Limits.pullback.fst f f) ≫
    Limits.pullback.snd f f

/-- The third coordinate of the threefold fiber product. -/
def radicialTripleThird (f : X ⟶ Y) : radicialTriple f ⟶ X :=
  Limits.pullback.snd (Limits.pullback.fst f f) (Limits.pullback.fst f f) ≫
    Limits.pullback.snd f f

@[reassoc]
theorem radicialTripleDiagonal_first (f : X ⟶ Y) :
    radicialTripleDiagonal f ≫ radicialTripleFirst f = 𝟙 X := by
  change (Limits.pullback.diagonal f ≫ Limits.pullback.diagonal (Limits.pullback.fst f f)) ≫
    Limits.pullback.fst (Limits.pullback.fst f f) (Limits.pullback.fst f f) ≫
      Limits.pullback.fst f f = 𝟙 X
  rw [Category.assoc, Limits.pullback.diagonal_fst_assoc,
    Limits.pullback.diagonal_fst]

@[reassoc]
theorem radicialTripleDiagonal_second (f : X ⟶ Y) :
    radicialTripleDiagonal f ≫ radicialTripleSecond f = 𝟙 X := by
  change (Limits.pullback.diagonal f ≫ Limits.pullback.diagonal (Limits.pullback.fst f f)) ≫
    Limits.pullback.fst (Limits.pullback.fst f f) (Limits.pullback.fst f f) ≫
      Limits.pullback.snd f f = 𝟙 X
  rw [Category.assoc, Limits.pullback.diagonal_fst_assoc,
    Limits.pullback.diagonal_snd]

@[reassoc]
theorem radicialTripleDiagonal_third (f : X ⟶ Y) :
    radicialTripleDiagonal f ≫ radicialTripleThird f = 𝟙 X := by
  change (Limits.pullback.diagonal f ≫ Limits.pullback.diagonal (Limits.pullback.fst f f)) ≫
    Limits.pullback.snd (Limits.pullback.fst f f) (Limits.pullback.fst f f) ≫
      Limits.pullback.snd f f = 𝟙 X
  rw [Category.assoc, Limits.pullback.diagonal_snd_assoc,
    Limits.pullback.diagonal_snd]

theorem radicialTriple_first_second (f : X ⟶ Y) :
    radicialTripleFirst f ≫ f = radicialTripleSecond f ≫ f := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k : Limits.pullback f f ⟶ Y =>
      Limits.pullback.fst (Limits.pullback.fst f f) (Limits.pullback.fst f f) ≫ k)
      (Limits.pullback.condition : Limits.pullback.fst f f ≫ f =
        Limits.pullback.snd f f ≫ f)).trans (Category.assoc _ _ _).symm)

theorem radicialTriple_first_third (f : X ⟶ Y) :
    radicialTripleFirst f ≫ f = radicialTripleThird f ≫ f := by
  calc
    _ = (Limits.pullback.snd (Limits.pullback.fst f f) (Limits.pullback.fst f f) ≫
        Limits.pullback.fst f f) ≫ f :=
      congrArg (fun k ↦ k ≫ f) Limits.pullback.condition
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun k : Limits.pullback f f ⟶ Y =>
          Limits.pullback.snd (Limits.pullback.fst f f) (Limits.pullback.fst f f) ≫ k)
        (Limits.pullback.condition : Limits.pullback.fst f f ≫ f =
          Limits.pullback.snd f f ≫ f)).trans (Category.assoc _ _ _).symm)

theorem radicialTriple_second_third (f : X ⟶ Y) :
    radicialTripleSecond f ≫ f = radicialTripleThird f ≫ f :=
  (radicialTriple_first_second f).symm.trans (radicialTriple_first_third f)

/-- The canonical radicial comparison satisfies the cocycle on the actual
threefold fiber product. The reindexed maps use universal pullback lifts. -/
theorem radicialDescentHom_cocycle
    (f : X ⟶ Y) [IsSeparated f] [UniversallyInjective f] (V : finiteEtaleProperty.Over ⊤ X) :
    radicialDescentHom f V (radicialTripleFirst f) (radicialTripleSecond f)
        (radicialTriple_first_second f) ≫
      radicialDescentHom f V (radicialTripleSecond f) (radicialTripleThird f)
        (radicialTriple_second_third f) =
      radicialDescentHom f V (radicialTripleFirst f) (radicialTripleThird f)
        (radicialTriple_first_third f) :=
  radicialDescentHom_cocycle_of_section f V (radicialTripleDiagonal f)
    (radicialTripleFirst f) (radicialTripleSecond f) (radicialTripleThird f)
    (radicialTriple_first_second f) (radicialTriple_second_third f)
    (radicialTripleDiagonal_first f) (radicialTripleDiagonal_second f)
    (radicialTripleDiagonal_third f)

end AlgebraicGeometry.FiniteEtale
