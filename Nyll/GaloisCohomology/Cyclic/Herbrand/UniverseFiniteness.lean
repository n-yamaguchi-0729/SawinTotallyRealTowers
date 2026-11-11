/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Module.ULift
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality

/-!
# Herbrand finiteness for independently sized coefficient modules

The same homomorphisms and actions are lifted into one working coefficient universe.
The existing equivariant quotient comparisons remove those lifts from both arithmetic
Herbrand groups. Thus the original kernel/image sequence and its norm quotient are preserved.
No finite-dimensionality, smallness, or new comparison hypothesis is imposed.
-/

@[expose] public section

noncomputable section

universe u v w x r

namespace CyclicCohomology.ProfiniteCohomology.Herbrand.Universe

private def liftHom {A : Type v} {B : Type w} [CommGroup A] [CommGroup B]
    (f : A →* B) : ULift.{r} A →* ULift.{r} B where
  toFun a := ULift.up (f a.down)
  map_one' := congrArg ULift.up (map_one f)
  map_mul' a b := congrArg ULift.up (map_mul f a.down b.down)

private theorem liftHom_injective {A : Type v} {B : Type w} [CommGroup A] [CommGroup B]
    (f : A →* B) (hf : Function.Injective f) : Function.Injective (liftHom.{v,w,r} f) := by
  intro a b h
  apply ULift.ext
  exact hf (congrArg ULift.down h)

private theorem liftHom_surjective {A : Type v} {B : Type w} [CommGroup A] [CommGroup B]
    (f : A →* B) (hf : Function.Surjective f) : Function.Surjective (liftHom.{v,w,r} f) := by
  intro b
  rcases hf b.down with ⟨a, ha⟩
  exact ⟨ULift.up a, congrArg ULift.up ha⟩

private theorem liftHom_exact {A : Type v} {B : Type w} {C : Type x}
    [CommGroup A] [CommGroup B] [CommGroup C] (i : A →* B) (j : B →* C)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b) :
    ∀ b : ULift.{r} B, liftHom j b = 1 ↔ ∃ a : ULift.{r} A, liftHom i a = b := by
  intro b
  constructor
  · intro hb
    rcases (hker b.down).1 (congrArg ULift.down hb) with ⟨a, ha⟩
    exact ⟨ULift.up a, congrArg ULift.up ha⟩
  · rintro ⟨a, rfl⟩
    exact congrArg ULift.up ((hker (i a.down)).2 ⟨a.down, rfl⟩)

private theorem liftHom_equivariant {G : Type u} {A : Type v} {B : Type w}
    [Group G] [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A] [MulDistribMulAction G B] (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    ∀ (g : G) (a : ULift.{r} A), liftHom f (g • a) = g • liftHom f a :=
  fun g a => congrArg ULift.up (hf g a.down)

variable {G : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]

private theorem defined_ulift_iff (σ : G) :
    HerbrandQuotientDefined G (ULift.{r} A) σ ↔ HerbrandQuotientDefined G A σ := by
  let e : ULift.{r} A ≃* A := MulEquiv.ulift
  constructor
  · rintro ⟨h0, hm⟩
    let : Finite (HerbrandH0 G (ULift.{r} A)) := h0
    let : Finite (HerbrandHMinusOne G (ULift.{r} A) σ) := hm
    exact ⟨herbrandH0Finite_of_equivariantMulEquiv (G := G) e (fun _ _ => rfl),
      herbrandHMinusOneFinite_of_equivariantMulEquiv (G := G) e (fun _ _ => rfl) σ⟩
  · rintro ⟨h0, hm⟩
    let : Finite (HerbrandH0 G A) := h0
    let : Finite (HerbrandHMinusOne G A σ) := hm
    exact ⟨herbrandH0Finite_of_equivariantMulEquiv (G := G) e.symm (fun _ _ => rfl),
      herbrandHMinusOneFinite_of_equivariantMulEquiv (G := G) e.symm (fun _ _ => rfl) σ⟩

/-- Any two defined Herbrand quotients imply the third for the same actual exact maps,
with independent universes for the group and all three coefficient modules. -/
theorem herbrandQuotientDefined_anyTwo
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    (HerbrandQuotientDefined G A σ ∧ HerbrandQuotientDefined G B σ →
        HerbrandQuotientDefined G C σ) ∧
      (HerbrandQuotientDefined G A σ ∧ HerbrandQuotientDefined G C σ →
        HerbrandQuotientDefined G B σ) ∧
      (HerbrandQuotientDefined G B σ ∧ HerbrandQuotientDefined G C σ →
        HerbrandQuotientDefined G A σ) := by
  let i' : ULift.{max v w x} A →* ULift.{max v w x} B := liftHom i
  let j' : ULift.{max v w x} B →* ULift.{max v w x} C := liftHom j
  have h := CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotientDefined_anyTwo
    i' j'
    (liftHom_equivariant i hi) (liftHom_equivariant j hj) (liftHom_exact i j hker)
    (liftHom_injective i hinj) (liftHom_surjective j hsurj) σ hgen
  have hA : HerbrandQuotientDefined G (ULift.{max v w x} A) σ ↔
      HerbrandQuotientDefined G A σ := defined_ulift_iff σ
  have hB : HerbrandQuotientDefined G (ULift.{max v w x} B) σ ↔
      HerbrandQuotientDefined G B σ := defined_ulift_iff σ
  have hC : HerbrandQuotientDefined G (ULift.{max v w x} C) σ ↔
      HerbrandQuotientDefined G C σ := defined_ulift_iff σ
  exact ⟨fun ⟨ha, hb⟩ => hC.mp (h.1 ⟨hA.mpr ha, hB.mpr hb⟩),
    (fun ⟨ha, hc⟩ => hB.mp (h.2.1 ⟨hA.mpr ha, hC.mpr hc⟩)),
    fun ⟨hb, hc⟩ => hA.mp (h.2.2 ⟨hB.mpr hb, hC.mpr hc⟩)⟩

/-- Transfer finiteness along the original exact maps after removing coefficient lifts. -/
theorem herbrandQuotientDefined_right_of_left_middle
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hA : HerbrandQuotientDefined G A σ)
    (hB : HerbrandQuotientDefined G B σ) :
    HerbrandQuotientDefined G C σ :=
  (herbrandQuotientDefined_anyTwo i j hi hj hker hinj hsurj σ hgen).1
    ⟨hA, hB⟩

/-- Transfer finiteness along the original exact maps after removing coefficient lifts. -/
theorem herbrandQuotientDefined_middle_of_left_right
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hA : HerbrandQuotientDefined G A σ)
    (hC : HerbrandQuotientDefined G C σ) :
    HerbrandQuotientDefined G B σ :=
  (herbrandQuotientDefined_anyTwo i j hi hj hker hinj hsurj σ hgen).2.1
    ⟨hA, hC⟩

/-- Transfer finiteness along the original exact maps after removing coefficient lifts. -/
theorem herbrandQuotientDefined_left_of_middle_right
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hB : HerbrandQuotientDefined G B σ)
    (hC : HerbrandQuotientDefined G C σ) :
    HerbrandQuotientDefined G A σ :=
  (herbrandQuotientDefined_anyTwo i j hi hj hker hinj hsurj σ hgen).2.2
    ⟨hB, hC⟩

/-- The cardinality identity for the original Herbrand quotients survives only the actual
coefficient lifts, with no equality assumption between independently selected comparisons. -/
theorem herbrand_exact_cardinality_identity
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    Nat.card (HerbrandH0 G B) * Nat.card (HerbrandHMinusOne G A σ) *
        Nat.card (HerbrandHMinusOne G C σ) =
      Nat.card (HerbrandH0 G A) * Nat.card (HerbrandH0 G C) *
        Nat.card (HerbrandHMinusOne G B σ) := by
  let i' : ULift.{max v w x} A →* ULift.{max v w x} B := liftHom i
  let j' : ULift.{max v w x} B →* ULift.{max v w x} C := liftHom j
  have hA : HerbrandQuotientDefined G (ULift.{max v w x} A) σ :=
    (defined_ulift_iff σ).mpr ⟨inferInstance, inferInstance⟩
  let : Finite (HerbrandH0 G (ULift.{max v w x} A)) := hA.1
  let : Finite (HerbrandHMinusOne G (ULift.{max v w x} A) σ) := hA.2
  have hA0 : Nat.card (HerbrandH0 G (ULift.{max v w x} A)) =
      Nat.card (HerbrandH0 G A) :=
    Nat.card_congr (herbrandH0EquivariantMulEquiv (G := G)
      (MulEquiv.ulift : ULift.{max v w x} A ≃* A) (fun _ _ => rfl)).toEquiv
  have hAm : Nat.card (HerbrandHMinusOne G (ULift.{max v w x} A) σ) =
      Nat.card (HerbrandHMinusOne G A σ) :=
    Nat.card_congr (herbrandHMinusOneEquivariantMulEquiv (G := G)
      (MulEquiv.ulift : ULift.{max v w x} A ≃* A) (fun _ _ => rfl) σ).toEquiv
  have hB : HerbrandQuotientDefined G (ULift.{max v w x} B) σ :=
    (defined_ulift_iff σ).mpr ⟨inferInstance, inferInstance⟩
  let : Finite (HerbrandH0 G (ULift.{max v w x} B)) := hB.1
  let : Finite (HerbrandHMinusOne G (ULift.{max v w x} B) σ) := hB.2
  have hB0 : Nat.card (HerbrandH0 G (ULift.{max v w x} B)) =
      Nat.card (HerbrandH0 G B) :=
    Nat.card_congr (herbrandH0EquivariantMulEquiv (G := G)
      (MulEquiv.ulift : ULift.{max v w x} B ≃* B) (fun _ _ => rfl)).toEquiv
  have hBm : Nat.card (HerbrandHMinusOne G (ULift.{max v w x} B) σ) =
      Nat.card (HerbrandHMinusOne G B σ) :=
    Nat.card_congr (herbrandHMinusOneEquivariantMulEquiv (G := G)
      (MulEquiv.ulift : ULift.{max v w x} B ≃* B) (fun _ _ => rfl) σ).toEquiv
  have hC : HerbrandQuotientDefined G (ULift.{max v w x} C) σ :=
    (defined_ulift_iff σ).mpr ⟨inferInstance, inferInstance⟩
  let : Finite (HerbrandH0 G (ULift.{max v w x} C)) := hC.1
  let : Finite (HerbrandHMinusOne G (ULift.{max v w x} C) σ) := hC.2
  have hC0 : Nat.card (HerbrandH0 G (ULift.{max v w x} C)) =
      Nat.card (HerbrandH0 G C) :=
    Nat.card_congr (herbrandH0EquivariantMulEquiv (G := G)
      (MulEquiv.ulift : ULift.{max v w x} C ≃* C) (fun _ _ => rfl)).toEquiv
  have hCm : Nat.card (HerbrandHMinusOne G (ULift.{max v w x} C) σ) =
      Nat.card (HerbrandHMinusOne G C σ) :=
    Nat.card_congr (herbrandHMinusOneEquivariantMulEquiv (G := G)
      (MulEquiv.ulift : ULift.{max v w x} C ≃* C) (fun _ _ => rfl) σ).toEquiv
  have h := CyclicCohomology.ProfiniteCohomology.Herbrand.herbrand_exact_cardinality_identity
    i' j'
    (liftHom_equivariant i hi) (liftHom_equivariant j hj) (liftHom_exact i j hker)
    (liftHom_injective i hinj) (liftHom_surjective j hsurj) σ hgen
  rw [hA0, hAm, hB0, hBm, hC0, hCm] at h
  exact h

/-- The original Herbrand quotient is multiplicative for an actual short exact sequence
of independently sized coefficient modules. -/
theorem herbrandQuotient_multiplicative_of_shortExact
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    herbrandQuotient (G := G) (A := B) σ =
      herbrandQuotient (G := G) (A := A) σ *
        herbrandQuotient (G := G) (A := C) σ := by
  have hcard := herbrand_exact_cardinality_identity i j hi hj hker hinj hsurj σ hgen
  have hA : (Nat.card (HerbrandHMinusOne G A σ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finite.card_pos (α := HerbrandHMinusOne G A σ)).ne'
  have hB : (Nat.card (HerbrandHMinusOne G B σ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finite.card_pos (α := HerbrandHMinusOne G B σ)).ne'
  have hC : (Nat.card (HerbrandHMinusOne G C σ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finite.card_pos (α := HerbrandHMinusOne G C σ)).ne'
  unfold herbrandQuotient
  field_simp [hA, hB, hC]
  have hcardQ :
      (Nat.card (HerbrandH0 G B) : ℚ) * Nat.card (HerbrandHMinusOne G A σ) *
          Nat.card (HerbrandHMinusOne G C σ) =
        Nat.card (HerbrandH0 G A) * Nat.card (HerbrandH0 G C) *
          Nat.card (HerbrandHMinusOne G B σ) := by
    exact_mod_cast hcard
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hcardQ

end CyclicCohomology.ProfiniteCohomology.Herbrand.Universe
