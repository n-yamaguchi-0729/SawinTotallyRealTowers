/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality

/-!
# Finiteness in the Herbrand exact hexagon

This file supplies the finiteness clause in Herbrand-quotient multiplicativity:
for a short exact sequence of modules over a finite cyclic group, if the Herbrand
quotients of any two terms are defined, then the quotient of the third term is
defined as well.
-/

@[expose] public section

namespace CyclicCohomology

noncomputable section

namespace ProfiniteCohomology
namespace Herbrand

open CategoryTheory

universe uG uA

variable {G : Type uG} {A B C : Type uA}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

/-- Herbrand-quotient multiplicativity, finiteness transfer from the first and third terms to
the middle term. -/
theorem herbrandQuotientDefined_middle_of_left_right
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hA : HerbrandQuotientDefined G A σ)
    (hC : HerbrandQuotientDefined G C σ) :
    HerbrandQuotientDefined G B σ :=
  (herbrandQuotientDefined_anyTwo_of_periodic i j hi hj hker hinj hsurj σ hgen).2.1
    ⟨hA, hC⟩

/-- Herbrand-quotient multiplicativity, finiteness transfer from the first and middle terms to
the third term. -/
theorem herbrandQuotientDefined_right_of_left_middle
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hA : HerbrandQuotientDefined G A σ)
    (hB : HerbrandQuotientDefined G B σ) :
    HerbrandQuotientDefined G C σ :=
  (herbrandQuotientDefined_anyTwo_of_periodic i j hi hj hker hinj hsurj σ hgen).1
    ⟨hA, hB⟩

/-- Herbrand-quotient multiplicativity, finiteness transfer from the middle and third terms to
the first term. -/
theorem herbrandQuotientDefined_left_of_middle_right
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hB : HerbrandQuotientDefined G B σ)
    (hC : HerbrandQuotientDefined G C σ) :
    HerbrandQuotientDefined G A σ :=
  (herbrandQuotientDefined_anyTwo_of_periodic i j hi hj hker hinj hsurj σ hgen).2.2
    ⟨hB, hC⟩

/-- Herbrand-quotient multiplicativity, the complete "any two imply the third" finiteness
statement for a short exact sequence. -/
theorem herbrandQuotientDefined_anyTwo
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    (HerbrandQuotientDefined G A σ ∧ HerbrandQuotientDefined G B σ →
        HerbrandQuotientDefined G C σ) ∧
      (HerbrandQuotientDefined G A σ ∧ HerbrandQuotientDefined G C σ →
        HerbrandQuotientDefined G B σ) ∧
      (HerbrandQuotientDefined G B σ ∧ HerbrandQuotientDefined G C σ →
        HerbrandQuotientDefined G A σ) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hA, hB⟩
    exact herbrandQuotientDefined_right_of_left_middle
      i j hi hj hker hinj hsurj σ hgen hA hB
  · rintro ⟨hA, hC⟩
    exact herbrandQuotientDefined_middle_of_left_right
      i j hi hj hker hinj hsurj σ hgen hA hC
  · rintro ⟨hB, hC⟩
    exact herbrandQuotientDefined_left_of_middle_right
      i j hi hj hker hinj hsurj σ hgen hB hC

/-- Herbrand-quotient multiplicativity, Herbrand-quotient multiplicativity once the three
quotients are defined. -/
theorem herbrandQuotient_multiplicative_of_shortExact
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    herbrandQuotient (G := G) (A := B) σ =
      herbrandQuotient (G := G) (A := A) σ *
        herbrandQuotient (G := G) (A := C) σ :=
  herbrandQuotient_exact_multiplicative
    i j hi hj hker hinj hsurj σ hgen

/-- Herbrand-quotient multiplicativity in its first two-defined form: if the quotients of `A`
and `C` are defined, the quotient of `B` is defined and multiplicativity
holds for that induced finiteness witness. -/
theorem herbrandQuotient_multiplicative_of_left_right_defined
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    ∃ hB : HerbrandQuotientDefined G B σ,
      @herbrandQuotient G B _ _ _ _ σ hB.1 hB.2 =
        herbrandQuotient (G := G) (A := A) σ *
          herbrandQuotient (G := G) (A := C) σ := by
  let hA : HerbrandQuotientDefined G A σ := ⟨inferInstance, inferInstance⟩
  let hC : HerbrandQuotientDefined G C σ := ⟨inferInstance, inferInstance⟩
  let hB := herbrandQuotientDefined_middle_of_left_right
    i j hi hj hker hinj hsurj σ hgen hA hC
  refine ⟨hB, ?_⟩
  let : Finite (HerbrandH0 G B) := hB.1
  let : Finite (HerbrandHMinusOne G B σ) := hB.2
  exact herbrandQuotient_multiplicative_of_shortExact
    i j hi hj hker hinj hsurj σ hgen

/-- Herbrand-quotient multiplicativity in its second two-defined form: if the quotients of `A`
and `B` are defined, the quotient of `C` is defined and multiplicativity
holds for that induced finiteness witness. -/
theorem herbrandQuotient_multiplicative_of_left_middle_defined
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)] :
    ∃ hC : HerbrandQuotientDefined G C σ,
      herbrandQuotient (G := G) (A := B) σ =
        herbrandQuotient (G := G) (A := A) σ *
          @herbrandQuotient G C _ _ _ _ σ hC.1 hC.2 := by
  let hA : HerbrandQuotientDefined G A σ := ⟨inferInstance, inferInstance⟩
  let hB : HerbrandQuotientDefined G B σ := ⟨inferInstance, inferInstance⟩
  let hC := herbrandQuotientDefined_right_of_left_middle
    i j hi hj hker hinj hsurj σ hgen hA hB
  refine ⟨hC, ?_⟩
  let : Finite (HerbrandH0 G C) := hC.1
  let : Finite (HerbrandHMinusOne G C σ) := hC.2
  exact herbrandQuotient_multiplicative_of_shortExact
    i j hi hj hker hinj hsurj σ hgen

/-- Herbrand-quotient multiplicativity in its third two-defined form: if the quotients of `B`
and `C` are defined, the quotient of `A` is defined and multiplicativity
holds for that induced finiteness witness. -/
theorem herbrandQuotient_multiplicative_of_middle_right_defined
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    ∃ hA : HerbrandQuotientDefined G A σ,
      herbrandQuotient (G := G) (A := B) σ =
        @herbrandQuotient G A _ _ _ _ σ hA.1 hA.2 *
          herbrandQuotient (G := G) (A := C) σ := by
  let hB : HerbrandQuotientDefined G B σ := ⟨inferInstance, inferInstance⟩
  let hC : HerbrandQuotientDefined G C σ := ⟨inferInstance, inferInstance⟩
  let hA := herbrandQuotientDefined_left_of_middle_right
    i j hi hj hker hinj hsurj σ hgen hB hC
  refine ⟨hA, ?_⟩
  let : Finite (HerbrandH0 G A) := hA.1
  let : Finite (HerbrandHMinusOne G A σ) := hA.2
  exact herbrandQuotient_multiplicative_of_shortExact
    i j hi hj hker hinj hsurj σ hgen

/-- Herbrand-quotient multiplicativity, the finite-module case. -/
theorem herbrandQuotient_eq_one_of_finite_module
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    herbrandQuotient (G := G) (A := A) σ = 1 :=
  herbrandQuotient_finite_module_eq_one σ hgen

end Herbrand
end ProfiniteCohomology

end
end CyclicCohomology
