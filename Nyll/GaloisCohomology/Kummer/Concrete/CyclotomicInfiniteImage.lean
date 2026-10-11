/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.GroupTheory.Torsion

/-!
# Infinite image of the cyclotomic character

A finite cyclotomic image would yield a finite fixed field containing all
primary roots of unity. The actual primitive roots contradict finiteness.
-/

namespace KummerTheory
universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]

/-- Roots of unbounded prime-power order give an infinite primary group. -/
theorem infinite_primaryComponent_of_primitive_roots
    (p : ℕ) [Fact p.Prime] [∀ i : ℕ, HasEnoughRootsOfUnity Ω (p ^ i)] :
    Infinite (CommGroup.primaryComponent Ωˣ p) := by
  classical
  choose ζ hζ using fun n => HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ n)
  let z (n : ℕ) : Ωˣ := (hζ n).isUnit (NeZero.ne (p ^ n)) |>.unit'
  have hz (n : ℕ) : IsPrimitiveRoot (z n) (p ^ n) :=
    (hζ n).isUnit_unit' (NeZero.ne (p ^ n))
  let f : ℕ → CommGroup.primaryComponent Ωˣ p :=
    fun n => ⟨z n, n, (hz n).pow_eq_one⟩
  apply Infinite.of_injective f
  intro a b hab
  apply Nat.pow_right_injective (Fact.out : p.Prime).one_lt
  have he : z a = z b := congrArg Subtype.val hab
  exact (IsPrimitiveRoot.iff_orderOf.mp (hz a)).symm.trans
    ((congrArg orderOf he).trans (IsPrimitiveRoot.iff_orderOf.mp (hz b)))

/-- Every primary root is fixed by the kernel of the cyclotomic character. -/
theorem primaryUnit_mem_fixedField_cyclotomic_ker
    (p : ℕ) [Fact p.Prime] [∀ i : ℕ, HasEnoughRootsOfUnity Ω (p ^ i)]
    (z : CommGroup.primaryComponent Ωˣ p) :
    (z.val : Ω) ∈ IntermediateField.fixedField
      ((cyclotomicCharacter Ω p).comp (MulSemiringAction.toRingAut Gal(Ω/K) Ω)).ker := by
  obtain ⟨n, hn⟩ := z.property
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ n)
  let η : Ωˣ := hζ.isUnit (NeZero.ne (p ^ n)) |>.unit'
  have hη : IsPrimitiveRoot η (p ^ n) := hζ.isUnit_unit' (NeZero.ne _)
  obtain ⟨a, ha⟩ := primitiveRootCoordinate_surjective_roots hη z.val hn
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hχ : cyclotomicCharacter Ω p σ.toRingEquiv = 1 := hσ
  have he := primitiveRootCoordinate_cyclotomic p n hη σ.toRingEquiv a
  rw [hχ, Units.val_one, map_one, one_mul, ha] at he
  exact congrArg Units.val he

/-- Finiteness of primary roots in finite subextensions forces infinite image. -/
theorem infinite_range_cyclotomicCharacter_of_finite_primary
    [IsGalois K Ω]
    (p : ℕ) [Fact p.Prime] [∀ i : ℕ, HasEnoughRootsOfUnity Ω (p ^ i)]
    (hRoots : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      Finite (CommGroup.primaryComponent Eˣ p)) :
    Set.Infinite (Set.range
      ((cyclotomicCharacter Ω p).comp (MulSemiringAction.toRingAut Gal(Ω/K) Ω))) := by
  classical
  let χ : Gal(Ω/K) →* (PadicInt p)ˣ :=
    (cyclotomicCharacter Ω p).comp (MulSemiringAction.toRingAut Gal(Ω/K) Ω)
  intro hfin
  have : Finite (Set.range χ) := hfin.to_subtype
  have hcont : Continuous (fun σ : Gal(Ω/K) => (⟨χ σ, σ, rfl⟩ : Set.range χ)) :=
    (cyclotomicCharacter.continuous p K Ω).subtype_mk _
  let oneχ : Set.range χ := ⟨1, 1, map_one χ⟩
  have hopen : IsOpen (χ.ker : Set Gal(Ω/K)) := by
    have ho := (isOpen_discrete ({oneχ} : Set (Set.range χ))).preimage hcont
    convert ho using 1
    ext σ
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  let E : IntermediateField K Ω := IntermediateField.fixedField χ.ker
  have hfix : E.fixingSubgroup = χ.ker :=
    InfiniteGalois.fixingSubgroup_fixedField
      ⟨χ.ker, (show IsClosed (χ.ker : Set Gal(Ω/K)) from
        isClosed_eq (cyclotomicCharacter.continuous p K Ω) continuous_const)⟩
  have hE : FiniteDimensional K E := (InfiniteGalois.isOpen_iff_finite E).mp (by
    rw [hfix]
    exact hopen)
  have : Finite (CommGroup.primaryComponent Eˣ p) := hRoots E hE
  let f : CommGroup.primaryComponent Ωˣ p → CommGroup.primaryComponent Eˣ p := fun z =>
    ⟨Units.mk0 ⟨(z.val : Ω), primaryUnit_mem_fixedField_cyclotomic_ker p z⟩
      (fun h => Units.ne_zero z.val (congrArg Subtype.val h)), by
      obtain ⟨n, hn⟩ := z.property
      refine ⟨n, ?_⟩
      apply Units.ext
      apply Subtype.ext
      exact congrArg Units.val hn⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun z : CommGroup.primaryComponent Eˣ p => ((z.val : E) : Ω)) h
  have : Finite (CommGroup.primaryComponent Ωˣ p) := Finite.of_injective f hf
  have : Infinite (CommGroup.primaryComponent Ωˣ p) :=
    infinite_primaryComponent_of_primitive_roots p
  exact not_finite (CommGroup.primaryComponent Ωˣ p)

end KummerTheory
