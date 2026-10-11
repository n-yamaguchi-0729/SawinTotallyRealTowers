/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.ZMod

/-! # Finite cyclic characters inside the additive circle -/

namespace ZMod

/-- Every circle element annihilated by `N` comes from `ZMod N`. -/
theorem exists_toAddCircle_eq_of_nsmul_eq_zero
    (N : ℕ) [NeZero N] (z : UnitAddCircle) (hz : N • z = 0) :
    ∃ a : ZMod N, toAddCircle a = z := by
  obtain ⟨k, _, hk⟩ := (AddCircle.nsmul_eq_zero_iff (NeZero.pos N)).mp hz
  refine ⟨k, ?_⟩
  rw [toAddCircle_natCast]
  simpa only [mul_one] using hk

/-- Reduction between finite cyclic groups becomes multiplication on the circle. -/
theorem toAddCircle_castHom_mul
    (N m : ℕ) [NeZero N] [NeZero m] (a : ZMod (N * m)) :
    toAddCircle (castHom (dvd_mul_right N m) (ZMod N) a) =
      m • toAddCircle a := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  rw [map_intCast, toAddCircle_intCast, toAddCircle_intCast, ← AddCircle.coe_nsmul]
  congr 1
  rw [nsmul_eq_mul, Nat.cast_mul]
  field_simp [show (N : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne N),
    show (m : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne m)]

/-- A continuous circle-valued character of exponent `N` takes values in the
embedded finite cyclic group. -/
theorem exists_continuous_zmod_character
    {A : Type*} [Group A] [TopologicalSpace A]
    (N : ℕ) [NeZero N] (f : A →ₜ* Multiplicative UnitAddCircle)
    (hf : ∀ a : A, N • (f a).toAdd = 0) :
    ∃ g : A →ₜ* Multiplicative (ZMod N), ∀ a : A,
      toAddCircle (g a).toAdd = (f a).toAdd := by
  choose g hg using fun a => exists_toAddCircle_eq_of_nsmul_eq_zero N (f a).toAdd (hf a)
  have hinj := toAddCircle_injective N
  let ghom : A →* Multiplicative (ZMod N) :=
    { toFun := fun a => Multiplicative.ofAdd (g a)
      map_one' := by
        change g 1 = 0
        apply hinj
        rw [hg, map_zero]
        exact congrArg Multiplicative.toAdd (map_one f)
      map_mul' := by
        intro a b
        change g (a * b) = g a + g b
        apply hinj
        rw [map_add, hg, hg, hg]
        exact congrArg Multiplicative.toAdd (map_mul f a b) }
  have hemb : Topology.IsEmbedding (toAddCircle : ZMod N → UnitAddCircle) :=
    (show Continuous (toAddCircle : ZMod N → UnitAddCircle) from
      continuous_of_discreteTopology).isClosedEmbedding hinj |>.isEmbedding
  have hcont : Continuous g := hemb.continuous_iff.mpr (by
    change Continuous (fun a => toAddCircle (g a))
    simpa only [hg] using (show Continuous (fun a : A => (f a).toAdd) from f.continuous))
  exact ⟨⟨ghom, hcont⟩, hg⟩

end ZMod
