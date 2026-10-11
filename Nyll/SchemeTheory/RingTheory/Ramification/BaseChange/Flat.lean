/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Ramification indices in a flat base-change square

If both vertical maps in a commutative square are faithfully flat and the
chosen primes are exactly the extensions of the original primes, then the
ramification index is unchanged across the square.  The proof compares the
two ramification-index tower formulas; the two vertical indices are one
because their defining ideals map onto the chosen primes.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uS uR' uS'

/-- A prime which is exactly the extension of the prime below it has
ramification index one.  This elementary form does not require the algebra
map to be essentially of finite type. -/
theorem ramificationIdx_eq_one_of_map_eq
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hmap : p.map (algebraMap R S) = q) :
    q.ramificationIdx R = 1 := by
  let Sq := Localization.AtPrime q
  have hmap_local :
      p.map (algebraMap R Sq) = IsLocalRing.maximalIdeal Sq := by
    calc
      p.map (algebraMap R Sq) =
          (p.map (algebraMap R S)).map (algebraMap S Sq) := by
        rw [Ideal.map_map, IsScalarTower.algebraMap_eq R S Sq]
      _ = q.map (algebraMap S Sq) := by rw [hmap]
      _ = IsLocalRing.maximalIdeal Sq :=
        Localization.AtPrime.map_eq_maximalIdeal
  rw [Ideal.ramificationIdx_eq p q, hmap_local,
    ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff]

/-- Ramification indices are unchanged in a flat commutative square when
the selected vertical primes are their scheme-theoretic extensions.

Faithful flatness supplies the two vertical `LiesOver` instances.  The only
remaining prime comparison is the horizontal one in the upper row. -/
theorem ramificationIdx_eq_of_flat_baseChange_mapped_primes
    {R : Type uR} {S : Type uS} {R' : Type uR'} {S' : Type uS'}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S']
    [Module.FaithfullyFlat R R'] [Module.FaithfullyFlat S S']
    [Module.Flat R' S']
    (p : Ideal R) (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (p' : Ideal R') (q' : Ideal S') [q'.IsPrime] [q'.LiesOver p']
    (hpmap : p.map (algebraMap R R') = p')
    (hqmap : q.map (algebraMap S S') = q') :
    q'.ramificationIdx R' = q.ramificationIdx R := by
  have hp_over : p'.LiesOver p := by
    rw [← hpmap]
    exact
      { over :=
          (Ideal.comap_map_eq_self_of_faithfullyFlat
            (B := R') p).symm }
  have hq_over : q'.LiesOver q := by
    rw [← hqmap]
    exact
      { over :=
          (Ideal.comap_map_eq_self_of_faithfullyFlat
            (B := S') q).symm }
  let : p'.LiesOver p := hp_over
  let : q'.LiesOver q := hq_over
  let : p'.IsPrime := Ideal.isPrime_of_liesOver q' p'
  have hp_one : p'.ramificationIdx R = 1 :=
    ramificationIdx_eq_one_of_map_eq p p' hpmap
  have hq_one : q'.ramificationIdx S = 1 :=
    ramificationIdx_eq_one_of_map_eq q q' hqmap
  have hleft := Ideal.ramificationIdx_tower (R := R) q q'
  have hright := Ideal.ramificationIdx_tower (R := R) p' q'
  rw [hq_one, mul_one] at hleft
  rw [hp_one, one_mul] at hright
  exact hright.symm.trans hleft

end EtaleFundamentalGroups

end
