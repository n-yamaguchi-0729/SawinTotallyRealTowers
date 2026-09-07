import Mathlib.Data.ZMod.Basic
import ProCGroups.CompletedGroupAlgebra.ProfiniteModules.FiniteGroupAlgebra.Topology

set_option autoImplicit false

/-!
# Functoriality of finite group algebras

This file studies group-algebra maps induced by homomorphisms of finite groups, including
composition, basis formulas, continuity, and surjectivity. It also develops coefficient
calculations for cyclic reductions used in later kernel arguments.
-/

open scoped Topology
open ProCGroups

namespace CompletedGroupAlgebra

universe u v

/-- Finite-stage group algebras are functorial by continuous ring homomorphisms. -/
theorem finiteGroupAlgebra_mapDomainRingHom_continuous
    (R : Type u) (G H : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [Group H] [Finite G] [Finite H] (φ : G →* H) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    letI : TopologicalSpace (MonoidAlgebra R H) := finiteGroupAlgebraTopology R H
    Continuous (MonoidAlgebra.mapDomainRingHom R φ : MonoidAlgebra R G → MonoidAlgebra R H) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype H := Fintype.ofFinite H
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let : TopologicalSpace (MonoidAlgebra R H) := finiteGroupAlgebraTopology R H
  let e : MonoidAlgebra R H ≃ (H → R) :=
    (MonoidAlgebra.coeffEquiv (R := R) (M := H)).trans Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : MonoidAlgebra R H → H → R) :=
    Topology.IsInducing.induced e
  have hcoord : ∀ g : G, Continuous fun x : MonoidAlgebra R G => x.coeff g :=
    finiteGroupAlgebra_coordinate_continuous R G
  rw [he.continuous_iff]
  apply continuous_pi
  intro h
  change Continuous fun x : MonoidAlgebra R G =>
    (MonoidAlgebra.mapDomainRingHom R φ x : MonoidAlgebra R H).coeff h
  rw [show (fun x : MonoidAlgebra R G =>
        (MonoidAlgebra.mapDomainRingHom R φ x : MonoidAlgebra R H).coeff h) =
      (fun x : MonoidAlgebra R G =>
        ∑ g ∈ Finset.univ.filter (fun g : G => φ g = h), x.coeff g) from ?_]
  · apply continuous_finsetSum
    intro g _hg
    exact hcoord g
  · funext x
    change (Finsupp.mapDomain φ x.coeff) h =
      ∑ g ∈ Finset.univ.filter (fun g : G => φ g = h), x.coeff g
    rw [Finsupp.mapDomain, Finsupp.sum]
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    change (∑ g ∈ x.coeff.support, if φ g = h then x.coeff g else 0) =
      ∑ g ∈ Finset.univ.filter (fun g : G => φ g = h), x.coeff g
    rw [Finset.sum_filter]
    exact Finset.sum_subset (by intro g _hg; simp only [Finset.mem_univ]) (by
      intro g _hguniv hgnot
      by_cases hφ : φ g = h
      · simp only [hφ, ↓reduceIte, Finsupp.notMem_support_iff.mp hgnot]
      · simp only [hφ, ↓reduceIte])

/-- The finite-stage group algebra functor sends the identity homomorphism to the identity. -/
theorem finiteGroupAlgebra_mapDomainRingHom_id
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    MonoidAlgebra.mapDomainRingHom R (MonoidHom.id G) = RingHom.id (MonoidAlgebra R G) := by
  exact MonoidAlgebra.mapDomainRingHom_id

/-- The finite-stage group algebra functor respects composition. -/
theorem finiteGroupAlgebra_mapDomainRingHom_comp
    (R : Type u) (G H K : Type v) [CommRing R] [Group G] [Group H] [Group K]
    (φ : G →* H) (ψ : H →* K) :
    (MonoidAlgebra.mapDomainRingHom R ψ).comp (MonoidAlgebra.mapDomainRingHom R φ) =
      MonoidAlgebra.mapDomainRingHom R (ψ.comp φ) := by
  exact (MonoidAlgebra.mapDomainRingHom_comp (R := R) ψ φ).symm

/-- Functoriality on the canonical group-like basis elements of a finite-stage group algebra. -/
theorem finiteGroupAlgebra_mapDomainRingHom_of
    (R : Type u) (G H : Type v) [CommRing R] [Group G] [Group H]
    (φ : G →* H) (g : G) :
    MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.of R G g) =
      MonoidAlgebra.of R H (φ g) := by
  change MonoidAlgebra.mapDomain φ (MonoidAlgebra.single g 1) =
    MonoidAlgebra.single (φ g) 1
  exact MonoidAlgebra.mapDomain_single

/--
A finite group-algebra relation is preserved by pushing the group variable along a homomorphism.
-/
theorem finiteGroupAlgebra_mapDomain_sub_one_mul_eq_zero
    {R G H : Type*} [Ring R] [Group G] [Group H]
    (f : G →* H) (g : G) (y : MonoidAlgebra R G)
    (hrel : (MonoidAlgebra.of R G g - 1) * y = 0) :
    (MonoidAlgebra.of R H (f g) - 1) *
        MonoidAlgebra.mapDomainRingHom R f y = 0 := by
  have hmap := congrArg (MonoidAlgebra.mapDomainRingHom R f) hrel
  calc
    (MonoidAlgebra.of R H (f g) - 1) *
        MonoidAlgebra.mapDomainRingHom R f y
        = MonoidAlgebra.mapDomainRingHom R f
            ((MonoidAlgebra.of R G g - 1) * y) := by
          rw [map_mul, map_sub, map_one]
          rw [show MonoidAlgebra.mapDomainRingHom R f (MonoidAlgebra.of R G g) =
            MonoidAlgebra.of R H (f g) by
              change MonoidAlgebra.mapDomain f (MonoidAlgebra.single g 1) =
                MonoidAlgebra.single (f g) 1
              exact MonoidAlgebra.mapDomain_single]
    _ = 0 := by simpa only [map_zero] using hmap

/-- Integer-power version of finite group-algebra relation functoriality. -/
theorem finiteGroupAlgebra_mapDomain_zpow_sub_one_mul_eq_zero
    {R G H : Type*} [Ring R] [Group G] [Group H]
    (f : G →* H) (g : G) (n : ℤ) (y : MonoidAlgebra R G)
    (hrel : (MonoidAlgebra.of R G (g ^ n) - 1) * y = 0) :
    (MonoidAlgebra.of R H ((f g) ^ n) - 1) *
    MonoidAlgebra.mapDomainRingHom R f y = 0 := by
  simpa only [map_zpow] using
    finiteGroupAlgebra_mapDomain_sub_one_mul_eq_zero f (g ^ n) y hrel

/--
A finite group-algebra relation \((a - 1)y = 0\) makes coefficients constant along the left
\(a\)-orbits.
-/
theorem finiteGroupAlgebra_coeff_eq_zpow_mul_of_sub_one_mul_eq_zero
    {R G : Type*} [Ring R] [Group G] (a : G) (y : MonoidAlgebra R G)
    (hrel : (MonoidAlgebra.of R G a - 1) * y = 0) :
    ∀ k : ℤ, ∀ t : G, y.coeff (a ^ k * t) = y.coeff t := by
  have hmul : MonoidAlgebra.of R G a * y = y := by
    have h : MonoidAlgebra.of R G a * y - y = 0 := by
      simpa [sub_mul] using hrel
    exact sub_eq_zero.mp h
  have hpowmul : ∀ m : ℕ, MonoidAlgebra.of R G (a ^ m) * y = y := by
    intro m
    induction m with
    | zero =>
        rw [pow_zero]
        change MonoidAlgebra.single (1 : G) (1 : R) * y = y
        rw [← MonoidAlgebra.one_def]
        simp only [one_mul]
    | succ m ih =>
        calc
          MonoidAlgebra.of R G (a ^ (m + 1)) * y
              = MonoidAlgebra.of R G (a ^ m) * (MonoidAlgebra.of R G a * y) := by
                  rw [← mul_assoc, ← map_mul]
                  simp only [pow_succ, MonoidAlgebra.of_apply]
          _ = MonoidAlgebra.of R G (a ^ m) * y := by rw [hmul]
          _ = y := ih
  have hneg : ∀ m : ℕ, ∀ t : G, y.coeff ((a ^ m)⁻¹ * t) = y.coeff t := by
    intro m t
    have hcoeff :=
      congrArg (fun z : MonoidAlgebra R G => z.coeff t) (hpowmul m)
    have hleft :
        (MonoidAlgebra.of R G (a ^ m) * y).coeff t =
          y.coeff ((a ^ m)⁻¹ * t) := by
      change (MonoidAlgebra.single (a ^ m) (1 : R) * y).coeff t =
        y.coeff ((a ^ m)⁻¹ * t)
      rw [MonoidAlgebra.coeff_single_mul_apply]
      simp only [one_mul]
    simpa [hleft] using hcoeff
  have hpos : ∀ m : ℕ, ∀ t : G, y.coeff (a ^ m * t) = y.coeff t := by
    intro m t
    have h := hneg m (a ^ m * t)
    have hsimp : (a ^ m)⁻¹ * (a ^ m * t) = t := by simp only [inv_mul_cancel_left]
    exact (by simpa [hsimp] using h.symm)
  intro k
  cases k with
  | ofNat m =>
      intro t
      simpa using hpos m t
  | negSucc m =>
      intro t
      simpa [zpow_negSucc] using hneg (m + 1) t

/--
A finite group-algebra relation \((a - 1)y = 0\) also gives \((a^k - 1)y = 0\) for every integer
power \(k\).
-/
theorem finiteGroupAlgebra_zpow_sub_one_mul_eq_zero_of_sub_one_mul_eq_zero
    {R G : Type*} [Ring R] [Group G] (a : G) (k : ℤ) (y : MonoidAlgebra R G)
    (hrel : (MonoidAlgebra.of R G a - 1) * y = 0) :
    (MonoidAlgebra.of R G (a ^ k) - 1) * y = 0 := by
  ext t
  have horbit :=
    finiteGroupAlgebra_coeff_eq_zpow_mul_of_sub_one_mul_eq_zero
      (R := R) (G := G) a y hrel (-k) t
  have hleft :
      (MonoidAlgebra.of R G (a ^ k) * y).coeff t =
        y.coeff ((a ^ k)⁻¹ * t) := by
    change (MonoidAlgebra.single (a ^ k) (1 : R) * y).coeff t =
      y.coeff ((a ^ k)⁻¹ * t)
    rw [MonoidAlgebra.coeff_single_mul_apply]
    simp only [one_mul]
  have harg : a ^ (-k) * t = (a ^ k)⁻¹ * t := by simp only [zpow_neg]
  rw [sub_mul, one_mul]
  change (MonoidAlgebra.of R G (a ^ k) * y).coeff t - y.coeff t = 0
  rw [hleft]
  simpa [harg] using sub_eq_zero.mpr horbit

/--
The standard finite cyclic reduction from \(\mathbb{Z}/(K M)\mathbb{Z}\) to
\(\mathbb{Z}/M\mathbb{Z}\).
-/
def finiteCyclicReduction (M K : ℕ) :
    Multiplicative (ZMod (K * M)) →* Multiplicative (ZMod M) :=
  (ZMod.castHom (Nat.dvd_mul_left M K) (ZMod M)).toAddMonoidHom.toMultiplicative

/--
The finite product cyclic reduction keeps an auxiliary finite quotient coordinate while reducing
only the cyclic coordinate.
-/
def finiteProductCyclicReduction (Q : Type*) [Group Q] (M K : ℕ) :
    Q × Multiplicative (ZMod (K * M)) →*
      Q × Multiplicative (ZMod M) where
  toFun x := (x.1, finiteCyclicReduction M K x.2)
  map_one' := by
    ext <;> simp [finiteCyclicReduction]
  map_mul' x y := by
    ext <;> simp [finiteCyclicReduction]

/--
An integer cast to \(\mathbb{Z}/n\mathbb{Z}\) is represented by either its absolute value or the
negative of its absolute value, depending on its sign.
-/
theorem int_cast_eq_natAbs_or_neg_natAbs_zmod_of_modulus (L : ℕ) (n : ℤ) :
    (n : ZMod L) = (n.natAbs : ZMod L) ∨
      (n : ZMod L) = -(n.natAbs : ZMod L) := by
  rcases Int.natAbs_eq n with hn | hn
  · left
    rw [hn]
    norm_num
  · right
    rw [hn]
    norm_num

/--
A natural number cast into \(\mathbb{Z}/n\mathbb{Z}\) lies in the subgroup generated by an
integer cast whenever the required gcd divisibility condition holds.
-/
theorem zmod_natCast_mem_zmultiples_intCast_of_gcd_dvd
    {L M : ℕ} (n : ℤ) (hdiv : Nat.gcd n.natAbs L ∣ M) :
    ∃ q : ℤ, (M : ZMod L) = q • (n : ZMod L) := by
  rcases hdiv with ⟨c, hc⟩
  let d : ℕ := Nat.gcd n.natAbs L
  have hbez :
      ((d : ℤ) : ZMod L) =
        ((n.natAbs : ℤ) * (Nat.gcdA n.natAbs L : ℤ) +
          (L : ℤ) * (Nat.gcdB n.natAbs L : ℤ) : ℤ) := by
    exact congrArg (fun z : ℤ => (z : ZMod L)) (Nat.gcd_eq_gcd_ab n.natAbs L)
  have hd_natAbs :
      (d : ZMod L) =
        (Nat.gcdA n.natAbs L : ℤ) • (n.natAbs : ZMod L) := by
    calc
      (d : ZMod L)
          = ((d : ℤ) : ZMod L) := by norm_num
      _ = ((n.natAbs : ℤ) * (Nat.gcdA n.natAbs L : ℤ) +
              (L : ℤ) * (Nat.gcdB n.natAbs L : ℤ) : ℤ) := hbez
      _ = (Nat.gcdA n.natAbs L : ℤ) • (n.natAbs : ZMod L) := by
              simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, mul_comm, Int.cast_add,
                Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, mul_zero, add_zero,
                zsmul_eq_mul]
  rcases int_cast_eq_natAbs_or_neg_natAbs_zmod_of_modulus L n with hn | hn
  · refine ⟨(c : ℤ) * Nat.gcdA n.natAbs L, ?_⟩
    rw [hc]
    calc
      ((d * c : ℕ) : ZMod L)
          = (c : ℕ) • (d : ZMod L) := by
              rw [nsmul_eq_mul]
              norm_num [mul_comm]
      _ = (c : ℕ) • ((Nat.gcdA n.natAbs L : ℤ) • (n.natAbs : ZMod L)) := by
              rw [hd_natAbs]
      _ = ((c : ℤ) * Nat.gcdA n.natAbs L) • (n.natAbs : ZMod L) := by
              simp only [Nat.cast_natAbs, zsmul_eq_mul, nsmul_eq_mul, Int.cast_mul,
                Int.cast_natCast, mul_assoc]
      _ = ((c : ℤ) * Nat.gcdA n.natAbs L) • (n : ZMod L) := by
              rw [hn]
  · refine ⟨-((c : ℤ) * Nat.gcdA n.natAbs L), ?_⟩
    rw [hc]
    calc
      ((d * c : ℕ) : ZMod L)
          = (c : ℕ) • (d : ZMod L) := by
              rw [nsmul_eq_mul]
              norm_num [mul_comm]
      _ = (c : ℕ) • ((Nat.gcdA n.natAbs L : ℤ) • (n.natAbs : ZMod L)) := by
              rw [hd_natAbs]
      _ = ((c : ℤ) * Nat.gcdA n.natAbs L) • (n.natAbs : ZMod L) := by
              simp only [Nat.cast_natAbs, zsmul_eq_mul, nsmul_eq_mul, Int.cast_mul,
                Int.cast_natCast, mul_assoc]
      _ = -(((c : ℤ) * Nat.gcdA n.natAbs L) • (n : ZMod L)) := by
              rw [hn]
              simp only [Nat.cast_natAbs, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, smul_neg,
                neg_neg]
      _ = (-((c : ℤ) * Nat.gcdA n.natAbs L)) • (n : ZMod L) := by
              rw [neg_zsmul]

/--
The kernel direction of the map from \(\mathbb{Z}/(K M)\mathbb{Z}\) to
\(\mathbb{Z}/M\mathbb{Z}\) is described by integer multiples of \(M\).
-/
theorem exists_zsmul_natCast_of_zmod_castHom_eq
    {M K : ℕ} [NeZero (K * M)] {a b : ZMod (K * M)}
    (h :
      (ZMod.castHom (Nat.dvd_mul_left M K) (ZMod M)) a =
        (ZMod.castHom (Nat.dvd_mul_left M K) (ZMod M)) b) :
    ∃ q : ℤ, a = b + q • (M : ZMod (K * M)) := by
  have hval : (a.val : ZMod M) = (b.val : ZMod M) := by
    rw [ZMod.castHom_apply, ZMod.castHom_apply] at h
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val] at h
    exact h
  have hmodNat : a.val ≡ b.val [MOD M] :=
    (ZMod.natCast_eq_natCast_iff a.val b.val M).mp hval
  rcases (Nat.modEq_iff_dvd.mp hmodNat) with ⟨q, hq⟩
  use -q
  rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b]
  have hcast :
      (((b.val : ℤ) - (a.val : ℤ) : ℤ) : ZMod (K * M)) =
        (((M : ℤ) * q : ℤ) : ZMod (K * M)) :=
    congrArg (fun z : ℤ => (z : ZMod (K * M))) hq
  have hdiff :
      (b.val : ZMod (K * M)) - (a.val : ZMod (K * M)) =
        (M : ZMod (K * M)) * (q : ZMod (K * M)) := by
    simpa [Int.cast_sub, Int.cast_natCast, Int.cast_mul] using hcast
  calc
    (a.val : ZMod (K * M))
        = (b.val : ZMod (K * M)) -
            (M : ZMod (K * M)) * (q : ZMod (K * M)) := by
            rw [← hdiff]
            abel
    _ = (b.val : ZMod (K * M)) + (-q : ℤ) • (M : ZMod (K * M)) := by
            rw [zsmul_eq_mul]
            norm_num
            ring

/-- Every fiber of \(\mathbb{Z}/(K M)\mathbb{Z} \to \mathbb{Z}/M\mathbb{Z}\) has \(K\) elements. -/
theorem finiteCyclicReduction_fiber_card
    {M K : ℕ} [NeZero (K * M)] (i : Multiplicative (ZMod M)) :
    Fintype.card {t : Multiplicative (ZMod (K * M)) //
      finiteCyclicReduction M K t = i} = K := by
  classical
  have hMne : M ≠ 0 := by
    intro hM
    exact NeZero.ne (K * M) (by simp only [hM, mul_zero])
  let : NeZero M := ⟨hMne⟩
  let f : Multiplicative (ZMod (K * M)) →* Multiplicative (ZMod M) :=
    finiteCyclicReduction M K
  have hsurj : Function.Surjective f := by
    intro y
    cases y with
    | ofAdd y =>
        rcases ZMod.castHom_surjective (Nat.dvd_mul_left M K) y with ⟨x, hx⟩
        exact
          ⟨Multiplicative.ofAdd x,
            by simpa [f, finiteCyclicReduction] using congrArg Multiplicative.ofAdd hx⟩
  have hcardFiberKer :
      Fintype.card {t : Multiplicative (ZMod (K * M)) // f t = i} =
        Fintype.card {t : Multiplicative (ZMod (K * M)) // f t = 1} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact MonoidHom.card_fiber_eq_of_mem_range f (hsurj i) (hsurj 1)
  have hkerSubtype :
      Fintype.card {t : Multiplicative (ZMod (K * M)) // f t = 1} =
        Nat.card f.ker := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr
      { toFun := fun t => ⟨t.1, MonoidHom.mem_ker.mpr t.2⟩
        invFun := fun t => ⟨t.1, MonoidHom.mem_ker.mp t.2⟩
        left_inv := by intro t; rfl
        right_inv := by intro t; rfl }
  have hdomain : Nat.card (Multiplicative (ZMod (K * M))) = K * M := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_congr Multiplicative.toAdd).trans (ZMod.card (K * M))
  have hrange : Nat.card f.range = M := by
    have htop : f.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
    rw [htop]
    have htopcard :
        Nat.card (↥(⊤ : Subgroup (Multiplicative (ZMod M)))) =
          Nat.card (Multiplicative (ZMod M)) :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [htopcard]
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_congr Multiplicative.toAdd).trans (ZMod.card M)
  have hkerMul : Nat.card f.ker * M = K * M := by
    have h := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hdomain, hrange] at h
    exact h
  have hker : Nat.card f.ker = K :=
    Nat.mul_right_cancel (Nat.pos_of_ne_zero hMne) hkerMul
  rw [hcardFiberKer, hkerSubtype, hker]

/--
The product-with-other-coordinates fiber over \((q,i)\) has the same size as the cyclic fiber,
namely \(K\).
-/
theorem finiteProductCyclicReduction_fiber_card
    {Q : Type*} [Group Q] [Fintype Q] [DecidableEq Q]
    {M K : ℕ} [NeZero (K * M)] (i : Q × Multiplicative (ZMod M)) :
    Fintype.card {t : Q × Multiplicative (ZMod (K * M)) //
      finiteProductCyclicReduction Q M K t = i} = K := by
  classical
  let e :
      {t : Q × Multiplicative (ZMod (K * M)) //
        finiteProductCyclicReduction Q M K t = i} ≃
        {z : Multiplicative (ZMod (K * M)) //
          finiteCyclicReduction M K z = i.2} :=
  {
    toFun t := ⟨t.1.2, by
      simpa [finiteProductCyclicReduction] using congrArg Prod.snd t.2⟩
    invFun z := ⟨(i.1, z.1), by
      ext <;> first | rfl | assumption | exact finiteProductCyclicReduction |
        exact finiteProductCyclicReduction.symm |
        simp only [finiteProductCyclicReduction, MonoidHom.coe_mk, OneHom.coe_mk, z.2,
          Prod.mk.eta]⟩
    left_inv t := by
      apply Subtype.ext
      have hfst := congrArg Prod.fst t.2
      ext <;> first | rfl | assumption | exact finiteProductCyclicReduction |
        exact finiteProductCyclicReduction.symm |
        simp only [finiteProductCyclicReduction, MonoidHom.coe_mk, OneHom.coe_mk] at hfst ⊢
      exact hfst.symm
    right_inv z := by
      apply Subtype.ext
      rfl }
  calc
    Fintype.card {t : Q × Multiplicative (ZMod (K * M)) //
        finiteProductCyclicReduction Q M K t = i}
        = Fintype.card {z : Multiplicative (ZMod (K * M)) //
          finiteCyclicReduction M K z = i.2} := Fintype.card_congr e
    _ = K := finiteCyclicReduction_fiber_card (M := M) (K := K) (i := i.2)

/-- Product-coordinate version of the GCD-conditioned fiber constancy. -/
theorem finiteProductCyclicGroupAlgebra_coeff_eq_of_same_reduction_of_int_sub_one_mul_eq_zero
    {R Q : Type*} [Ring R] [Group Q] {M K : ℕ} [NeZero (K * M)] (n : ℤ)
    (hgcd : Nat.gcd n.natAbs (K * M) ∣ M)
    (y : MonoidAlgebra R (Q × Multiplicative (ZMod (K * M))))
    (hrel :
      (MonoidAlgebra.of R (Q × Multiplicative (ZMod (K * M)))
          (1, Multiplicative.ofAdd (n : ZMod (K * M))) - 1) * y = 0)
    {s t : Q × Multiplicative (ZMod (K * M))}
    (hst : finiteProductCyclicReduction Q M K s = finiteProductCyclicReduction Q M K t) :
    y.coeff s = y.coeff t := by
  rcases s with ⟨qs, s⟩
  rcases t with ⟨qt, t⟩
  cases s with
  | ofAdd a =>
      cases t with
      | ofAdd b =>
          have hq : qs = qt := by
            simpa [finiteProductCyclicReduction] using congrArg Prod.fst hst
          subst qs
          have hcyc :
              finiteCyclicReduction M K (Multiplicative.ofAdd a) =
                finiteCyclicReduction M K (Multiplicative.ofAdd b) := by
            simpa [finiteProductCyclicReduction] using congrArg Prod.snd hst
          rcases
              exists_zsmul_natCast_of_zmod_castHom_eq
                (M := M) (K := K) (a := a) (b := b)
                (Multiplicative.ofAdd.injective hcyc) with
            ⟨q, hqM0⟩
          rcases
              zmod_natCast_mem_zmultiples_intCast_of_gcd_dvd
                (L := K * M) (M := M) n hgcd with
            ⟨c, hc⟩
          have hqM :
              q • (M : ZMod (K * M)) =
                (q * c) • (n : ZMod (K * M)) := by
            rw [hc, smul_smul]
          have harg : a = b + (q * c) • (n : ZMod (K * M)) := by
            rw [← hqM]
            exact hqM0
          let g : Q × Multiplicative (ZMod (K * M)) :=
            (1, Multiplicative.ofAdd (n : ZMod (K * M)))
          let t0 : Q × Multiplicative (ZMod (K * M)) :=
            (qt, Multiplicative.ofAdd b)
          have horbit :=
            finiteGroupAlgebra_coeff_eq_zpow_mul_of_sub_one_mul_eq_zero
              (R := R) (G := Q × Multiplicative (ZMod (K * M))) g y hrel
              (q * c) t0
          have hgt : g ^ (q * c) * t0 = (qt, Multiplicative.ofAdd a) := by
            ext
            · simp only [Prod.pow_mk, one_zpow, Prod.mk_mul_mk, one_mul, g, t0]
            · change
                Multiplicative.ofAdd
                    ((q * c) • (n : ZMod (K * M)) + b) =
                  Multiplicative.ofAdd a
              rw [harg]
              abel_nf
          simpa [t0] using hgt ▸ horbit

/--
In a finite-stage group algebra projection, coefficients that are constant on a fiber aggregate
to the fiber cardinality times the common coefficient.
-/
theorem mapDomain_coeff_eq_nsmul_of_fiber_const
    {R G H : Type*} [Semiring R] [Monoid G] [Monoid H] [Fintype G] [DecidableEq H]
    (f : G →* H) (y : MonoidAlgebra R G) (h : H) (c : R)
    (hconst : ∀ g : G, f g = h → y.coeff g = c) :
    (MonoidAlgebra.mapDomainRingHom R f y).coeff h =
      Fintype.card {g : G // f g = h} • c := by
  classical
  have hy : y = ∑ g : G, MonoidAlgebra.single g (y.coeff g) := by
    have hsum : y.coeff.sum MonoidAlgebra.single = y :=
      MonoidAlgebra.sum_coeff_single y
    have hfin :
        y.coeff.sum MonoidAlgebra.single =
          ∑ g : G, MonoidAlgebra.single g (y.coeff g) :=
      Finsupp.sum_fintype y.coeff (fun g r => MonoidAlgebra.single g r)
        (by intro g; simp only [MonoidAlgebra.single_zero])
    exact hsum.symm.trans hfin
  rw [hy, map_sum]
  simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  rw [show (∑ g : G, MonoidAlgebra.single (f g) (y.coeff g)).coeff h =
      ∑ g : G, (MonoidAlgebra.single (f g) (y.coeff g) :
        MonoidAlgebra R H).coeff h by
    simpa only [Finsupp.finsetSum_apply] using
      congrArg (fun z : H →₀ R => z h)
        (MonoidAlgebra.coeff_sum (R := R) (M := H) Finset.univ
          (fun g : G => MonoidAlgebra.single (f g) (y.coeff g)))]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  let s : Finset G := Finset.univ.filter fun x : G => f x = h
  calc
    (∑ x : G, if f x = h then y.coeff x else 0)
        = ∑ x ∈ s, y.coeff x := by
            simp only [Finset.sum_filter, s]
    _ = ∑ x ∈ s, c := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hconst x (by simpa [s] using (Finset.mem_filter.mp hx).2)
    _ = ∑ x : {g : G // f g = h}, c := by
            rw [← Finset.sum_subtype
              (s := s)
              (h := by intro x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, s])
              (f := fun _ => c)]
    _ = Fintype.card {g : G // f g = h} • c := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Product-coordinate coefficient aggregation with the GCD-conditioned cyclic depth. -/
theorem
  finiteProductCyclicGroupAlgebra_projection_coeff_eq_K_nsmul_of_int_sub_one_mul_eq_zero_of_gcd
    {R Q : Type*} [Ring R] [Group Q] [Finite Q]
    {M K : ℕ} [NeZero (K * M)] (n : ℤ)
    (hgcd : Nat.gcd n.natAbs (K * M) ∣ M)
    (y : MonoidAlgebra R (Q × Multiplicative (ZMod (K * M))))
    (i : Q × Multiplicative (ZMod M)) (t0 : Q × Multiplicative (ZMod (K * M)))
    (ht0 : finiteProductCyclicReduction Q M K t0 = i)
    (hrel :
      (MonoidAlgebra.of R (Q × Multiplicative (ZMod (K * M)))
          (1, Multiplicative.ofAdd (n : ZMod (K * M))) - 1) * y = 0) :
    (MonoidAlgebra.mapDomainRingHom R
      (finiteProductCyclicReduction Q M K) y).coeff i =
      K • y.coeff t0 := by
  classical
  let : Fintype Q := Fintype.ofFinite Q
  rw [mapDomain_coeff_eq_nsmul_of_fiber_const
    (finiteProductCyclicReduction Q M K) y i (y.coeff t0)]
  · rw [finiteProductCyclicReduction_fiber_card (Q := Q) (M := M) (K := K) (i := i)]
  · intro t ht
    exact
      finiteProductCyclicGroupAlgebra_coeff_eq_of_same_reduction_of_int_sub_one_mul_eq_zero
        (R := R) (Q := Q) (M := M) (K := K) n hgcd y hrel (by rw [ht, ht0])

/--
With \(\mathbb{Z}/K\mathbb{Z}\) coefficients, the product-coordinate projection vanishes under
the stated gcd-conditioned multiple of \(g-1\).
-/
theorem finiteProductCyclicGroupAlgebra_projection_eq_zero_of_int_sub_one_mul_eq_zero_of_gcd
    {Q : Type*} [Group Q] [Finite Q]
    {M K : ℕ} [NeZero (K * M)] (n : ℤ)
    (hgcd : Nat.gcd n.natAbs (K * M) ∣ M)
    (y : MonoidAlgebra (ZMod K) (Q × Multiplicative (ZMod (K * M))))
    (hrel :
      (MonoidAlgebra.of (ZMod K) (Q × Multiplicative (ZMod (K * M)))
          (1, Multiplicative.ofAdd (n : ZMod (K * M))) - 1) * y = 0) :
    MonoidAlgebra.mapDomainRingHom (ZMod K) (finiteProductCyclicReduction Q M K) y = 0 := by
  classical
  let : Fintype Q := Fintype.ofFinite Q
  have hMne : M ≠ 0 := by
    intro hM
    exact NeZero.ne (K * M) (by simp only [hM, mul_zero])
  let : NeZero M := ⟨hMne⟩
  let projectionCoeff :=
    finiteProductCyclicGroupAlgebra_projection_coeff_eq_K_nsmul_of_int_sub_one_mul_eq_zero_of_gcd
      (R := ZMod K) (Q := Q) (M := M) (K := K)
  ext x
  rcases x with ⟨q, i⟩
  cases i with
  | ofAdd i =>
      rcases ZMod.castHom_surjective (Nat.dvd_mul_left M K) i with ⟨t0, ht0⟩
      have ht0' :
          finiteProductCyclicReduction Q M K (q, Multiplicative.ofAdd t0) =
            (q, Multiplicative.ofAdd i) := by
        ext
        · simp only [finiteProductCyclicReduction, MonoidHom.coe_mk, OneHom.coe_mk]
        · change Multiplicative.ofAdd
              ((ZMod.castHom (Nat.dvd_mul_left M K) (ZMod M)) t0) =
            Multiplicative.ofAdd i
          exact congrArg Multiplicative.ofAdd ht0
      have hcoeff :=
        projectionCoeff n hgcd y
          (q, Multiplicative.ofAdd i) (q, Multiplicative.ofAdd t0) ht0' hrel
      rw [hcoeff]
      rw [nsmul_eq_mul]
      simp only [CharP.cast_eq_zero, zero_mul, MonoidAlgebra.coeff_zero,
        Finsupp.zero_apply]

/--
Product-coordinate vanishing when the first coordinate is killed by taking a finite integer
power of the relation element.
-/
theorem finiteProductCyclicGroupAlgebra_projection_eq_zero_of_pair_relation_of_order
    {Q : Type*} [Group Q] [Finite Q]
    {M K : ℕ} [NeZero (K * M)] (a : Q) (n : ℤ) (d : ℕ)
    (had : a ^ d = 1)
    (hgcd : Nat.gcd (((d : ℤ) * n).natAbs) (K * M) ∣ M)
    (y : MonoidAlgebra (ZMod K) (Q × Multiplicative (ZMod (K * M))))
    (hrel :
      (MonoidAlgebra.of (ZMod K) (Q × Multiplicative (ZMod (K * M)))
          (a, Multiplicative.ofAdd (n : ZMod (K * M))) - 1) * y = 0) :
    MonoidAlgebra.mapDomainRingHom (ZMod K) (finiteProductCyclicReduction Q M K) y = 0 := by
  classical
  let : Fintype Q := Fintype.ofFinite Q
  let g : Q × Multiplicative (ZMod (K * M)) :=
    (a, Multiplicative.ofAdd (n : ZMod (K * M)))
  have hpowrel :
      (MonoidAlgebra.of (ZMod K) (Q × Multiplicative (ZMod (K * M)))
          (g ^ (d : ℤ)) - 1) * y = 0 :=
    finiteGroupAlgebra_zpow_sub_one_mul_eq_zero_of_sub_one_mul_eq_zero
      (R := ZMod K) (G := Q × Multiplicative (ZMod (K * M))) g (d : ℤ) y hrel
  have hgpow :
      g ^ (d : ℤ) =
        (1, Multiplicative.ofAdd (((d : ℤ) * n : ℤ) : ZMod (K * M))) := by
    ext
    · change a ^ (d : ℤ) = 1
      simpa [zpow_natCast] using had
    · change (Multiplicative.ofAdd (n : ZMod (K * M))) ^ (d : ℤ) =
        Multiplicative.ofAdd (((d : ℤ) * n : ℤ) : ZMod (K * M))
      change Multiplicative.ofAdd ((d : ℤ) • (n : ZMod (K * M))) =
        Multiplicative.ofAdd (((d : ℤ) * n : ℤ) : ZMod (K * M))
      simp only [zsmul_eq_mul, Int.cast_natCast, mul_comm, Int.cast_mul]
  have hrel' :
      (MonoidAlgebra.of (ZMod K) (Q × Multiplicative (ZMod (K * M)))
          (1, Multiplicative.ofAdd (((d : ℤ) * n : ℤ) : ZMod (K * M))) - 1) * y = 0 := by
    rw [hgpow] at hpowrel
    exact hpowrel
  exact
    finiteProductCyclicGroupAlgebra_projection_eq_zero_of_int_sub_one_mul_eq_zero_of_gcd
      (Q := Q) (M := M) (K := K) ((d : ℤ) * n) hgcd y hrel'

/--
A surjective group homomorphism lets each group-like basis element be lifted through the induced
group-algebra map.
-/
theorem finiteGroupAlgebra_mapDomainRingHom_of_preimage
    (R : Type u) (G H : Type v) [CommRing R] [Group G] [Group H]
    (φ : MonoidHom G H) (hφ : Function.Surjective φ) (h : H) :
    ∃ g : G, φ g = h ∧
      MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.of R G g) =
        MonoidAlgebra.of R H h := by
  rcases hφ h with ⟨g, hg⟩
  refine ⟨g, hg, ?_⟩
  rw [← hg]
  exact finiteGroupAlgebra_mapDomainRingHom_of R G H φ g

/--
A coefficient supported at a target group element has a coefficient-supported lift along a
surjective group homomorphism.
-/
theorem finiteGroupAlgebra_mapDomainRingHom_single_preimage
    (R : Type u) (G H : Type v) [CommRing R] [Group G] [Group H]
    (φ : MonoidHom G H) (hφ : Function.Surjective φ) (h : H) (r : R) :
    ∃ g : G, φ g = h ∧
      MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.single g r) =
        MonoidAlgebra.single h r := by
  rcases hφ h with ⟨g, hg⟩
  refine ⟨g, hg, ?_⟩
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, hg]

/-- A surjective group homomorphism induces a surjective map on group algebras. -/
theorem finiteGroupAlgebra_mapDomainRingHom_surjective
    (R : Type u) (G H : Type v) [CommRing R] [Group G] [Group H]
    (φ : MonoidHom G H) (hφ : Function.Surjective φ) :
    Function.Surjective (MonoidAlgebra.mapDomainRingHom R φ) := by
  classical
  intro x
  induction x using MonoidAlgebra.induction with
  | zero =>
      exact ⟨0, map_zero _⟩
  | single_add h r x _ _ ih =>
      rcases hφ h with ⟨g, hg⟩
      rcases ih with ⟨y, hy⟩
      refine ⟨MonoidAlgebra.single g r + y, ?_⟩
      rw [map_add, hy]
      rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, hg]

end CompletedGroupAlgebra
