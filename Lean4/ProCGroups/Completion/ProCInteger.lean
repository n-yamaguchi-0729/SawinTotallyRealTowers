import Mathlib.Topology.Instances.ZMod
import ProCGroups.ProC.InverseLimits.Limits
import ProCGroups.ProC.InverseLimits.Predicates

set_option autoImplicit false

/-!
# `ProCGroups.Completion.ProCInteger`

This module constructs the inverse limit of cyclic integer quotients indexed by the moduli
admitted by a finite group class, equips it with its topological ring structure, and proves its
profinite multiplicative and density properties.
-/

open scoped Topology

namespace ProCGroups.Completion

noncomputable section

universe u v

/-- A coefficient level: a positive modulus whose additive cyclic group belongs to \(C\),
independently of the universe used to represent that finite group. -/
structure ProCIntegerIndex (C : FiniteGroupClass.{u}) where
  /-- The positive integer defining the coefficient ring `ZMod modulus` at this level. -/
  modulus : ℕ
  /-- The modulus is nonzero, as required for the finite cyclic coefficient group. -/
  positive : 0 < modulus
  /--
  The multiplicative presentation of the additive cyclic group `ZMod modulus` belongs to `C`,
  using universe-independent membership.
  -/
  cyclic_mem : C.MemAcrossUniverses (Multiplicative (ZMod modulus))

namespace ProCIntegerIndex

/-- Internal bridge from native membership of a universe lift to the universe-independent
public membership predicate. -/
private theorem memAcrossUniverses_of_ulift_mem
    {C : FiniteGroupClass.{u}} {G : Type} [Group G]
    (hG : C (ULift.{u} G)) : C.MemAcrossUniverses G :=
  (C.memAcrossUniverses_ulift_iff G).1 (C.memAcrossUniverses_of_mem hG)

/-- Internal bridge used when a universe-specific formation theorem needs a native carrier. -/
private theorem ulift_mem_of_memAcrossUniverses
    {C : FiniteGroupClass.{u}} {G : Type} [Group G]
    (hG : C.MemAcrossUniverses G) : C (ULift.{u} G) :=
  C.mem_of_memAcrossUniverses ((C.memAcrossUniverses_ulift_iff G).2 hG)

/-- The order relation is the refinement relation on the corresponding data. -/
instance instLEProCIntegerIndex (C : FiniteGroupClass.{u}) : LE (ProCIntegerIndex C) where
  le i j := i.modulus ∣ j.modulus

/-- The preorder is induced by refinement of the corresponding data. -/
instance instPreorderProCIntegerIndex (C : FiniteGroupClass.{u}) : Preorder (ProCIntegerIndex C)
    where
  le := (· ≤ ·)
  le_refl i := dvd_rfl
  le_trans _ _ _ hij hjk := dvd_trans hij hjk

/-- A coefficient index built from an allowed positive modulus. -/
def ofModulus {C : FiniteGroupClass.{u}} (n : ℕ) (hn : 0 < n)
    (hC : C.MemAcrossUniverses (Multiplicative (ZMod n))) : ProCIntegerIndex C where
  modulus := n
  positive := hn
  cyclic_mem := hC

/--
The positivity certificate carried by a coefficient index, packaged for formulations requiring
Fact.
-/
theorem positiveFact {C : FiniteGroupClass.{u}} (i : ProCIntegerIndex C) :
    Fact (0 < i.modulus) :=
  ⟨i.positive⟩

/--
The terminal coefficient index \(\mathbb{Z}/1\mathbb{Z}\), available when \(C\) contains trivial
quotients.
-/
def terminal {C : FiniteGroupClass.{u}} (htriv : FiniteGroupClass.ContainsTrivialQuotients C) :
    ProCIntegerIndex C where
  modulus := 1
  positive := Nat.zero_lt_one
  cyclic_mem := memAcrossUniverses_of_ulift_mem (htriv.of_subsingleton inferInstance)

/-- Every positive modulus is allowed for the all-finite class. -/
def ofAllFiniteModulus (n : ℕ) (hn : 0 < n) :
    ProCIntegerIndex (FiniteGroupClass.allFinite : FiniteGroupClass.{u}) where
  modulus := n
  positive := hn
  cyclic_mem := memAcrossUniverses_of_ulift_mem (by
    have : NeZero n := ⟨Nat.ne_of_gt hn⟩
    exact Finite.of_equiv (ZMod n) (Multiplicative.ofAdd.trans Equiv.ulift.symm))

/-- The all-finite coefficient index has the prescribed modulus. -/
@[simp]
theorem modulus_ofAllFiniteModulus (n : ℕ) (hn : 0 < n) :
    (ofAllFiniteModulus n hn).modulus = n :=
  rfl

/--
The order of an element of a finite \(C\)-group is an allowed coefficient modulus for hereditary
classes.
-/
def ofElementOrder {C : FiniteGroupClass.{u}}
    (hHer : FiniteGroupClass.Hereditary C)
    {K : Type u} [Group K] [Finite K] (hK : C K) (k : K) :
    ProCIntegerIndex C := by
  letI : NeZero (orderOf k) := ⟨Nat.ne_of_gt (orderOf_pos k)⟩
  refine ofModulus (orderOf k) (orderOf_pos k) ?_
  let fInt : ℤ →+ Additive (Subgroup.zpowers k) :=
  { toFun := fun z => Additive.ofMul ⟨k ^ z, z, rfl⟩
    map_zero' := by
      apply Additive.ext
      ext
      simp only [zpow_zero, toMul_ofMul, toMul_zero, OneMemClass.coe_one]
    map_add' a b := by
      apply Additive.ext
      ext
      simp only [zpow_add, toMul_ofMul, toMul_add, Subgroup.coe_mul]}
  have hfInt_order : fInt (orderOf k) = 0 := by
    apply Additive.ext
    ext
    change k ^ ((orderOf k : ℕ) : ℤ) = 1
    simp only [zpow_natCast, pow_orderOf_eq_one]
  let fZ : ZMod (orderOf k) →+ Additive (Subgroup.zpowers k) :=
    (ZMod.lift (orderOf k)) ⟨fInt, hfInt_order⟩
  have hfZ_inj : Function.Injective fZ := by
    rw [ZMod.lift_injective]
    intro m hm
    have hpow : k ^ m = 1 := by
      have hm' : (⟨k ^ m, m, rfl⟩ : Subgroup.zpowers k) = 1 := by
        change (fInt m).toMul = (0 : Additive (Subgroup.zpowers k)).toMul
        exact congrArg Additive.toMul hm
      simpa using congrArg Subtype.val hm'
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd m (orderOf k)).2
      ((orderOf_dvd_iff_zpow_eq_one (x := k) (i := m)).2 hpow)
  let φ0 : Multiplicative (ZMod (orderOf k)) →* Subgroup.zpowers k :=
    AddMonoidHom.toMultiplicativeLeft fZ
  let uliftDown :
      ULift (Multiplicative (ZMod (orderOf k))) →*
        Multiplicative (ZMod (orderOf k)) :=
  { toFun := fun x => x.down
    map_one' := rfl
    map_mul' := by
      intro x y
      cases x
      cases y
      rfl }
  let φ : ULift (Multiplicative (ZMod (orderOf k))) →* K :=
    (Subgroup.zpowers k).subtype.comp (φ0.comp uliftDown)
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    have hval :
        ((φ0 a.down : Subgroup.zpowers k) : K) =
          ((φ0 b.down : Subgroup.zpowers k) : K) := by
      simpa [φ, uliftDown] using hab
    have hsub : φ0 a.down = φ0 b.down := Subtype.ext hval
    have hadd : fZ a.down.toAdd = fZ b.down.toAdd := by
      apply Additive.ext
      simpa [φ0] using hsub
    have hz : a.down.toAdd = b.down.toAdd := hfZ_inj hadd
    apply ULift.ext
    exact Multiplicative.ext hz
  exact memAcrossUniverses_of_ulift_mem (hHer.of_injective hK φ hφ_inj)

/-- Formation closure makes the allowed coefficient moduli directed by common multiples. -/
theorem directed_of_formation {C : FiniteGroupClass.{u}} (hForm : FiniteGroupClass.Formation C) :
    Directed (· ≤ ·) (id : ProCIntegerIndex C → ProCIntegerIndex C) := by
  classical
  intro i j
  let n := Nat.lcm i.modulus j.modulus
  have hn : 0 < n := Nat.lcm_pos i.positive j.positive
  have hi : i.modulus ∣ n := Nat.dvd_lcm_left i.modulus j.modulus
  have hj : j.modulus ∣ n := Nat.dvd_lcm_right i.modulus j.modulus
  let A : Type u := ULift.{u} (Multiplicative (ZMod n))
  let K : ULift Bool → Type u
    | ⟨false⟩ => ULift.{u} (Multiplicative (ZMod i.modulus))
    | ⟨true⟩ => ULift.{u} (Multiplicative (ZMod j.modulus))
  let : ∀ b : ULift Bool, Group (K b) := by
    intro b
    cases b with
    | up b =>
      cases b <;> infer_instance
  let f : A →* (∀ b : ULift Bool, K b) := {
    toFun := fun x b => by
      cases b with
      | up b =>
        cases b
        · exact ULift.up
            (Multiplicative.ofAdd (ZMod.castHom hi (ZMod i.modulus) x.down.toAdd))
        · exact ULift.up
            (Multiplicative.ofAdd (ZMod.castHom hj (ZMod j.modulus) x.down.toAdd))
    map_one' := by
      funext b
      cases b with
      | up b =>
        cases b
        · change
            ULift.up
              (Multiplicative.ofAdd
                (ZMod.castHom hi (ZMod i.modulus) (0 : ZMod n))) =
              (1 : ULift (Multiplicative (ZMod i.modulus)))
          ext
          simp only [ZMod.castHom_apply, ZMod.cast_zero, ofAdd_zero, toAdd_one, ULift.one_down]
        · change
            ULift.up
              (Multiplicative.ofAdd
                (ZMod.castHom hj (ZMod j.modulus) (0 : ZMod n))) =
              (1 : ULift (Multiplicative (ZMod j.modulus)))
          ext
          simp only [ZMod.castHom_apply, ZMod.cast_zero, ofAdd_zero, toAdd_one, ULift.one_down]
    map_mul' := by
      intro x y
      funext b
      cases b with
      | up b =>
        cases b
        · cases x with
          | up x =>
          cases y with
          | up y =>
            change
              ULift.up
                (Multiplicative.ofAdd
                  (ZMod.castHom hi (ZMod i.modulus) (x.toAdd + y.toAdd))) =
                ULift.up
                  (Multiplicative.ofAdd
                    (ZMod.castHom hi (ZMod i.modulus) x.toAdd +
                      ZMod.castHom hi (ZMod i.modulus) y.toAdd))
            ext
            exact (ZMod.castHom hi (ZMod i.modulus)).map_add x.toAdd y.toAdd
        · cases x with
          | up x =>
          cases y with
          | up y =>
            change
              ULift.up
                (Multiplicative.ofAdd
                  (ZMod.castHom hj (ZMod j.modulus) (x.toAdd + y.toAdd))) =
                ULift.up
                  (Multiplicative.ofAdd
                    (ZMod.castHom hj (ZMod j.modulus) x.toAdd +
                      ZMod.castHom hj (ZMod j.modulus) y.toAdd))
            ext
            exact (ZMod.castHom hj (ZMod j.modulus)).map_add x.toAdd y.toAdd
  }
  have hf : Function.Injective f := by
    intro x y hxy
    have hfalse :
        ZMod.castHom hi (ZMod i.modulus) x.down.toAdd =
          ZMod.castHom hi (ZMod i.modulus) y.down.toAdd := by
      simpa [f, K] using congrFun hxy ⟨false⟩
    have htrue :
        ZMod.castHom hj (ZMod j.modulus) x.down.toAdd =
          ZMod.castHom hj (ZMod j.modulus) y.down.toAdd := by
      simpa [f, K] using congrFun hxy ⟨true⟩
    rcases ZMod.intCast_surjective x.down.toAdd with ⟨a, ha⟩
    rcases ZMod.intCast_surjective y.down.toAdd with ⟨b, hb⟩
    have hiab : (i.modulus : ℤ) ∣ a - b := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      rw [Int.cast_sub, sub_eq_zero]
      have ha_i :
          ZMod.castHom hi (ZMod i.modulus) x.down.toAdd = (a : ZMod i.modulus) := by
        simp only [← ha, map_intCast]
      have hb_i :
          ZMod.castHom hi (ZMod i.modulus) y.down.toAdd = (b : ZMod i.modulus) := by
        simp only [← hb, map_intCast]
      exact ha_i.symm.trans (hfalse.trans hb_i)
    have hjab : (j.modulus : ℤ) ∣ a - b := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      rw [Int.cast_sub, sub_eq_zero]
      have ha_j :
          ZMod.castHom hj (ZMod j.modulus) x.down.toAdd = (a : ZMod j.modulus) := by
        simp only [← ha, map_intCast]
      have hb_j :
          ZMod.castHom hj (ZMod j.modulus) y.down.toAdd = (b : ZMod j.modulus) := by
        simp only [← hb, map_intCast]
      exact ha_j.symm.trans (htrue.trans hb_j)
    have hnab_nat : n ∣ (a - b).natAbs := by
      exact Nat.lcm_dvd ((Int.natCast_dvd).1 hiab) ((Int.natCast_dvd).1 hjab)
    have hnab : (n : ℤ) ∣ a - b := (Int.natCast_dvd).2 hnab_nat
    have hab : (a : ZMod n) = (b : ZMod n) := by
      rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hnab
    have hxy_add : x.down.toAdd = y.down.toAdd := by
      calc
        x.down.toAdd = (a : ZMod n) := ha.symm
        _ = (b : ZMod n) := hab
        _ = y.down.toAdd := hb
    apply ULift.ext
    exact Multiplicative.ext hxy_add
  have hsurj : ∀ b : ULift Bool,
      Function.Surjective fun g : A => f g b := by
    intro b
    cases b with
    | up b =>
      cases b
      · intro y
        rcases ZMod.castHom_surjective hi y.down.toAdd with ⟨x, hx⟩
        refine ⟨ULift.up (Multiplicative.ofAdd x), ?_⟩
        cases y
        apply ULift.ext
        apply Multiplicative.ext
        exact hx
      · intro y
        rcases ZMod.castHom_surjective hj y.down.toAdd with ⟨x, hx⟩
        refine ⟨ULift.up (Multiplicative.ofAdd x), ?_⟩
        cases y
        apply ULift.ext
        apply Multiplicative.ext
        exact hx
  have hCK : ∀ b : ULift Bool, C (K b) := by
    intro b
    cases b with
    | up b =>
      cases b
      · simpa [K] using ulift_mem_of_memAcrossUniverses i.cyclic_mem
      · simpa [K] using ulift_mem_of_memAcrossUniverses j.cyclic_mem
  have hCn : C A :=
    hForm.finiteSubdirectProductClosed f hf hsurj hCK
  refine ⟨ofModulus n hn ?_, ?_, ?_⟩
  · exact memAcrossUniverses_of_ulift_mem (by simpa [A] using hCn)
  · exact hi
  · exact hj

/--
In a finite \(C\)-group, a single allowed coefficient modulus is divisible by every element
order.
-/
theorem exists_index_orderOf_dvd_of_finite_mem {C : FiniteGroupClass.{u}}
    (hForm : FiniteGroupClass.Formation C)
    (hHer : FiniteGroupClass.Hereditary C)
    {K : Type u} [Group K] [Finite K] (hK : C K) :
    ∃ i : ProCIntegerIndex C, ∀ k : K, orderOf k ∣ i.modulus := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hfinset :
      ∀ s : Finset K, ∃ i : ProCIntegerIndex C, ∀ k ∈ s, orderOf k ∣ i.modulus := by
    intro s
    induction s using Finset.induction with
    | empty =>
        exact ⟨ofElementOrder hHer hK (1 : K), by simp only [Finset.notMem_empty,
            IsEmpty.forall_iff, implies_true]⟩
    | insert a s has ih =>
        rcases ih with ⟨i, hi⟩
        let j := ofElementOrder hHer hK a
        rcases ProCIntegerIndex.directed_of_formation (C := C) hForm i j with ⟨m, hmi, hmj⟩
        refine ⟨m, ?_⟩
        intro k hk
        rw [Finset.mem_insert] at hk
        rcases hk with hk_eq | hk
        · subst k
          exact dvd_trans (by rfl : orderOf a ∣ j.modulus) hmj
        · exact dvd_trans (hi k hk) hmi
  rcases hfinset (Finset.univ : Finset K) with ⟨i, hi⟩
  exact ⟨i, fun k => hi k (Finset.mem_univ k)⟩

/-- In a finite \(C\)-group, some allowed coefficient modulus kills every element. -/
theorem exists_index_kills_finite_group_of_mem {C : FiniteGroupClass.{u}}
    (hForm : FiniteGroupClass.Formation C)
    (hHer : FiniteGroupClass.Hereditary C)
    {K : Type u} [Group K] [Finite K] (hK : C K) :
    ∃ i : ProCIntegerIndex C, ∀ k : K, k ^ i.modulus = 1 := by
  rcases exists_index_orderOf_dvd_of_finite_mem
      (C := C) hForm hHer hK with ⟨i, hi⟩
  exact ⟨i, fun k =>
    (orderOf_dvd_iff_pow_eq_one (x := k) (n := i.modulus)).1 (hi k)⟩

end ProCIntegerIndex

variable (C : FiniteGroupClass.{u})

/-- The finite cyclic stage \(\mathbb{Z}/n\mathbb{Z}\) of the pro-\(C\) integers. -/
abbrev ProCIntegerStage (i : ProCIntegerIndex C) : Type :=
  ZMod i.modulus

/-- The transition map between finite stages is induced by the corresponding quotient map. -/
def proCIntegerTransition {i j : ProCIntegerIndex C} (hij : i ≤ j) :
    ProCIntegerStage C j →+* ProCIntegerStage C i :=
  ZMod.castHom hij (ZMod i.modulus)

/-- The finite cyclic stages defining the pro-\(C\) integers as an inverse system. -/
def proCIntegerSystem : ProCGroups.InverseSystems.InverseSystem (I := ProCIntegerIndex C) where
  X := ProCIntegerStage C
  topologicalSpace := fun _ => inferInstance
  map := fun {i j} hij => proCIntegerTransition (C := C) hij
  continuous_map := by
    intro i j hij
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    ext x
    simp only [proCIntegerTransition, ZMod.castHom_self, RingHom.id_apply, id_eq]
  map_comp := by
    intro i j k hij hjk
    ext x
    exact congrArg (fun f : ZMod k.modulus →+* ZMod i.modulus => f x)
      (ZMod.castHom_comp hij hjk)

/-- The compatibility condition for a point of the inverse limit defining the pro-\(C\) integers. -/
def ProCIntegerCompatible
    (x : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i) : Prop :=
  ∀ i j, ∀ hij : i ≤ j, proCIntegerTransition (C := C) hij (x j) = x i

/--
Explicit carrier-level name for the current inverse-limit implementation of pro-\(C\) integers.
-/
abbrev ProCIntegerLimitCarrier : Type _ :=
  {x : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i // ProCIntegerCompatible C x}

/-- The projection from the pro-\(C\) integers to a finite cyclic stage. -/
def proCIntegerProj (i : ProCIntegerIndex C) : ProCIntegerLimitCarrier C → ProCIntegerStage C i :=
  fun x => x.1 i

/-- Extensionality for pro-\(C\) integers through their finite cyclic projections. -/
@[ext]
theorem ProCIntegerLimitCarrier.ext {x y : ProCIntegerLimitCarrier C}
    (h : ∀ i : ProCIntegerIndex C,
      proCIntegerProj (C := C) i x = proCIntegerProj (C := C) i y) :
    x = y :=
  Subtype.ext (funext h)

/--
The zero element is defined coordinatewise as the compatible family of zero elements at all
finite stages.
-/
instance instZeroProCInteger : Zero (ProCIntegerLimitCarrier C) where
  zero := ⟨fun _ => 0, by
    intro i j hij
    exact map_zero (proCIntegerTransition (C := C) hij)⟩

/--
Addition on the pro-\(C\) integer completion is defined coordinatewise through finite quotient
stages.
-/
instance instAddProCInteger : Add (ProCIntegerLimitCarrier C) where
  add x y := ⟨fun i => x.1 i + y.1 i, by
    intro i j hij
    rw [map_add]
    exact congrArg₂ HAdd.hAdd (x.2 i j hij) (y.2 i j hij)⟩

/--
Negation on the pro-\(C\) completed integers is defined coordinatewise through finite quotients.
-/
instance instNegProCInteger : Neg (ProCIntegerLimitCarrier C) where
  neg x := ⟨fun i => -x.1 i, by
    intro i j hij
    rw [map_neg]
    exact congrArg Neg.neg (x.2 i j hij)⟩

/--
Subtraction on the completed group algebra is defined coordinatewise through the finite-stage
group-algebra subtractions.
-/
instance instSubProCInteger : Sub (ProCIntegerLimitCarrier C) where
  sub x y := ⟨fun i => x.1 i - y.1 i, by
    intro i j hij
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 i j hij) (y.2 i j hij)⟩

/-- The pro-\(C\) completed integers carry natural-number scalar multiplication coordinatewise. -/
instance instSMulNatProCInteger : SMul ℕ (ProCIntegerLimitCarrier C) where
  smul n x := ⟨fun i => n • x.1 i, by
    intro i j hij
    rw [map_nsmul]
    exact congrArg (n • ·) (x.2 i j hij)⟩

/--
The completed group algebra carries integer scalar multiplication by applying the scalar action
at every finite quotient stage.
-/
instance instSMulIntProCInteger : SMul ℤ (ProCIntegerLimitCarrier C) where
  smul n x := ⟨fun i => n • x.1 i, by
    intro i j hij
    rw [map_zsmul]
    exact congrArg (n • ·) (x.2 i j hij)⟩

/-- The unit pro-\(C\) integer is defined coordinatewise. -/
instance instOneProCInteger : One (ProCIntegerLimitCarrier C) where
  one := ⟨fun _ => 1, by
    intro i j hij
    exact map_one (proCIntegerTransition (C := C) hij)⟩

/--
Multiplication on the pro-\(C\) completed integers is defined coordinatewise through finite
quotients.
-/
instance instMulProCInteger : Mul (ProCIntegerLimitCarrier C) where
  mul x y := ⟨fun i => x.1 i * y.1 i, by
    intro i j hij
    rw [map_mul]
    exact congrArg₂ HMul.hMul (x.2 i j hij) (y.2 i j hij)⟩

/--
Natural number casts in the pro-\(C\) integer completion are computed coordinatewise from
finite-stage natural number casts.
-/
instance instNatCastProCInteger : NatCast (ProCIntegerLimitCarrier C) where
  natCast n := ⟨fun _ => n, by
    intro i j hij
    exact map_natCast (proCIntegerTransition (C := C) hij) n⟩

/--
Integer casts in the pro-\(C\) integer completion are computed coordinatewise from finite-stage
integer casts.
-/
instance instIntCastProCInteger : IntCast (ProCIntegerLimitCarrier C) where
  intCast n := ⟨fun _ => n, by
    intro i j hij
    exact map_intCast (proCIntegerTransition (C := C) hij) n⟩

/-- The profinite or pro-\(C\) group object has powers computed at every finite-stage coordinate. -/
instance instPowProCInteger : Pow (ProCIntegerLimitCarrier C) ℕ where
  pow x n := ⟨fun i => x.1 i ^ n, by
    intro i j hij
    rw [map_pow]
    exact congrArg (fun t => t ^ n) (x.2 i j hij)⟩

/-- The underlying compatible family of pro-\(C\) integers computes zero coordinatewise. -/
@[simp]
theorem coe_zero_proCInteger :
    ((0 : ProCIntegerLimitCarrier C) : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i) = 0 := by
  funext i
  rfl

/-- The underlying compatible family of pro-\(C\) integers computes \(1\) coordinatewise. -/
@[simp]
theorem coe_one_proCInteger :
    ((1 : ProCIntegerLimitCarrier C) : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i) = 1 := by
  funext i
  rfl

/-- The underlying compatible family of pro-\(C\) integers computes addition coordinatewise. -/
@[simp]
theorem coe_add_proCInteger (x y : ProCIntegerLimitCarrier C) :
    ((x + y : ProCIntegerLimitCarrier C) : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i) = x +
        y := by
  funext i
  rfl

/--
The underlying compatible family of pro-\(C\) integers computes multiplication coordinatewise.
-/
@[simp]
theorem coe_mul_proCInteger (x y : ProCIntegerLimitCarrier C) :
    ((x * y : ProCIntegerLimitCarrier C) : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i) = x *
        y := by
  funext i
  rfl

/-- The underlying compatible family of pro-\(C\) integers computes negation coordinatewise. -/
@[simp]
theorem coe_neg_proCInteger (x : ProCIntegerLimitCarrier C) :
    ((-x : ProCIntegerLimitCarrier C) : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i) = -x := by
  funext i
  rfl

/-- The underlying compatible family of pro-\(C\) integers computes subtraction coordinatewise. -/
@[simp]
theorem coe_sub_proCInteger (x y : ProCIntegerLimitCarrier C) :
    ((x - y : ProCIntegerLimitCarrier C) : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i) = x -
        y := by
  funext i
  rfl

/--
The underlying compatible family of pro-\(C\) integers computes natural number casts
coordinatewise.
-/
@[simp]
theorem coe_natCast_proCInteger (n : ℕ) :
    ((n : ProCIntegerLimitCarrier C) : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i) = n := by
  funext i
  rfl

/-- The underlying compatible family of pro-\(C\) integers computes integer casts coordinatewise. -/
@[simp]
theorem coe_intCast_proCInteger (n : ℤ) :
    ((n : ProCIntegerLimitCarrier C) : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i) =
      fun i => (n : ProCIntegerStage C i) := by
  funext i
  rfl

/-- The underlying compatible family of pro-\(C\) integers computes powers coordinatewise. -/
@[simp]
theorem coe_pow_proCInteger (x : ProCIntegerLimitCarrier C) (n : ℕ) :
    ((x ^ n : ProCIntegerLimitCarrier C) : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i) = x ^
        n := by
  funext i
  rfl

/--
The pro-\(C\) integer completion inherits a ring structure from the compatible finite-stage
rings.
-/
instance instCommRingProCInteger : CommRing (ProCIntegerLimitCarrier C) :=
  Function.Injective.commRing
    (fun x : ProCIntegerLimitCarrier C => (x : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i))
    Subtype.val_injective
    (coe_zero_proCInteger (C := C))
    (coe_one_proCInteger (C := C))
    (coe_add_proCInteger (C := C))
    (coe_mul_proCInteger (C := C))
    (coe_neg_proCInteger (C := C))
    (coe_sub_proCInteger (C := C))
    (by intro n x; funext i; change (n • x).1 i = n • x.1 i; rfl)
    (by intro n x; funext i; change (n • x).1 i = n • x.1 i; rfl)
    (coe_pow_proCInteger (C := C))
    (coe_natCast_proCInteger (C := C))
    (coe_intCast_proCInteger (C := C))

/-- Finite projections of pro-\(C\) integers commute with 0. -/
@[simp]
theorem proCIntegerProj_zero (i : ProCIntegerIndex C) :
    proCIntegerProj (C := C) i (0 : ProCIntegerLimitCarrier C) = 0 :=
  by rfl

/-- Finite projections of pro-\(C\) integers commute with 1. -/
@[simp]
theorem proCIntegerProj_one (i : ProCIntegerIndex C) :
    proCIntegerProj (C := C) i (1 : ProCIntegerLimitCarrier C) = 1 :=
  by rfl

/-- Finite projections of pro-\(C\) integers commute with addition. -/
@[simp]
theorem proCIntegerProj_add (i : ProCIntegerIndex C) (x y : ProCIntegerLimitCarrier C) :
    proCIntegerProj (C := C) i (x + y) =
      proCIntegerProj (C := C) i x + proCIntegerProj (C := C) i y :=
  by
    change (x + y).1 i = x.1 i + y.1 i
    rfl

/-- Finite projections of pro-\(C\) integers commute with multiplication. -/
@[simp]
theorem proCIntegerProj_mul (i : ProCIntegerIndex C) (x y : ProCIntegerLimitCarrier C) :
    proCIntegerProj (C := C) i (x * y) =
      proCIntegerProj (C := C) i x * proCIntegerProj (C := C) i y :=
  by
    change (x * y).1 i = x.1 i * y.1 i
    rfl

/-- Finite projections of pro-\(C\) integers commute with negation. -/
@[simp]
theorem proCIntegerProj_neg (i : ProCIntegerIndex C) (x : ProCIntegerLimitCarrier C) :
    proCIntegerProj (C := C) i (-x) = -proCIntegerProj (C := C) i x :=
  by
    change (-x).1 i = -x.1 i
    rfl

/-- Finite projections of pro-\(C\) integers commute with subtraction. -/
@[simp]
theorem proCIntegerProj_sub (i : ProCIntegerIndex C) (x y : ProCIntegerLimitCarrier C) :
    proCIntegerProj (C := C) i (x - y) =
      proCIntegerProj (C := C) i x - proCIntegerProj (C := C) i y :=
  by
    change (x - y).1 i = x.1 i - y.1 i
    rfl

/-- Finite projections of pro-\(C\) integers commute with natural number casts. -/
@[simp]
theorem proCIntegerProj_natCast (i : ProCIntegerIndex C) (n : ℕ) :
    proCIntegerProj (C := C) i (n : ProCIntegerLimitCarrier C) = n :=
  by rfl

/-- Finite projections of pro-\(C\) integers commute with integer casts. -/
@[simp]
theorem proCIntegerProj_intCast (i : ProCIntegerIndex C) (n : ℤ) :
    proCIntegerProj (C := C) i (n : ProCIntegerLimitCarrier C) = n :=
  by rfl

/--
The projection from the pro-\(C\) integers to a finite cyclic stage is bundled as a ring
homomorphism.
-/
def proCIntegerProjRingHom (i : ProCIntegerIndex C) :
    ProCIntegerLimitCarrier C →+* ProCIntegerStage C i where
  toFun := proCIntegerProj (C := C) i
  map_zero' := by simp only [proCIntegerProj_zero]
  map_one' := by simp only [proCIntegerProj_one]
  map_add' := by intro x y; simp only [proCIntegerProj_add]
  map_mul' := by intro x y; simp only [proCIntegerProj_mul]

/--
The bundled ring homomorphism has the same underlying function as the coordinatewise
construction.
-/
@[simp]
theorem proCIntegerProjRingHom_apply (i : ProCIntegerIndex C) (x : ProCIntegerLimitCarrier C) :
    proCIntegerProjRingHom (C := C) i x = proCIntegerProj (C := C) i x :=
  by rfl

/-- Each finite projection from the pro-\(C\) integer ring is continuous. -/
theorem continuous_proCIntegerProj (i : ProCIntegerIndex C) :
    Continuous (proCIntegerProj (C := C) i) :=
  (continuous_apply i).comp continuous_subtype_val

/-- Compatibility of the finite projections with reduction maps. -/
theorem proCIntegerProj_transition {i j : ProCIntegerIndex C} (hij : i ≤ j)
    (x : ProCIntegerLimitCarrier C) :
    proCIntegerTransition (C := C) hij (proCIntegerProj (C := C) j x) =
      proCIntegerProj (C := C) i x :=
  x.2 i j hij

/-- A finite cyclic stage belongs to `C` across universes. This is the public stage-membership API;
it avoids exposing a Type-0 specialization or requiring a separately supplied isomorphism-closure
hypothesis. -/
theorem multiplicative_proCIntegerStage_mem
    {C : FiniteGroupClass.{u}} (i : ProCIntegerIndex C) :
    C.MemAcrossUniverses (Multiplicative (ProCIntegerStage C i)) := by
  simpa [ProCIntegerStage] using i.cyclic_mem

/-- Each finite multiplicative cyclic stage has an open-normal \(C\)-basis when \(C\) is
quotient-closed. -/
theorem hasOpenNormalBasisInClass_multiplicative_proCIntegerStage
    {C : FiniteGroupClass.{0}}
    (hQuot : FiniteGroupClass.QuotientClosed C)
    (i : ProCIntegerIndex C) :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (Multiplicative (ProCIntegerStage C i)) := by
  have : NeZero i.modulus := ⟨Nat.ne_of_gt i.positive⟩
  have : Finite (Multiplicative (ProCIntegerStage C i)) :=
    Finite.of_equiv (ZMod i.modulus) Multiplicative.ofAdd
  exact ProCGroups.ProC.HasOpenNormalBasisInClass.of_finite_discrete (C := C)
    (G := Multiplicative (ProCIntegerStage C i)) hQuot
    ((C.memAcrossUniverses_iff).1
      (multiplicative_proCIntegerStage_mem (C := C) i))

/-- The group-valued inverse system obtained from the finite cyclic coefficient stages. -/
def proCIntegerMultiplicativeSystem (C : FiniteGroupClass.{u}) :
    ProCGroups.InverseSystems.InverseSystem (I := ProCIntegerIndex C) where
  X := fun i => Multiplicative (ProCIntegerStage C i)
  topologicalSpace := fun _ => inferInstance
  map := fun {i j} hij =>
    (proCIntegerTransition (C := C) hij).toAddMonoidHom.toMultiplicative
  continuous_map := by
    intro i j hij
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    ext x
    apply Multiplicative.ext
    change proCIntegerTransition (C := C) (le_rfl : i ≤ i) x.toAdd = x.toAdd
    simp only [proCIntegerTransition, ZMod.castHom_self, RingHom.id_apply]
  map_comp := by
    intro i j k hij hjk
    ext x
    apply Multiplicative.ext
    change
      proCIntegerTransition (C := C) hij
          (proCIntegerTransition (C := C) hjk x.toAdd) =
        proCIntegerTransition (C := C) (hij.trans hjk) x.toAdd
    exact congrArg (fun f : ZMod k.modulus →+* ZMod i.modulus => f x.toAdd)
      (ZMod.castHom_comp hij hjk)

/--
The constructed carrier inherits its group structure from the coordinatewise group structure of
the construction.
-/
instance instGroupProCIntegerMultiplicativeSystemStage
    (C : FiniteGroupClass.{u}) (i : ProCIntegerIndex C) :
    Group ((proCIntegerMultiplicativeSystem C).X i) := by
  dsimp [proCIntegerMultiplicativeSystem, ProCIntegerStage]
  infer_instance

/-- The object is a topological group with the induced group operations and topology. -/
instance instIsTopologicalGroupProCIntegerMultiplicativeSystemStage
    (C : FiniteGroupClass.{u}) (i : ProCIntegerIndex C) :
    IsTopologicalGroup ((proCIntegerMultiplicativeSystem C).X i) := by
  have : DiscreteTopology ((proCIntegerMultiplicativeSystem C).X i) :=
    inferInstanceAs (DiscreteTopology (Multiplicative (ZMod i.modulus)))
  exact topologicalGroup_of_discreteTopology

/-- The pro-\(C\) integer multiplicative system carries the induced group-system structure. -/
instance instIsGroupSystemProCIntegerMultiplicativeSystem
    (C : FiniteGroupClass.{u}) :
    ProCGroups.InverseSystems.IsGroupSystem
      (proCIntegerMultiplicativeSystem C) where
  map_one := by
    intro i j hij
    dsimp [proCIntegerMultiplicativeSystem, ProCIntegerStage]
    apply Multiplicative.ext
    exact map_zero (proCIntegerTransition (C := C) hij)
  map_mul := by
    intro i j hij x y
    dsimp [proCIntegerMultiplicativeSystem, ProCIntegerStage] at x y ⊢
    apply Multiplicative.ext
    exact map_add (proCIntegerTransition (C := C) hij) x.toAdd y.toAdd
  map_inv := by
    intro i j hij x
    dsimp [proCIntegerMultiplicativeSystem, ProCIntegerStage] at x ⊢
    apply Multiplicative.ext
    exact map_neg (proCIntegerTransition (C := C) hij) x.toAdd

/--
The inverse limit of the multiplicative finite stages is the multiplicative group underlying the
pro-\(C\) integers.
-/
def proCIntegerMultiplicativeLimitEquiv
    (C : FiniteGroupClass.{u}) :
    (proCIntegerMultiplicativeSystem C).inverseLimit ≃ₜ*
      Multiplicative (ProCIntegerLimitCarrier C) := by
  let S := proCIntegerMultiplicativeSystem C
  refine
    { toMulEquiv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · refine
      { toFun := fun x =>
          Multiplicative.ofAdd
            (⟨fun i => (S.projection i x).toAdd, by
              intro i j hij
              exact congrArg Multiplicative.toAdd (S.projection_compatible x i j hij)⟩ :
              ProCIntegerLimitCarrier C)
        invFun := fun x =>
          (⟨fun i => Multiplicative.ofAdd (proCIntegerProj (C := C) i x.toAdd), by
            intro i j hij
            apply Multiplicative.ext
            exact proCIntegerProj_transition (C := C) hij x.toAdd⟩ :
            S.inverseLimit)
        left_inv := by
          intro x
          apply S.ext
          intro i
          rfl
        right_inv := by
          intro x
          apply Multiplicative.ext
          ext i
          rfl
        map_mul' := by
          intro x y
          apply Multiplicative.ext
          ext i
          rfl }
  · refine continuous_ofAdd.comp ?_
    have hambient : Continuous fun x : S.inverseLimit =>
        (fun i : ProCIntegerIndex C => (S.projection i x).toAdd :
          ∀ i : ProCIntegerIndex C, ProCIntegerStage C i) := by
      exact continuous_pi fun i => continuous_toAdd.comp (S.continuous_projection i)
    exact Continuous.subtype_mk hambient (fun x => by
      intro i j hij
      exact congrArg Multiplicative.toAdd (S.projection_compatible x i j hij))
  · have hambient : Continuous fun x : Multiplicative (ProCIntegerLimitCarrier C) =>
        (fun i : ProCIntegerIndex C =>
          Multiplicative.ofAdd (proCIntegerProj (C := C) i x.toAdd) :
          ∀ i : ProCIntegerIndex C, S.X i) := by
      exact continuous_pi fun i =>
        continuous_ofAdd.comp
          ((continuous_proCIntegerProj (C := C) i).comp continuous_toAdd)
    exact Continuous.subtype_mk hambient (fun x => by
      intro i j hij
      apply Multiplicative.ext
      exact proCIntegerProj_transition (C := C) hij x.toAdd)

/-- A directed pro-\(C\) integer coefficient system has an open-normal \(C\)-basis on its
multiplicative inverse limit. -/
theorem hasOpenNormalBasisInClass_proCIntegerMultiplicativeSystem_inverseLimit
    {C : FiniteGroupClass.{0}}
    [Nonempty (ProCIntegerIndex C)]
    (hIso : FiniteGroupClass.IsomClosed C)
    (hQuot : FiniteGroupClass.QuotientClosed C)
    (hdir : Directed (· ≤ ·) (id : ProCIntegerIndex C → ProCIntegerIndex C)) :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (proCIntegerMultiplicativeSystem C).inverseLimit
        := by
  let S : ProCGroups.InverseSystems.InverseSystem (I := ProCIntegerIndex C) :=
    proCIntegerMultiplicativeSystem C
  have : ∀ i : ProCIntegerIndex C, Finite (S.X i) := fun i => by
    have : NeZero i.modulus := ⟨Nat.ne_of_gt i.positive⟩
    exact Finite.of_equiv (ZMod i.modulus) Multiplicative.ofAdd
  have : ∀ i : ProCIntegerIndex C, DiscreteTopology (S.X i) := fun i =>
    inferInstanceAs (DiscreteTopology (Multiplicative (ZMod i.modulus)))
  exact ProCGroups.ProC.inverseLimit (S := S) hIso hQuot hdir
    (fun i => hasOpenNormalBasisInClass_multiplicative_proCIntegerStage
      (C := C) hQuot i)

/--
The compatibility condition defining pro-\(C\) integers is closed in the product of the finite
cyclic stages.
-/
theorem isClosed_setOf_proCIntegerCompatible :
    IsClosed {x : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i |
      ProCIntegerCompatible C x} := by
  simp only [ProCIntegerCompatible, Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun hij => ?_
  have hleft :
      Continuous fun x : (∀ k : ProCIntegerIndex C, ProCIntegerStage C k) =>
        proCIntegerTransition (C := C) hij (x j) := by
    exact (continuous_of_discreteTopology :
      Continuous (proCIntegerTransition (C := C) hij)).comp (continuous_apply j)
  exact isClosed_eq hleft (continuous_apply i)

/--
The constructed object carries the compact space structure inherited from its profinite
construction.
-/
instance instCompactSpaceProCInteger : CompactSpace (ProCIntegerLimitCarrier C) := by
  let : ∀ i : ProCIntegerIndex C, CompactSpace (ProCIntegerStage C i) := fun i => by
    have : NeZero i.modulus := ⟨Nat.ne_of_gt i.positive⟩
    dsimp [ProCIntegerStage]
    infer_instance
  let hs : IsClosed {x : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i |
      ProCIntegerCompatible C x} :=
    isClosed_setOf_proCIntegerCompatible (C := C)
  change CompactSpace {x : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i //
    ProCIntegerCompatible C x}
  exact hs.isClosedEmbedding_subtypeVal.compactSpace

/--
The constructed object is Hausdorff, with its \(T_2\) structure inherited from the profinite
construction.
-/
instance instT2SpaceProCInteger : T2Space (ProCIntegerLimitCarrier C) := by
  change T2Space {x : ∀ i : ProCIntegerIndex C, ProCIntegerStage C i //
    ProCIntegerCompatible C x}
  infer_instance

/-- Addition on the pro-\(C\) integer completion is continuous for the inverse-limit topology. -/
instance instContinuousAddProCInteger : ContinuousAdd (ProCIntegerLimitCarrier C) where
  continuous_add := by
    refine Continuous.subtype_mk (continuous_pi fun i => ?_) (fun p => (p.1 + p.2).2)
    change Continuous fun p : ProCIntegerLimitCarrier C × ProCIntegerLimitCarrier C =>
      proCIntegerProj (C := C) i p.1 + proCIntegerProj (C := C) i p.2
    exact ((continuous_proCIntegerProj (C := C) i).comp continuous_fst).add
      ((continuous_proCIntegerProj (C := C) i).comp continuous_snd)

/--
Multiplication on the pro-\(C\) integer completion is continuous for the inverse-limit topology.
-/
instance instContinuousMulProCInteger : ContinuousMul (ProCIntegerLimitCarrier C) where
  continuous_mul := by
    refine Continuous.subtype_mk (continuous_pi fun i => ?_) (fun p => (p.1 * p.2).2)
    change Continuous fun p : ProCIntegerLimitCarrier C × ProCIntegerLimitCarrier C =>
      proCIntegerProj (C := C) i p.1 * proCIntegerProj (C := C) i p.2
    exact ((continuous_proCIntegerProj (C := C) i).comp continuous_fst).mul
      ((continuous_proCIntegerProj (C := C) i).comp continuous_snd)

/-- Negation on the pro-\(C\) integer completion is continuous for the inverse-limit topology. -/
instance instContinuousNegProCInteger : ContinuousNeg (ProCIntegerLimitCarrier C) where
  continuous_neg := by
    refine Continuous.subtype_mk (continuous_pi fun i => ?_) (fun x => (-x).2)
    change Continuous fun x : ProCIntegerLimitCarrier C => -proCIntegerProj (C := C) i x
    exact (continuous_proCIntegerProj (C := C) i).neg

/--
The coordinatewise ring operations make the pro-\(C\) integer completion a topological ring.
-/
instance instIsTopologicalRingProCInteger : IsTopologicalRing (ProCIntegerLimitCarrier C) := by
  exact
    { toIsTopologicalSemiring := IsTopologicalSemiring.mk
      toContinuousNeg := instContinuousNegProCInteger (C := C) }

/-- The additive group underlying the pro-\(C\) integers, written multiplicatively, has an
open-normal \(C\)-basis whenever the coefficient indices are directed and \(C\) is isomorphism- and
quotient-closed. -/
theorem hasOpenNormalBasisInClass_multiplicative_proCInteger
    {C : FiniteGroupClass.{0}}
    [Nonempty (ProCIntegerIndex C)]
    (hIso : FiniteGroupClass.IsomClosed C)
    (hQuot : FiniteGroupClass.QuotientClosed C)
    (hdir : Directed (· ≤ ·) (id : ProCIntegerIndex C → ProCIntegerIndex C)) :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (Multiplicative (ProCIntegerLimitCarrier C)) := by
  let S := proCIntegerMultiplicativeSystem C
  have hS : ProCGroups.ProC.HasOpenNormalBasisInClass C S.inverseLimit :=
    hasOpenNormalBasisInClass_proCIntegerMultiplicativeSystem_inverseLimit
      (C := C) hIso hQuot hdir
  exact ProCGroups.ProC.HasOpenNormalBasisInClass.ofContinuousMulEquiv (C := C) hS
    (proCIntegerMultiplicativeLimitEquiv C)

/-- Integer constants in the pro-\(C\) integers. -/
def intToProCInteger : ℤ →+* ProCIntegerLimitCarrier C where
  toFun n := (n : ProCIntegerLimitCarrier C)
  map_zero' := by ext i; exact Int.cast_zero
  map_one' := by ext i; exact Int.cast_one
  map_add' := by intro m n; ext i; exact Int.cast_add m n
  map_mul' := by intro m n; ext i; exact Int.cast_mul m n

/-- The bundled integer embedding evaluates to the coordinatewise integer cast in the limit. -/
@[simp]
theorem intToProCInteger_apply (n : ℤ) :
    intToProCInteger (C := C) n = (n : ProCIntegerLimitCarrier C) :=
  by rfl

/--
Projecting an integer embedded in the pro-\(C\) integers gives its residue class at that
modulus.
-/
@[simp]
theorem proCIntegerProj_intToProCInteger (i : ProCIntegerIndex C) (n : ℤ) :
    proCIntegerProj (C := C) i (intToProCInteger (C := C) n) = (n : ZMod i.modulus) :=
  by rfl

/--
The ordinary integers are dense in the pro-\(C\) integer completion when the coefficient indices
are directed.
-/
theorem denseRange_intToProCInteger_of_directed
    [Nonempty (ProCIntegerIndex C)]
    (hdir : Directed (· ≤ ·) (id : ProCIntegerIndex C → ProCIntegerIndex C)) :
    DenseRange (intToProCInteger (C := C)) := by
  let S := proCIntegerSystem C
  let ρ : ∀ i : ProCIntegerIndex C, ℤ → S.X i := fun i n => (n : ZMod i.modulus)
  have hρ : S.CompatibleMaps ρ := by
    intro i j hij
    funext n
    exact map_intCast (ZMod.castHom hij (ZMod i.modulus)) n
  have hsurj : ∀ i, Function.Surjective (ρ i) := by
    intro i
    exact ZMod.intCast_surjective
  have hdense : DenseRange (S.inverseLimitLift ρ hρ) :=
    ProCGroups.InverseSystems.InverseSystem.denseRange_lift
      (S := S) ρ hρ hsurj hdir
  have hfun :
      (intToProCInteger (C := C) : ℤ → ProCIntegerLimitCarrier C) =
        S.inverseLimitLift ρ hρ := by
    funext n
    apply Subtype.ext
    rfl
  rw [hfun]
  exact hdense

/-- All-finite pro-integer coefficient indices are directed by common multiples. -/
theorem directed_proCIntegerIndex_allFinite :
    Directed (· ≤ ·)
      (id : ProCIntegerIndex (FiniteGroupClass.allFinite : FiniteGroupClass.{u}) →
        ProCIntegerIndex (FiniteGroupClass.allFinite : FiniteGroupClass.{u})) := by
  intro i j
  let n := Nat.lcm i.modulus j.modulus
  have hn : 0 < n := Nat.lcm_pos i.positive j.positive
  refine ⟨ProCIntegerIndex.ofAllFiniteModulus n hn, ?_, ?_⟩
  · change i.modulus ∣ n
    exact Nat.dvd_lcm_left i.modulus j.modulus
  · change j.modulus ∣ n
    exact Nat.dvd_lcm_right i.modulus j.modulus

/-- The multiplicative group of ordinary profinite integers has an open-normal basis for the
all-finite quotient class. -/
theorem hasOpenNormalBasisInClass_multiplicative_proCInteger_allFinite :
    ProCGroups.ProC.HasOpenNormalBasisInClass
      (FiniteGroupClass.allFinite : FiniteGroupClass.{0})
      (Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.allFinite : FiniteGroupClass.{0}))) := by
  let C : FiniteGroupClass.{0} := FiniteGroupClass.allFinite
  let : Nonempty (ProCIntegerIndex C) :=
    ⟨ProCIntegerIndex.ofAllFiniteModulus 1 Nat.zero_lt_one⟩
  simpa [C] using
    hasOpenNormalBasisInClass_multiplicative_proCInteger
      (C := C)
      FiniteGroupClass.allFinite_isomClosed
      FiniteGroupClass.allFinite_quotientClosed
      directed_proCIntegerIndex_allFinite

/--
The ordinary integers are dense in the profinite completion with all finite cyclic coefficient
stages.
-/
theorem denseRange_intToProCInteger_allFinite :
    DenseRange (intToProCInteger
      (C := (FiniteGroupClass.allFinite : FiniteGroupClass.{u}))) := by
  let C : FiniteGroupClass.{u} := FiniteGroupClass.allFinite
  let S := proCIntegerSystem C
  let ρ : ∀ i : ProCIntegerIndex C, ℤ → S.X i := fun i n => (n : ZMod i.modulus)
  have hρ : S.CompatibleMaps ρ := by
    intro i j hij
    funext n
    exact map_intCast (ZMod.castHom hij (ZMod i.modulus)) n
  have hsurj : ∀ i, Function.Surjective (ρ i) := by
    intro i
    exact ZMod.intCast_surjective
  let : Nonempty (ProCIntegerIndex C) :=
    ⟨ProCIntegerIndex.ofAllFiniteModulus 1 Nat.zero_lt_one⟩
  have hdense : DenseRange (S.inverseLimitLift ρ hρ) :=
    ProCGroups.InverseSystems.InverseSystem.denseRange_lift
      (S := S) ρ hρ hsurj directed_proCIntegerIndex_allFinite
  have hfun :
      (intToProCInteger (C := C) : ℤ → ProCIntegerLimitCarrier C) =
        S.inverseLimitLift ρ hρ := by
    funext n
    apply Subtype.ext
    rfl
  rw [hfun]
  exact hdense

/--
The distinguished multiplicative element corresponding to \(1\) in the additive pro-\(C\)
integers. It is a topological generator only for suitable finite-group classes.
-/
def proCIntegerOne : Multiplicative (ProCIntegerLimitCarrier C) :=
  Multiplicative.ofAdd (1 : ProCIntegerLimitCarrier C)

/--
The canonical homomorphism from the infinite cyclic group to multiplicative pro-\(C\) integers.
-/
def multiplicativeIntToProCInteger :
    Multiplicative ℤ →* Multiplicative (ProCIntegerLimitCarrier C) where
  toFun z := Multiplicative.ofAdd ((z.toAdd : ℤ) : ProCIntegerLimitCarrier C)
  map_one' := by
    apply Multiplicative.ext
    simp only [toAdd_one, Int.cast_zero, ofAdd_zero]
  map_mul' z w := by
    apply Multiplicative.ext
    ext i
    change (((z * w).toAdd : ℤ) : ProCIntegerStage C i) =
      ((z.toAdd : ℤ) : ProCIntegerStage C i) + ((w.toAdd : ℤ) : ProCIntegerStage C i)
    exact Int.cast_add z.toAdd w.toAdd

/--
On the multiplicative copy of an integer `n`, the canonical cyclic homomorphism returns the
multiplicative form of the coordinatewise cast of `n` into the pro-\(C\) integers.
-/
@[simp]
theorem multiplicativeIntToProCInteger_apply (n : ℤ) :
    multiplicativeIntToProCInteger (C := C) (Multiplicative.ofAdd n) =
      Multiplicative.ofAdd ((n : ℤ) : ProCIntegerLimitCarrier C) :=
  rfl

/-- The dense infinite-cyclic map sends n to the n-th power of the canonical generator. -/
theorem multiplicativeIntToProCInteger_zpow_one (n : ℤ) :
    multiplicativeIntToProCInteger (C := C) (Multiplicative.ofAdd n) =
      (proCIntegerOne (C := C)) ^ n := by
  apply Multiplicative.ext
  ext i
  simp only [multiplicativeIntToProCInteger, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
  proCIntegerProj_intCast, proCIntegerOne, toAdd_zpow, zsmul_eq_mul, mul_one]

/-- The multiplicative infinite-cyclic map is dense in the ordinary profinite integers. -/
theorem denseRange_multiplicativeIntToProCInteger_allFinite :
    DenseRange
      (multiplicativeIntToProCInteger
        (C := (FiniteGroupClass.allFinite : FiniteGroupClass.{u}))) := by
  let C : FiniteGroupClass.{u} := FiniteGroupClass.allFinite
  have hdense :
      Dense (Set.range fun n : ℤ =>
        (n : ProCIntegerLimitCarrier C)) :=
    denseRange_intToProCInteger_allFinite
  have hdense' :
      Dense (Set.range fun n : ℤ =>
        Multiplicative.ofAdd (n : ProCIntegerLimitCarrier C)) := by
    change Dense (Set.range fun n : ℤ => (n : ProCIntegerLimitCarrier C))
    exact hdense
  change Dense (Set.range fun z : Multiplicative ℤ =>
    Multiplicative.ofAdd (z.toAdd : ProCIntegerLimitCarrier C))
  have hrange :
      Set.range (fun z : Multiplicative ℤ =>
        Multiplicative.ofAdd (z.toAdd : ProCIntegerLimitCarrier C)) =
        Set.range (fun n : ℤ =>
          Multiplicative.ofAdd (n : ProCIntegerLimitCarrier C)) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.toAdd, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨Multiplicative.ofAdd n, rfl⟩
  rw [hrange]
  exact hdense'

/-- The distinguished element 1 topologically generates the ordinary profinite integers. -/
theorem topologicallyGenerates_singleton_proCIntegerOne_allFinite :
    ProCGroups.Generation.TopologicallyGenerates
      (G := Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.allFinite : FiniteGroupClass.{0})))
      ({proCIntegerOne
        (C := (FiniteGroupClass.allFinite : FiniteGroupClass.{0}))} : Set _) := by
  let C : FiniteGroupClass.{0} := FiniteGroupClass.allFinite
  simpa [C, proCIntegerOne] using
    (ProCGroups.Generation.topologicallyGenerates_singleton_of_denseRange_mint
      (f := multiplicativeIntToProCInteger (C := C))
      denseRange_multiplicativeIntToProCInteger_allFinite)

/-- The ordinary profinite integers have a cyclic open-normal quotient basis. -/
theorem hasCyclicOpenNormalBasis_multiplicative_proCInteger_allFinite :
    ProCGroups.ProC.HasCyclicOpenNormalBasis
      (Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.allFinite : FiniteGroupClass.{0}))) := by
  let : T2Space
      (Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.allFinite : FiniteGroupClass.{0}))) := by
    change T2Space
      (ProCIntegerLimitCarrier (FiniteGroupClass.allFinite : FiniteGroupClass.{0}))
    exact instT2SpaceProCInteger
      (C := (FiniteGroupClass.allFinite : FiniteGroupClass.{0}))
  let : TotallyDisconnectedSpace
      (Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.allFinite : FiniteGroupClass.{0}))) := by
    change TotallyDisconnectedSpace
      (ProCIntegerLimitCarrier (FiniteGroupClass.allFinite : FiniteGroupClass.{0}))
    infer_instance
  exact ProCGroups.ProC.hasCyclicOpenNormalBasis_of_topologicallyGenerates_singleton
    (G := Multiplicative
      (ProCIntegerLimitCarrier (FiniteGroupClass.allFinite : FiniteGroupClass.{0})))
    topologicallyGenerates_singleton_proCIntegerOne_allFinite

end

end ProCGroups.Completion
