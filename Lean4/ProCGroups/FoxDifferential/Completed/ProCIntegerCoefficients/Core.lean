import ProCGroups.FoxDifferential.Common.CrossedDifferentialModule
import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.InClass.StageCoeffMap
import ProCGroups.Completion.ProCInteger

set_option autoImplicit false

/-!
# Fox differential: completed — \(\mathbb{Z}_C\) coefficients — core

The principal declarations in this module are:

- `ZCCoeff`
  The pro-\(C\) integer coefficient ring.
- `ZCCompletedGroupAlgebraIndex`
  The two-parameter finite-stage index for \(\mathbb{Z}_C\llbracket H\rrbracket\): a coefficient
  quotient of \(\mathbb{Z}_C\) and a finite \(C\)-quotient of \(H\).
- `zcCompletedGroupAlgebraTransition_of`
  Evaluation of a pro-\(C\) transition on a group-like basis element.
- `zcCompletedGroupAlgebraTransition_single`
  The transition map \(R[G/V] \to R[G/U]\) sends a singleton supported at a class of \(G/V\) to the
  singleton supported at its image in \(G/U\), with the same coefficient.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators
open ProCGroups.Completion
open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

/-- The pro-\(C\) integer coefficient ring. -/
abbrev ZCCoeff (C : ProCGroups.FiniteGroupClass.{u}) : Type _ :=
  ProCIntegerLimitCarrier C

/--
The two-parameter finite-stage index for \(\mathbb{Z}_C\llbracket H\rrbracket\): a coefficient
quotient of \(\mathbb{Z}_C\) and a finite \(C\)-quotient of \(H\).
-/
abbrev ZCCompletedGroupAlgebraIndex
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] : Type u :=
  ProCIntegerIndex C × CompletedGroupAlgebraIndexInClass H C

/-- A finite stage \((\mathbb{Z}/n\mathbb{Z})[H/U]\) of the pro-\(C\) completed group algebra. -/
abbrev ZCCompletedGroupAlgebraStage
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (i : ZCCompletedGroupAlgebraIndex C H) : Type u :=
  ModNCompletedGroupAlgebraStageInClass i.1.modulus H C i.2

/--
Transition maps for the true pro-\(C\) completed group algebra. The coefficient direction is
divisibility of allowed pro-\(C\) integer moduli, and the group direction is refinement of
\(C\)-quotients.
-/
def zcCompletedGroupAlgebraTransition
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {i j : ZCCompletedGroupAlgebraIndex C H} (hij : i ≤ j) :
    ZCCompletedGroupAlgebraStage C H j →+* ZCCompletedGroupAlgebraStage C H i := by
  letI : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  exact
    (modNCompletedGroupAlgebraStageCoeffMapInClass
        (n := i.1.modulus) (m := j.1.modulus) (G := H) C i.2 hij.1).comp
      (modNCompletedGroupAlgebraTransitionInClass (n := j.1.modulus) (G := H) C hij.2)

/-- Evaluation of a pro-\(C\) transition on a group-like basis element. -/
@[simp]
theorem zcCompletedGroupAlgebraTransition_of
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {i j : ZCCompletedGroupAlgebraIndex C H} (hij : i ≤ j)
    (q : CompletedGroupAlgebraQuotientInClass H C j.2) :
    zcCompletedGroupAlgebraTransition C H hij
        (MonoidAlgebra.of (ModNCompletedCoeff j.1.modulus) _ q) =
      MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus) _
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := H)
          (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q) := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  let : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  erw [zcCompletedGroupAlgebraTransition, RingHom.comp_apply,
    modNCompletedGroupAlgebraTransitionInClass_of,
    modNCompletedGroupAlgebraStageCoeffMapInClass_single_apply]
  rw [map_one]
  rfl

/--
The transition map \(R[G/V] \to R[G/U]\) sends a singleton supported at a class of \(G/V\) to
the singleton supported at its image in \(G/U\), with the same coefficient.
-/
@[simp]
theorem zcCompletedGroupAlgebraTransition_single
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {i j : ZCCompletedGroupAlgebraIndex C H} (hij : i ≤ j)
    (q : CompletedGroupAlgebraQuotientInClass H C j.2)
    (a : ModNCompletedCoeff j.1.modulus) :
    zcCompletedGroupAlgebraTransition C H hij (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := H)
          (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q)
        (modNCompletedCoeffMap (n := i.1.modulus) (m := j.1.modulus) hij.1 a) := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  let : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  erw [zcCompletedGroupAlgebraTransition, RingHom.comp_apply,
    modNCompletedGroupAlgebraTransitionInClass_single,
    modNCompletedGroupAlgebraStageCoeffMapInClass_single_apply]
  rfl

/--
The \(\mathbb{Z}_C\)-completed group-algebra transition for a reflexive refinement is the identity
ring homomorphism.
-/
@[simp]
theorem zcCompletedGroupAlgebraTransition_id
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (i : ZCCompletedGroupAlgebraIndex C H) :
    zcCompletedGroupAlgebraTransition C H (le_rfl : i ≤ i) = RingHom.id _ := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  rw [zcCompletedGroupAlgebraTransition]
  rw [modNCompletedGroupAlgebraTransitionInClass_id,
    modNCompletedGroupAlgebraStageCoeffMapInClass_rfl]
  simp only [RingHomCompTriple.comp_eq]

/-- \(\mathbb{Z}_C\)-completed group-algebra transitions compose along quotient refinements. -/
@[simp 900]
theorem zcCompletedGroupAlgebraTransition_comp
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {i j k : ZCCompletedGroupAlgebraIndex C H}
    (hij : i ≤ j) (hjk : j ≤ k) :
    (zcCompletedGroupAlgebraTransition C H hij).comp
        (zcCompletedGroupAlgebraTransition C H hjk) =
      zcCompletedGroupAlgebraTransition C H (hij.trans hjk) := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  let : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  let : Fact (0 < k.1.modulus) := ⟨k.1.positive⟩
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((zcCompletedGroupAlgebraTransition C H hij).comp
          (zcCompletedGroupAlgebraTransition C H hjk)) x =
        zcCompletedGroupAlgebraTransition C H (hij.trans hjk) x)
    x ?_ ?_ ?_
  · intro q
    erw [RingHom.comp_apply,
      zcCompletedGroupAlgebraTransition_of C H hjk,
      zcCompletedGroupAlgebraTransition_of C H hij,
      zcCompletedGroupAlgebraTransition_of C H (hij.trans hjk)]
    congr 1
    exact congrFun
      (congrArg DFunLike.coe
        (OpenNormalSubgroupInClass.map_comp
          (C := C) (G := H)
          (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2)
          (W := OrderDual.ofDual k.2) hij.2 hjk.2)) q
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    have hcoeff :
        ((zcCompletedGroupAlgebraTransition C H hij).comp
            (zcCompletedGroupAlgebraTransition C H hjk))
            (algebraMap (ModNCompletedCoeff k.1.modulus)
              (ZCCompletedGroupAlgebraStage C H k) a) =
          zcCompletedGroupAlgebraTransition C H (hij.trans hjk)
            (algebraMap (ModNCompletedCoeff k.1.modulus)
              (ZCCompletedGroupAlgebraStage C H k) a) := by
      rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
      simp only [zcCompletedGroupAlgebraTransition, modNCompletedGroupAlgebraStageCoeffMapInClass,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe,
      modNCompletedGroupAlgebraTransitionInClass, map_intCast]
    rw [hcoeff]

/-- The inverse system defining the pro-\(C\) completed group algebra. -/
def zcCompletedGroupAlgebraSystem
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    InverseSystem (I := ZCCompletedGroupAlgebraIndex C H) where
  X := ZCCompletedGroupAlgebraStage C H
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij => zcCompletedGroupAlgebraTransition C H hij
  continuous_map := by
    intro i j hij
    let : TopologicalSpace (ZCCompletedGroupAlgebraStage C H i) := ⊥
    let : TopologicalSpace (ZCCompletedGroupAlgebraStage C H j) := ⊥
    let : DiscreteTopology (ZCCompletedGroupAlgebraStage C H j) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (zcCompletedGroupAlgebraTransition_id C H i)) x
  map_comp := by
    intro i j k hij hjk
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (zcCompletedGroupAlgebraTransition_comp C H hij hjk)) x

/-- Compatibility for a family of finite \(\mathbb{Z}_C\llbracket H\rrbracket\) stage elements. -/
def ZCCompletedGroupAlgebraCompatible
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (x : ∀ i : ZCCompletedGroupAlgebraIndex C H, ZCCompletedGroupAlgebraStage C H i) : Prop :=
  ∀ i j, ∀ hij : i ≤ j, zcCompletedGroupAlgebraTransition C H hij (x j) = x i

/-- The completed group algebra \(\mathbb{Z}_C\llbracket H\rrbracket\). -/
abbrev ZCCompletedGroupAlgebra
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] : Type u :=
  {x : ∀ i : ZCCompletedGroupAlgebraIndex C H, ZCCompletedGroupAlgebraStage C H i //
    ZCCompletedGroupAlgebraCompatible C H x}

/--
The projection from \(\mathbb{Z}_C\llbracket H\rrbracket\) to a finite \(C\)-coefficient and
\(C\)-quotient stage.
-/
abbrev zcCompletedGroupAlgebraProjection
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (i : ZCCompletedGroupAlgebraIndex C H) :
    ZCCompletedGroupAlgebra C H → ZCCompletedGroupAlgebraStage C H i :=
  fun x => x.1 i

section Ring

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The zero element is defined coordinatewise as the compatible family of zero elements at all
finite stages.
-/
instance instZeroZCCompletedGroupAlgebra : Zero (ZCCompletedGroupAlgebra C H) where
  zero := ⟨fun i => 0, by intro i j hij; exact map_zero _⟩

/--
Addition on \(\mathbb{Z}_C\llbracket H\rrbracket\) is defined coordinatewise through
finite-stage group-algebra additions.
-/
instance instAddZCCompletedGroupAlgebra : Add (ZCCompletedGroupAlgebra C H) where
  add x y := ⟨fun i => x.1 i + y.1 i, by
    intro i j hij
    rw [map_add]
    exact congrArg₂ HAdd.hAdd (x.2 i j hij) (y.2 i j hij)⟩

/--
Negation on the \(\mathbb{Z}_C\)-completed group algebra is defined coordinatewise through
finite-stage group-algebra negations.
-/
instance instNegZCCompletedGroupAlgebra : Neg (ZCCompletedGroupAlgebra C H) where
  neg x := ⟨fun i => -x.1 i, by
    intro i j hij
    rw [map_neg]
    exact congrArg Neg.neg (x.2 i j hij)⟩

/--
Subtraction on the completed group algebra is defined coordinatewise through the finite-stage
group-algebra subtractions.
-/
instance instSubZCCompletedGroupAlgebra : Sub (ZCCompletedGroupAlgebra C H) where
  sub x y := ⟨fun i => x.1 i - y.1 i, by
    intro i j hij
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 i j hij) (y.2 i j hij)⟩

/--
The completed group algebra carries coefficient-ring scalar multiplication by applying the
scalar action at every finite quotient stage.
-/
instance instSMulNatZCCompletedGroupAlgebra : SMul ℕ (ZCCompletedGroupAlgebra C H) where
  smul n x := ⟨fun i => n • x.1 i, by
    intro i j hij
    rw [map_nsmul]
    exact congrArg (n • ·) (x.2 i j hij)⟩

/--
The completed group algebra carries coefficient-ring scalar multiplication by applying the
scalar action at every finite quotient stage.
-/
instance instSMulIntZCCompletedGroupAlgebra : SMul ℤ (ZCCompletedGroupAlgebra C H) where
  smul n x := ⟨fun i => n • x.1 i, by
    intro i j hij
    rw [map_zsmul]
    exact congrArg (n • ·) (x.2 i j hij)⟩

/--
The zero element of \(\mathbb{Z}_C\llbracket H\rrbracket\) is represented by the compatible
family of finite-stage zero elements.
-/
@[simp]
theorem coe_zero_zcCompletedGroupAlgebra :
    ((0 : ZCCompletedGroupAlgebra C H) :
      (i : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H i) = 0 := by
  funext i
  rfl

/--
The underlying finite-stage family of a sum in \(\mathbb{Z}_C\llbracket H\rrbracket\) is the sum
of the underlying finite-stage families.
-/
@[simp]
theorem coe_add_zcCompletedGroupAlgebra (x y : ZCCompletedGroupAlgebra C H) :
    ((x + y : ZCCompletedGroupAlgebra C H) :
      (i : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H i) = x + y := by
  funext i
  rfl

/--
The underlying finite-stage family of a negation in \(\mathbb{Z}_C\llbracket H\rrbracket\) is
the negation of the underlying finite-stage family.
-/
@[simp]
theorem coe_neg_zcCompletedGroupAlgebra (x : ZCCompletedGroupAlgebra C H) :
    ((-x : ZCCompletedGroupAlgebra C H) :
      (i : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H i) = -x := by
  funext i
  rfl

/--
The underlying finite-stage family of a difference in \(\mathbb{Z}_C\llbracket H\rrbracket\) is
the difference of the underlying finite-stage families.
-/
@[simp]
theorem coe_sub_zcCompletedGroupAlgebra (x y : ZCCompletedGroupAlgebra C H) :
    ((x - y : ZCCompletedGroupAlgebra C H) :
      (i : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H i) = x - y := by
  funext i
  rfl

/--
Natural-number scalar multiplication in \(\mathbb{Z}_C\llbracket H\rrbracket\) is computed
coordinatewise at every finite stage.
-/
@[simp]
theorem coe_nsmul_zcCompletedGroupAlgebra (n : ℕ) (x : ZCCompletedGroupAlgebra C H) :
    ((n • x : ZCCompletedGroupAlgebra C H) :
      (i : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H i) = n • x := by
  funext i
  rfl

/--
Integer scalar multiplication in \(\mathbb{Z}_C\llbracket H\rrbracket\) is computed
coordinatewise at every finite stage.
-/
@[simp]
theorem coe_zsmul_zcCompletedGroupAlgebra (n : ℤ) (x : ZCCompletedGroupAlgebra C H) :
    ((n • x : ZCCompletedGroupAlgebra C H) :
      (i : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H i) = n • x := by
  funext i
  rfl

/-- A temporary additive-group structure used while constructing the stronger ring instance. -/
local instance instAddCommGroupZCCompletedGroupAlgebra :
    AddCommGroup (ZCCompletedGroupAlgebra C H) :=
  Function.Injective.addCommGroup
    (fun x : ZCCompletedGroupAlgebra C H =>
      (x : (i : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H i))
    Subtype.val_injective
    (coe_zero_zcCompletedGroupAlgebra (C := C) (H := H))
    (coe_add_zcCompletedGroupAlgebra (C := C) (H := H))
    (coe_neg_zcCompletedGroupAlgebra (C := C) (H := H))
    (coe_sub_zcCompletedGroupAlgebra (C := C) (H := H))
    (fun x n => coe_nsmul_zcCompletedGroupAlgebra (C := C) (H := H) n x)
    (fun x n => coe_zsmul_zcCompletedGroupAlgebra (C := C) (H := H) n x)

/--
The unit of \(\mathbb{Z}_C\llbracket H\rrbracket\) is the compatible family of finite-stage
units.
-/
instance instOneZCCompletedGroupAlgebra : One (ZCCompletedGroupAlgebra C H) where
  one := ⟨fun i => 1, by intro i j hij; exact map_one _⟩

/--
Multiplication on the completed group algebra is defined coordinatewise through the finite-stage
group-algebra products.
-/
instance instMulZCCompletedGroupAlgebra : Mul (ZCCompletedGroupAlgebra C H) where
  mul x y := ⟨fun i => x.1 i * y.1 i, by
    intro i j hij
    rw [map_mul]
    exact congrArg₂ HMul.hMul (x.2 i j hij) (y.2 i j hij)⟩

/--
Natural number casts in \(\mathbb{Z}_C\llbracket H\rrbracket\) are computed coordinatewise from
finite-stage natural number casts.
-/
instance instNatCastZCCompletedGroupAlgebra : NatCast (ZCCompletedGroupAlgebra C H) where
  natCast n := ⟨fun i => n, by intro i j hij; exact map_natCast _ _⟩

/--
Integer casts in \(\mathbb{Z}_C\llbracket H\rrbracket\) are computed coordinatewise from
finite-stage integer casts.
-/
instance instIntCastZCCompletedGroupAlgebra : IntCast (ZCCompletedGroupAlgebra C H) where
  intCast n := ⟨fun i => n, by intro i j hij; exact map_intCast _ _⟩

/-- The completed group algebra has powers computed at every finite-stage coordinate. -/
instance instPowZCCompletedGroupAlgebra : Pow (ZCCompletedGroupAlgebra C H) ℕ where
  pow x n := ⟨fun i => x.1 i ^ n, by
    intro i j hij
    rw [map_pow]
    exact congrArg (fun z => z ^ n) (x.2 i j hij)⟩

/--
The unit of \(\mathbb{Z}_C\llbracket H\rrbracket\) is represented by the compatible family of
finite-stage units.
-/
@[simp]
theorem coe_one_zcCompletedGroupAlgebra :
    ((1 : ZCCompletedGroupAlgebra C H) :
      (i : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H i) = 1 := by
  funext i
  rfl

/--
The underlying finite-stage family of a product in \(\mathbb{Z}_C\llbracket H\rrbracket\) is the
product of the underlying finite-stage families.
-/
@[simp]
theorem coe_mul_zcCompletedGroupAlgebra (x y : ZCCompletedGroupAlgebra C H) :
    ((x * y : ZCCompletedGroupAlgebra C H) :
      (i : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H i) = x * y := by
  funext i
  rfl

/--
Natural number casts in the completed group algebra are computed coefficientwise after
projection to every completed finite quotient stage.
-/
@[simp]
theorem coe_natCast_zcCompletedGroupAlgebra (n : ℕ) :
    ((n : ZCCompletedGroupAlgebra C H) :
      (i : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H i) = n := by
  funext i
  rfl

/--
Integer casts in the completed group algebra are computed coefficientwise after projection to
every completed finite quotient stage.
-/
@[simp]
theorem coe_intCast_zcCompletedGroupAlgebra (n : ℤ) :
    ((n : ZCCompletedGroupAlgebra C H) :
      (i : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H i) = n := by
  funext i
  rfl

/--
Powers in \(\mathbb{Z}_C\llbracket H\rrbracket\) are computed coordinatewise at every finite
stage.
-/
@[simp]
theorem coe_pow_zcCompletedGroupAlgebra (x : ZCCompletedGroupAlgebra C H) (n : ℕ) :
    ((x ^ n : ZCCompletedGroupAlgebra C H) :
      (i : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H i) = x ^ n := by
  funext i
  rfl

/--
The completed group algebra is a ring because all ring operations and ring axioms are inherited
coordinatewise from the finite-stage group algebras.
-/
instance instRingZCCompletedGroupAlgebra : Ring (ZCCompletedGroupAlgebra C H) :=
  Function.Injective.ring
    (fun x : ZCCompletedGroupAlgebra C H =>
      (x : (i : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H i))
    Subtype.val_injective
    (coe_zero_zcCompletedGroupAlgebra (C := C) (H := H))
    (coe_one_zcCompletedGroupAlgebra (C := C) (H := H))
    (coe_add_zcCompletedGroupAlgebra (C := C) (H := H))
    (coe_mul_zcCompletedGroupAlgebra (C := C) (H := H))
    (coe_neg_zcCompletedGroupAlgebra (C := C) (H := H))
    (coe_sub_zcCompletedGroupAlgebra (C := C) (H := H))
    (fun n x => coe_nsmul_zcCompletedGroupAlgebra (C := C) (H := H) n x)
    (fun n x => coe_zsmul_zcCompletedGroupAlgebra (C := C) (H := H) n x)
    (fun x n => coe_pow_zcCompletedGroupAlgebra (C := C) (H := H) x n)
    (by intro n; exact coe_natCast_zcCompletedGroupAlgebra (C := C) (H := H) n)
    (by intro z; exact coe_intCast_zcCompletedGroupAlgebra (C := C) (H := H) z)

/-- The finite-stage projection sends \(1\) to \(1\). -/
@[simp]
theorem zcCompletedGroupAlgebraProjection_one
    (i : ZCCompletedGroupAlgebraIndex C H) :
    zcCompletedGroupAlgebraProjection C H i (1 : ZCCompletedGroupAlgebra C H) = 1 :=
  rfl

/-- The finite-stage projection preserves multiplication. -/
@[simp]
theorem zcCompletedGroupAlgebraProjection_mul
    (i : ZCCompletedGroupAlgebraIndex C H) (x y : ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraProjection C H i (x * y) =
      zcCompletedGroupAlgebraProjection C H i x *
        zcCompletedGroupAlgebraProjection C H i y :=
  rfl

/-- The finite-stage projection sends \(0\) to \(0\). -/
@[simp]
theorem zcCompletedGroupAlgebraProjection_zero
    (i : ZCCompletedGroupAlgebraIndex C H) :
    zcCompletedGroupAlgebraProjection C H i (0 : ZCCompletedGroupAlgebra C H) = 0 :=
  rfl

/-- The finite-stage projection preserves addition. -/
@[simp]
theorem zcCompletedGroupAlgebraProjection_add
    (i : ZCCompletedGroupAlgebraIndex C H) (x y : ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraProjection C H i (x + y) =
      zcCompletedGroupAlgebraProjection C H i x +
        zcCompletedGroupAlgebraProjection C H i y :=
  rfl

/-- The finite-stage projection preserves negation. -/
@[simp]
theorem zcCompletedGroupAlgebraProjection_neg
    (i : ZCCompletedGroupAlgebraIndex C H) (x : ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraProjection C H i (-x) =
      -zcCompletedGroupAlgebraProjection C H i x :=
  rfl

/-- The finite-stage projection preserves subtraction. -/
@[simp]
theorem zcCompletedGroupAlgebraProjection_sub
    (i : ZCCompletedGroupAlgebraIndex C H) (x y : ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraProjection C H i (x - y) =
      zcCompletedGroupAlgebraProjection C H i x -
        zcCompletedGroupAlgebraProjection C H i y :=
  rfl

/--
The projection from \(\mathbb{Z}_C\llbracket H\rrbracket\) to a finite stage is bundled as a
ring homomorphism.
-/
def zcCompletedGroupAlgebraProjectionRingHom
    (i : ZCCompletedGroupAlgebraIndex C H) :
    ZCCompletedGroupAlgebra C H →+* ZCCompletedGroupAlgebraStage C H i where
  toFun := zcCompletedGroupAlgebraProjection C H i
  map_zero' := zcCompletedGroupAlgebraProjection_zero C H i
  map_one' := zcCompletedGroupAlgebraProjection_one C H i
  map_add' := zcCompletedGroupAlgebraProjection_add C H i
  map_mul' := zcCompletedGroupAlgebraProjection_mul C H i

/--
The ring-homomorphism projection has the same underlying coordinate map as the finite-stage
projection.
-/
@[simp]
theorem zcCompletedGroupAlgebraProjectionRingHom_apply
    (i : ZCCompletedGroupAlgebraIndex C H) (x : ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraProjectionRingHom C H i x =
      zcCompletedGroupAlgebraProjection C H i x :=
  rfl

/-- The \(\mathbb{Z}_C\)-completed group algebra stage is a module over its coefficient ring. -/
instance instModuleZCCompletedGroupAlgebraStage
    (i : ZCCompletedGroupAlgebraIndex C H) :
    Module (ZCCompletedGroupAlgebra C H) (ZCCompletedGroupAlgebraStage C H i) :=
  Module.compHom _ (zcCompletedGroupAlgebraProjectionRingHom C H i)

/-- Finite-stage projections separate points of \(\mathbb{Z}_C\llbracket H\rrbracket\). -/
theorem zcCompletedGroupAlgebraProjection_ext
    {x y : ZCCompletedGroupAlgebra C H}
    (h : ∀ i : ZCCompletedGroupAlgebraIndex C H,
      zcCompletedGroupAlgebraProjection C H i x =
        zcCompletedGroupAlgebraProjection C H i y) :
    x = y := by
  apply Subtype.ext
  funext i
  exact h i

/--
Finite projections from \(\mathbb{Z}_C\llbracket H\rrbracket\) commute with the finite
transition maps.
-/
@[simp]
theorem zcCompletedGroupAlgebraTransition_projection
    {i j : ZCCompletedGroupAlgebraIndex C H} (hij : i ≤ j)
    (x : ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraTransition C H hij
        (zcCompletedGroupAlgebraProjection C H j x) =
      zcCompletedGroupAlgebraProjection C H i x :=
  x.2 i j hij

/-- A finite stage projection as a linear map over the completed group algebra. -/
def zcCompletedGroupAlgebraProjectionLinearMap
    (i : ZCCompletedGroupAlgebraIndex C H) :
    ZCCompletedGroupAlgebra C H →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedGroupAlgebraStage C H i where
  toFun := zcCompletedGroupAlgebraProjection C H i
  map_add' x y := zcCompletedGroupAlgebraProjection_add C H i x y
  map_smul' r x := by
    change zcCompletedGroupAlgebraProjection C H i (r * x) =
      zcCompletedGroupAlgebraProjection C H i r *
        zcCompletedGroupAlgebraProjection C H i x
    exact zcCompletedGroupAlgebraProjection_mul C H i r x

/--
The \(\mathbb{Z}_C\)-completed group-algebra projection, bundled as a linear map, acts by its
defining finite-stage coordinate formula.
-/
@[simp]
theorem zcCompletedGroupAlgebraProjectionLinearMap_apply
    (i : ZCCompletedGroupAlgebraIndex C H) (x : ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraProjectionLinearMap C H i x =
      zcCompletedGroupAlgebraProjection C H i x :=
  rfl

end Ring

/--
The projection from \(\mathbb{Z}_C\llbracket H\rrbracket\) to a finite stage commutes with
finite sums.
-/
theorem zcCompletedGroupAlgebraProjection_sum
    (C : ProCGroups.FiniteGroupClass.{u})
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {I : Type v} [Fintype I]
    (j : ZCCompletedGroupAlgebraIndex C H)
    (f : I → ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraProjection C H j (∑ i : I, f i) =
      ∑ i : I, zcCompletedGroupAlgebraProjection C H j (f i) := by
  classical
  refine Finset.induction_on (s := Finset.univ) ?_ ?_
  · rfl
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has]
    rw [zcCompletedGroupAlgebraProjection_add, ih]

/--
The coefficient element of \(\mathbb{Z}_C\llbracket H\rrbracket\) supported at the identity of
\(H\).
-/
def zcCompletedGroupAlgebraCoeff
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (a : ZCCoeff C) : ZCCompletedGroupAlgebra C H :=
  ⟨fun i =>
      MonoidAlgebra.single
        (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
        (proCIntegerProj (C := C) i.1 a), by
    intro i j hij
    let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
    let : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
    have ha : modNCompletedCoeffMap (n := i.1.modulus) (m := j.1.modulus) hij.1
        (proCIntegerProj (C := C) j.1 a) =
        proCIntegerProj (C := C) i.1 a :=
      proCIntegerProj_transition (C := C) hij.1 a
    have hmap :
        (OpenNormalSubgroupInClass.map
          (C := C) (G := H)
          (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2)
            (1 : CompletedGroupAlgebraQuotientInClass H C j.2) =
          (1 : CompletedGroupAlgebraQuotientInClass H C i.2) :=
      map_one _
    rw [zcCompletedGroupAlgebraTransition_single C H hij, hmap, ha]
    rfl⟩

/--
Coefficient change is performed stagewise: supports are unchanged and coefficients are
transported by the given ring homomorphism.
-/
def zcCompletedGroupAlgebraCoeffMap
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    ZCCoeff C →+* ZCCompletedGroupAlgebra C H where
  toFun := zcCompletedGroupAlgebraCoeff C H
  map_zero' := by
    apply Subtype.ext
    funext i
    change
      MonoidAlgebra.single
          (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
          (proCIntegerProj (C := C) i.1 0) = 0
    rw [proCIntegerProj_zero, MonoidAlgebra.single_zero]
  map_one' := by
    apply Subtype.ext
    funext i
    let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
    change
      MonoidAlgebra.single
          (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
          (proCIntegerProj (C := C) i.1 1) = 1
    rw [proCIntegerProj_one, ← MonoidAlgebra.one_def]
  map_add' a b := by
    apply Subtype.ext
    funext i
    change
      MonoidAlgebra.single
          (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
          (proCIntegerProj (C := C) i.1 (a + b)) =
        MonoidAlgebra.single
            (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
            (proCIntegerProj (C := C) i.1 a) +
          MonoidAlgebra.single
            (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
            (proCIntegerProj (C := C) i.1 b)
    rw [proCIntegerProj_add, MonoidAlgebra.single_add]
  map_mul' a b := by
    apply Subtype.ext
    funext i
    let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
    change MonoidAlgebra.single
        (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
        (proCIntegerProj (C := C) i.1 (a * b)) =
      MonoidAlgebra.single
        (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
        (proCIntegerProj (C := C) i.1 a) *
      MonoidAlgebra.single
        (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
        (proCIntegerProj (C := C) i.1 b)
    simp only [proCIntegerProj_mul, MonoidAlgebra.single_mul_single, mul_one]

/--
The completed group-algebra projection commutes with the coefficient-change map at the
corresponding finite stage.
-/
@[simp]
theorem zcCompletedGroupAlgebraProjection_coeffMap
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (i : ZCCompletedGroupAlgebraIndex C H) (a : ZCCoeff C) :
    zcCompletedGroupAlgebraProjection C H i
        (zcCompletedGroupAlgebraCoeffMap C H a) =
      MonoidAlgebra.single
        (1 : CompletedGroupAlgebraQuotientInClass H C i.2)
        (proCIntegerProj (C := C) i.1 a) :=
  rfl

/-- The group-like map \(H \to \mathbb{Z}_C\llbracket H\rrbracket\). -/
def zcGroupLike
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    H →* ZCCompletedGroupAlgebra C H where
  toFun h := ⟨fun i =>
      MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass H C i.2) (QuotientGroup.mk h), by
    intro i j hij
    change
      zcCompletedGroupAlgebraTransition C H hij
          (MonoidAlgebra.of (ModNCompletedCoeff j.1.modulus)
            (CompletedGroupAlgebraQuotientInClass H C j.2) (QuotientGroup.mk h)) =
        MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H C i.2) (QuotientGroup.mk h)
    exact zcCompletedGroupAlgebraTransition_of C H hij
      (QuotientGroup.mk h : CompletedGroupAlgebraQuotientInClass H C j.2)⟩
  map_one' := by
    apply Subtype.ext
    funext i
    change
      MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H C i.2)
          (1 : CompletedGroupAlgebraQuotientInClass H C i.2) = 1
    exact map_one
      (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass H C i.2))
  map_mul' h₁ h₂ := by
    apply Subtype.ext
    funext i
    change
      MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H C i.2) (QuotientGroup.mk (h₁ * h₂)) =
        MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass H C i.2) (QuotientGroup.mk h₁) *
          MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass H C i.2) (QuotientGroup.mk h₂)
    change
      MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H C i.2)
          ((QuotientGroup.mk h₁ :
            CompletedGroupAlgebraQuotientInClass H C i.2) *
            (QuotientGroup.mk h₂ :
              CompletedGroupAlgebraQuotientInClass H C i.2)) =
        MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass H C i.2)
            (QuotientGroup.mk h₁) *
          MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass H C i.2)
            (QuotientGroup.mk h₂)
    exact map_mul
      (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass H C i.2)) _ _

/--
Projecting a group-like element of \(\mathbb{Z}_C\llbracket H\rrbracket\) gives its finite-stage
group-like image.
-/
@[simp]
theorem zcCompletedGroupAlgebraProjection_groupLike
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (i : ZCCompletedGroupAlgebraIndex C H) (h : H) :
    zcCompletedGroupAlgebraProjection C H i (zcGroupLike C H h) =
      MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass H C i.2) (QuotientGroup.mk h) :=
  rfl

/--
The projection ring homomorphism sends a group-like element to its image in the corresponding
finite group-algebra stage.
-/
@[simp]
theorem zcCompletedGroupAlgebraProjectionRingHom_groupLike
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (i : ZCCompletedGroupAlgebraIndex C H) (h : H) :
    zcCompletedGroupAlgebraProjectionRingHom C H i (zcGroupLike C H h) =
      MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass H C i.2) (QuotientGroup.mk h) :=
  zcCompletedGroupAlgebraProjection_groupLike C H i h

/-- A completed group-algebra relation \((h - 1)y = 0\) descends to every finite stage. -/
theorem zcCompletedGroupAlgebra_projection_sub_one_mul_eq_zero
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (h : H) (y : ZCCompletedGroupAlgebra C H)
    (i : ZCCompletedGroupAlgebraIndex C H)
    (hrel : (zcGroupLike C H h - 1) * y = 0) :
    (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass H C i.2)
        (QuotientGroup.mk h) - 1) *
      zcCompletedGroupAlgebraProjection C H i y = 0 := by
  have hproj :=
    congrArg (zcCompletedGroupAlgebraProjection C H i) hrel
  simpa only [zcCompletedGroupAlgebraProjection_mul,
    zcCompletedGroupAlgebraProjection_sub,
    zcCompletedGroupAlgebraProjection_groupLike,
    zcCompletedGroupAlgebraProjection_one,
    zcCompletedGroupAlgebraProjection_zero] using hproj

/-- Integer-power version of finite-stage descent for \((h^n - 1)y = 0\). -/
theorem zcCompletedGroupAlgebra_projection_zpow_sub_one_mul_eq_zero
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (h : H) (n : ℤ) (y : ZCCompletedGroupAlgebra C H)
    (i : ZCCompletedGroupAlgebraIndex C H)
    (hrel : (zcGroupLike C H (h ^ n) - 1) * y = 0) :
    (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
        (CompletedGroupAlgebraQuotientInClass H C i.2)
        ((QuotientGroup.mk h : CompletedGroupAlgebraQuotientInClass H C i.2) ^ n) -
        1) *
      zcCompletedGroupAlgebraProjection C H i y = 0 := by
  have hstage :=
    zcCompletedGroupAlgebra_projection_sub_one_mul_eq_zero
      C H (h ^ n) y i hrel
  rw [QuotientGroup.mk_zpow] at hstage
  exact hstage

/--
A \(\mathbb{Z}_C\llbracket H\rrbracket\) transition with unchanged coefficient modulus is just
the quotient map on the finite group-algebra domain.
-/
theorem zcCompletedGroupAlgebraTransition_sameCoeff
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (coeff : ProCIntegerIndex C)
    {U V : OpenNormalSubgroupInClass C H}
    (hUV : (V.1 : Subgroup H) ≤ (U.1 : Subgroup H)) :
    zcCompletedGroupAlgebraTransition C H
        (i := (coeff, OrderDual.toDual U))
        (j := (coeff, OrderDual.toDual V))
        (show (coeff, OrderDual.toDual U) ≤ (coeff, OrderDual.toDual V) from
          ⟨dvd_rfl, hUV⟩) =
      MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff coeff.modulus)
        (OpenNormalSubgroupInClass.map
          (C := C) (G := H) (U := U) (V := V) hUV) := by
  let : Fact (0 < coeff.modulus) := ⟨coeff.positive⟩
  rw [zcCompletedGroupAlgebraTransition,
    modNCompletedGroupAlgebraStageCoeffMapInClass_rfl]
  simp only [RingHomCompTriple.comp_eq]
  unfold modNCompletedGroupAlgebraTransitionInClass
  rfl

/--
After coefficient change, projection of multiplication by a group-like element is computed in
the corresponding finite group-algebra stage.
-/
@[simp]
theorem zcCompletedGroupAlgebraProjection_coeffMap_mul_groupLike
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (i : ZCCompletedGroupAlgebraIndex C H) (a : ZCCoeff C) (h : H) :
    zcCompletedGroupAlgebraProjection C H i
        (zcCompletedGroupAlgebraCoeffMap C H a * zcGroupLike C H h) =
      MonoidAlgebra.single
        (QuotientGroup.mk h : CompletedGroupAlgebraQuotientInClass H C i.2)
        (proCIntegerProj (C := C) i.1 a) := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  erw [zcCompletedGroupAlgebraProjection_mul,
    zcCompletedGroupAlgebraProjection_coeffMap,
    zcCompletedGroupAlgebraProjection_groupLike,
    MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  rw [mul_one]
  congr 1
  exact one_mul _

/-- Every finite-stage projection from the pro-\(C\) completed group algebra is surjective. -/
theorem zcCompletedGroupAlgebraProjection_surjective
    (C : ProCGroups.FiniteGroupClass.{u})
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (i : ZCCompletedGroupAlgebraIndex C H) :
    Function.Surjective (zcCompletedGroupAlgebraProjection C H i) := by
  classical
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  let : DecidableEq (CompletedGroupAlgebraQuotientInClass H C i.2) := Classical.decEq _
  intro x
  induction x using MonoidAlgebra.induction with
  | zero =>
      exact ⟨0, by simp only [zcCompletedGroupAlgebraProjection_zero]⟩
  | @single_add q a x hq hx ih =>
      rcases ih with ⟨y, hy⟩
      rcases QuotientGroup.mk'_surjective
          ((((OrderDual.ofDual i.2).1 : OpenNormalSubgroup H) : Subgroup H)) q with
        ⟨h, rfl⟩
      rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
      let aLift : ZCCoeff C := (t : ProCIntegerLimitCarrier C)
      refine ⟨zcCompletedGroupAlgebraCoeffMap C H aLift * zcGroupLike C H h + y, ?_⟩
      rw [zcCompletedGroupAlgebraProjection_add,
        zcCompletedGroupAlgebraProjection_coeffMap_mul_groupLike, hy]
      simp only [proCIntegerProj_intCast, QuotientGroup.mk'_apply, aLift]
      rfl

section Basic

variable (C : ProCGroups.FiniteGroupClass.{v})
variable {G : Type u} [Group G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The completed coefficient homomorphism \(G \to \mathbb{Z}_C\llbracket H\rrbracket\) induced by
\(\psi: G \to H\).
-/
def zcCompletedGroupAlgebraScalar (ψ : G →* H) :
    G →* ZCCompletedGroupAlgebra C H :=
  (zcGroupLike C H).comp ψ

/--
The completed group-algebra scalar associated to `g` is the group-like element determined by `ψ g`.
-/
@[simp]
theorem zcCompletedGroupAlgebraScalar_apply (ψ : G →* H) (g : G) :
    zcCompletedGroupAlgebraScalar C ψ g = zcGroupLike C H (ψ g) :=
  rfl

/--
If \(g\in\ker \psi\), then the completed coefficient homomorphism induced by \(\psi\) sends
\(g\) to the unit element.
-/
@[simp]
theorem zcCompletedGroupAlgebraScalar_subtype_ker (ψ : G →* H) (g : ψ.ker) :
    zcCompletedGroupAlgebraScalar C ψ g = 1 := by
  rw [zcCompletedGroupAlgebraScalar_apply, g.2, map_one]

/--
The algebraic universal \(\mathbb{Z}_C\llbracket H\rrbracket\) differential module attached to
\(\psi : G \to H\). It is the \(\mathbb{Z}_C\llbracket H\rrbracket\)-module generated by the
symbols dg, subject to the Leibniz relations \(d(gh)=dg+\) \([\psi(g)]\) dh, i.e. the quotient
by the raw crossed-differential relation submodule. The final profinite Crowell middle term is
the separated finite-stage quotient \(\mathbb{Z}_C\)-separated completed differential module,
not this algebraic quotient.
-/
abbrev ZCCompletedDifferentialModule (ψ : G →* H) : Type _ :=
  CrossedDifferentialModule (zcCompletedGroupAlgebraScalar C ψ)

/-- The universal completed crossed differential, bundled with its Fox--Leibniz law. -/
def zcUniversalDifferential (ψ : G →* H) :
    ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCCompletedDifferentialModule C ψ) :=
  universalCrossedHom (zcCompletedGroupAlgebraScalar C ψ)

/-- The completed Fox boundary \(g \mapsto [\psi(g)] - 1\), bundled with its
Fox--Leibniz law. -/
def zcCompletedGroupAlgebraBoundary (ψ : G →* H) :
    ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCCompletedGroupAlgebra C H) where
  toFun g := zcGroupLike C H (ψ g) - 1
  map_mul' g h := by
    simp only [scalarCrossedAction_apply, map_mul, sub_eq_add_neg, add_comm,
      zcCompletedGroupAlgebraScalar_apply, smul_eq_mul, mul_add, mul_neg,
      mul_one, add_assoc, add_neg_cancel_comm_assoc]

/-- The completed Fox boundary vanishes on elements in the kernel of the target map. -/
@[simp]
theorem zcCompletedGroupAlgebraBoundary_eq_zero_of_mem_ker
    (ψ : G →* H) {g : G} (hg : ψ g = 1) :
    zcCompletedGroupAlgebraBoundary C ψ g = 0 := by
  change zcGroupLike C H (ψ g) - 1 = 0
  rw [hg, map_one]
  simp only [sub_self]

/-- The completed Fox boundary restricted to the kernel subgroup is zero. -/
@[simp]
theorem zcCompletedGroupAlgebraBoundary_subtype_ker
    (ψ : G →* H) (g : ψ.ker) :
    zcCompletedGroupAlgebraBoundary C ψ g = 0 :=
  zcCompletedGroupAlgebraBoundary_eq_zero_of_mem_ker (C := C) (ψ := ψ) g.2

section UniversalProperty

variable {A : Type*} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]

/--
The universal \(\mathbb{Z}_C\llbracket H\rrbracket\)-linear map from the completed
crossed-differential module to the completed group algebra is induced by the completed Fox
boundary \(g\mapsto [\psi(g)]-1\).
-/
def zcToCompletedGroupAlgebra (ψ : G →* H) :
    ZCCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedGroupAlgebra C H :=
  crossedHomModuleLift (A := ZCCompletedGroupAlgebra C H)
    (zcCompletedGroupAlgebraScalar C ψ) (zcCompletedGroupAlgebraBoundary C ψ)

/--
The universal map to the completed group algebra sends the universal differential of \(g\) to
the completed Fox boundary \([\psi(g)]-1\).
-/
@[simp]
theorem zcToCompletedGroupAlgebra_universal (ψ : G →* H) (g : G) :
    zcToCompletedGroupAlgebra C ψ (zcUniversalDifferential C ψ g) =
      zcCompletedGroupAlgebraBoundary C ψ g :=
  crossedHomModuleLift_universal
    (A := ZCCompletedGroupAlgebra C H) (zcCompletedGroupAlgebraScalar C ψ)
    (zcCompletedGroupAlgebraBoundary C ψ) g

/--
There is a unique \(\mathbb{Z}_C\llbracket H\rrbracket\)-linear map from the completed
crossed-differential module to the completed group algebra that sends every universal
differential to the corresponding completed Fox boundary.
-/
theorem existsUnique_zcToCompletedGroupAlgebra (ψ : G →* H) :
    ∃! f :
        ZCCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H]
          ZCCompletedGroupAlgebra C H,
      ∀ g, f (zcUniversalDifferential C ψ g) =
        zcCompletedGroupAlgebraBoundary C ψ g :=
  existsUnique_crossedHomModuleLift
    (A := ZCCompletedGroupAlgebra C H) (zcCompletedGroupAlgebraScalar C ψ)
    (zcCompletedGroupAlgebraBoundary C ψ)

end UniversalProperty

section SourceNaturality

variable {G' : Type u} [Group G']

/--
Source functoriality for the completed universal differential module. For a homomorphism \(f:G
\to G'\), the universal crossed differential attached to \(\psi'\circ f\) maps to the one
attached to \(\psi'\) by sending \(dg\) to \(d(f(g))\).
-/
def zcCompletedDifferentialModuleSourceMap
    (ψ' : G' →* H) (f : G →* G') :
    ZCCompletedDifferentialModule C (ψ'.comp f) →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedDifferentialModule C ψ' :=
  crossedHomModuleLift (A := ZCCompletedDifferentialModule C ψ')
    (zcCompletedGroupAlgebraScalar C (ψ'.comp f))
    { toFun := fun g => zcUniversalDifferential C ψ' (f g)
      map_mul' := by
        intro g h
        change zcUniversalDifferential C ψ' (f (g * h)) =
          zcUniversalDifferential C ψ' (f g) +
            zcCompletedGroupAlgebraScalar C (ψ'.comp f) g •
              zcUniversalDifferential C ψ' (f h)
        rw [map_mul, ScalarCrossedHom.map_mul (zcUniversalDifferential C ψ')]
        rfl }

/--
The universal source map on the completed differential module is determined by the source
quotient maps at finite stages.
-/
@[simp]
theorem zcCompletedDifferentialModuleSourceMap_universal
    (ψ' : G' →* H) (f : G →* G') (g : G) :
    zcCompletedDifferentialModuleSourceMap (C := C) ψ' f
        (zcUniversalDifferential C (ψ'.comp f) g) =
      zcUniversalDifferential C ψ' (f g) :=
  crossedHomModuleLift_universal
    (A := ZCCompletedDifferentialModule C ψ')
    (zcCompletedGroupAlgebraScalar C (ψ'.comp f))
    { toFun := fun g => zcUniversalDifferential C ψ' (f g)
      map_mul' := by
        intro g h
        change zcUniversalDifferential C ψ' (f (g * h)) =
          zcUniversalDifferential C ψ' (f g) +
            zcCompletedGroupAlgebraScalar C (ψ'.comp f) g •
              zcUniversalDifferential C ψ' (f h)
        rw [map_mul, ScalarCrossedHom.map_mul (zcUniversalDifferential C ψ')]
        rfl } g

/-- Completed universal zero descends along a source homomorphism. -/
theorem zcUniversalDifferential_eq_zero_of_source
    (ψ' : G' →* H) (f : G →* G') {g : G}
    (hg : zcUniversalDifferential C (ψ'.comp f) g = 0) :
    zcUniversalDifferential C ψ' (f g) = 0 := by
  rw [← zcCompletedDifferentialModuleSourceMap_universal (C := C) ψ' f g, hg, map_zero]

end SourceNaturality

section UniversalZero

variable {A : Type*} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]

/--
A zero universal differential is killed by every crossed differential represented by the
completed universal module.
-/
theorem crossedDifferential_eq_zero_of_zcUniversalDifferential_eq_zero
    (ψ : G →* H)
    (D : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ) A)
    {g : G} (hg : zcUniversalDifferential C ψ g = 0) :
    D g = 0 := by
  change
    universalCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) g = 0 at hg
  rw [← crossedHomModuleLift_universal
    (A := A) (zcCompletedGroupAlgebraScalar C ψ) D g, hg, map_zero]

end UniversalZero

end Basic

end

end FoxDifferential
