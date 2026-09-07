import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.GroupTheory.SemidirectProduct

set_option autoImplicit false

/-!
# Bundled crossed homomorphisms

This module defines crossed homomorphisms for an additive group action and their scalar-character
specialization.  It supplies the Fox product, inverse, conjugation, commutator, and power rules;
restriction to coefficient-trivial subgroups; linear pushforward and group-homomorphism pullback;
the standard semidirect-product representation; and the additive-group structure on the space of
crossed homomorphisms.

`CrossedHom` and `ScalarCrossedHom` are the only crossed-differential representations exposed by
this module.  The former parallel raw-function predicate and its conversion layer have been
removed, so downstream APIs operate on the bundled maps directly.
-/

namespace FoxDifferential

open scoped BigOperators commutatorElement

/-- Scalar multiplication by a character `coeff : G →* R`, expressed as an additive action.

Because `G` is a group, every `coeff g` is automatically a unit; `toHomUnits` records that fact
and produces actual additive automorphisms rather than mere additive endomorphisms. -/
def scalarCrossedAction
    {R G A : Type*} [Semiring R] [Group G] [AddCommGroup A] [Module R A]
    (coeff : G →* R) : G →* Multiplicative (AddAut A) :=
  (DistribMulAction.toAddAut Rˣ A).comp coeff.toHomUnits

/-- The action induced by a scalar character evaluates as scalar multiplication. -/
@[simp]
theorem scalarCrossedAction_apply
    {R G A : Type*} [Semiring R] [Group G] [AddCommGroup A] [Module R A]
    (coeff : G →* R) (g : G) (a : A) :
    scalarCrossedAction (A := A) coeff g a = coeff g • a :=
  rfl

/-- Convert an additive action to the multiplicative action used by Mathlib's standard
`SemidirectProduct`. -/
def crossedSemidirectMulAction
    {G A : Type*} [Group G] [AddCommGroup A]
    (action : G →* Multiplicative (AddAut A)) : G →* MulAut (Multiplicative A) :=
  (MulAutMultiplicative A).symm.toMonoidHom.comp action

/-- The standard Mathlib semidirect product attached to an additive action. -/
abbrev CrossedSemidirectProduct
    {G A : Type*} [Group G] [AddCommGroup A]
    (action : G →* Multiplicative (AddAut A)) :=
  SemidirectProduct (Multiplicative A) G (crossedSemidirectMulAction action)

/-- The multiplicative form of an additive action agrees with the original action on elements. -/
@[simp]
theorem crossedSemidirectMulAction_apply
    {G A : Type*} [Group G] [AddCommGroup A]
    (action : G →* Multiplicative (AddAut A)) (g : G) (a : A) :
    crossedSemidirectMulAction action g (Multiplicative.ofAdd a) =
      Multiplicative.ofAdd (action g a) :=
  rfl

/-- Read the multiplicative presentation of the action back in the original additive group. -/
@[simp]
theorem crossedSemidirectMulAction_toAdd
    {G A : Type*} [Group G] [AddCommGroup A]
    (action : G →* Multiplicative (AddAut A)) (g : G) (a : Multiplicative A) :
    Multiplicative.toAdd (crossedSemidirectMulAction action g a) =
      action g (Multiplicative.toAdd a) :=
  rfl

/-- A crossed homomorphism bundled with its acting representation and Fox--Leibniz law. -/
structure CrossedHom
    {G A : Type*} [Group G] [AddCommGroup A]
    (action : G →* Multiplicative (AddAut A)) where
  /-- The function from the source group to the additive target. -/
  toFun : G → A
  /-- The crossed-homomorphism law with respect to the specified action. -/
  map_mul' : ∀ g h, toFun (g * h) = toFun g + action g (toFun h)

/-- Scalar-character crossed homomorphisms are a specialization of general crossed
homomorphisms for the action `scalarCrossedAction coeff`. -/
abbrev ScalarCrossedHom
    {R G : Type*} [Semiring R] [Group G]
    (coeff : G →* R) (A : Type*) [AddCommGroup A] [Module R A] :=
  CrossedHom (scalarCrossedAction (A := A) coeff)

namespace CrossedHom

variable {G A : Type*} [Group G] [AddCommGroup A]
variable {action : G →* Multiplicative (AddAut A)}

/-- Crossed homomorphisms coerce to their underlying functions. -/
instance instFunLike : FunLike (CrossedHom action) G A where
  coe := CrossedHom.toFun
  coe_injective f g h := by
    cases f
    cases g
    simp_all

/-- The underlying function of a crossed homomorphism agrees with its coercion to a function. -/
@[simp]
theorem toFun_apply (d : CrossedHom action) (g : G) : d.toFun g = d g := rfl

/-- Equality of crossed homomorphisms is pointwise equality. -/
@[ext]
theorem ext {d e : CrossedHom action} (h : ∀ g, d g = e g) : d = e := by
  apply DFunLike.ext d e
  exact h

/-- The bundled Fox--Leibniz rule for a general additive action. -/
@[simp]
theorem map_mul (d : CrossedHom action) (g h : G) :
    d (g * h) = d g + action g (d h) :=
  d.map_mul' g h

/-- A crossed homomorphism vanishes at the identity. -/
@[simp]
theorem map_one (d : CrossedHom action) : d 1 = 0 := by
  have h := d.map_mul 1 1
  have hmul : d 1 = d 1 + d 1 := by
    simpa only [one_mul, action.map_one, toAdd_one, AddAut.zero_apply] using h
  have h' := congrArg (fun z : A => z - d 1) hmul
  have hzero : 0 = d 1 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
  exact hzero.symm

/-- Inverse rule for a crossed homomorphism. -/
theorem map_inv (d : CrossedHom action) (g : G) :
    d g⁻¹ = -(action g⁻¹ (d g)) := by
  have h := d.map_mul g⁻¹ g
  rw [inv_mul_cancel, map_one] at h
  rw [eq_neg_iff_add_eq_zero]
  exact h.symm

/-- Formula for multiplying by an inverse on the left. -/
theorem map_inv_mul (d : CrossedHom action) (g h : G) :
    d (g⁻¹ * h) = -(action g⁻¹ (d g)) + action g⁻¹ (d h) := by
  rw [d.map_mul, d.map_inv]

/-- Formula for multiplying by an inverse on the right. -/
theorem map_mul_inv (d : CrossedHom action) (g h : G) :
    d (g * h⁻¹) = d g - action (g * h⁻¹) (d h) := by
  rw [d.map_mul, d.map_inv]
  simp only [map_neg, sub_eq_add_neg, ← AddAut.add_apply]
  rw [← toAdd_mul, ← action.map_mul]

/-- Division rule for a crossed homomorphism. -/
theorem map_div (d : CrossedHom action) (g h : G) :
    d (g / h) = d g - action (g / h) (d h) := by
  simpa [div_eq_mul_inv] using d.map_mul_inv g h

/-- Conjugation rule for a crossed homomorphism. -/
theorem map_conj (d : CrossedHom action) (g h : G) :
    d (g * h * g⁻¹) =
      d g + action g (d h) - action (g * h * g⁻¹) (d g) := by
  rw [d.map_mul_inv (g * h) g, d.map_mul g h]

/-- Commutator rule for a crossed homomorphism. -/
theorem map_commutator (d : CrossedHom action) (g h : G) :
    d ⁅g, h⁆ =
      d g + action g (d h) - action (g * h * g⁻¹) (d g) -
        action ⁅g, h⁆ (d h) := by
  rw [commutatorElement_def, d.map_mul_inv (g * h * g⁻¹) h, d.map_conj g h]

/-- Positive-power rule for a crossed homomorphism. -/
theorem map_pow (d : CrossedHom action) (g : G) (n : ℕ) :
    d (g ^ n) = (Finset.range n).sum (fun k => action (g ^ k) (d g)) := by
  induction n with
  | zero => simp only [pow_zero, map_one, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
      rw [pow_succ, d.map_mul, ih, Finset.sum_range_succ]

/-- The graph of a crossed homomorphism is an ordinary homomorphism into the standard
semidirect product. -/
def toSemidirectMonoidHom (d : CrossedHom action) :
    G →* CrossedSemidirectProduct action where
  toFun g := ⟨Multiplicative.ofAdd (d g), g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · change d 1 = 0
      exact d.map_one
    · rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · change d (g * h) = d g + action g (d h)
      exact d.map_mul g h
    · rfl

/-- The left component of the semidirect-product graph is the value of the crossed homomorphism. -/
@[simp]
theorem toSemidirectMonoidHom_left (d : CrossedHom action) (g : G) :
    Multiplicative.toAdd (d.toSemidirectMonoidHom g).left = d g :=
  rfl

/-- The right component of the semidirect-product graph is the original group element. -/
@[simp]
theorem toSemidirectMonoidHom_right (d : CrossedHom action) (g : G) :
    (d.toSemidirectMonoidHom g).right = g :=
  rfl

/-- Recover a crossed homomorphism from a semidirect-product homomorphism whose right component
is the identity. -/
def ofSemidirectMonoidHom
    (f : G →* CrossedSemidirectProduct action)
    (hright : ∀ g, (f g).right = g) : CrossedHom action where
  toFun g := Multiplicative.toAdd (f g).left
  map_mul' := by
    intro g h
    have hleft := congrArg SemidirectProduct.left (f.map_mul g h)
    rw [SemidirectProduct.mul_left] at hleft
    have hleftAdd := congrArg Multiplicative.toAdd hleft
    simpa only [toAdd_mul, crossedSemidirectMulAction_toAdd, hright] using hleftAdd

/-- Recovering a crossed homomorphism takes the additive form of the graph's left component. -/
@[simp]
theorem ofSemidirectMonoidHom_apply
    (f : G →* CrossedSemidirectProduct action)
    (hright : ∀ g, (f g).right = g) (g : G) :
    ofSemidirectMonoidHom f hright g = Multiplicative.toAdd (f g).left :=
  rfl

/-- Recovering a crossed homomorphism from its semidirect-product graph returns the original map. -/
@[simp]
theorem ofSemidirectMonoidHom_toSemidirectMonoidHom (d : CrossedHom action) :
    ofSemidirectMonoidHom d.toSemidirectMonoidHom
      (fun g => toSemidirectMonoidHom_right d g) = d := by
  apply CrossedHom.ext
  intro g
  rfl

/-- The graph construction loses no information: a semidirect-product homomorphism over the
identity is exactly the graph of the crossed homomorphism obtained from its left component. -/
theorem toSemidirectMonoidHom_ofSemidirectMonoidHom
    (f : G →* CrossedSemidirectProduct action)
    (hright : ∀ g, (f g).right = g) :
    (ofSemidirectMonoidHom f hright).toSemidirectMonoidHom = f := by
  apply MonoidHom.ext
  intro g
  apply SemidirectProduct.ext
  · rfl
  · exact (hright g).symm

/-- Pull back a crossed homomorphism along a group homomorphism. -/
def compMonoidHom {K : Type*} [Group K]
    (d : CrossedHom action) (φ : K →* G) : CrossedHom (action.comp φ) where
  toFun k := d (φ k)
  map_mul' := by
    intro g h
    change d (φ (g * h)) = d (φ g) + action (φ g) (d (φ h))
    rw [φ.map_mul]
    exact d.map_mul (φ g) (φ h)

/-- Pullback along a group homomorphism evaluates by precomposition. -/
@[simp]
theorem compMonoidHom_apply {K : Type*} [Group K]
    (d : CrossedHom action) (φ : K →* G) (k : K) :
    d.compMonoidHom φ k = d (φ k) :=
  rfl

/-- Push a crossed homomorphism through an equivariant additive homomorphism. -/
def mapAddEquivariant (d : CrossedHom action) {B : Type*} [AddCommGroup B]
    (actionB : G →* Multiplicative (AddAut B)) (f : A →+ B)
    (hf : ∀ g a, f (action g a) = actionB g (f a))
    : CrossedHom actionB where
  toFun g := f (d g)
  map_mul' := by
    intro g h
    rw [d.map_mul g h, map_add, hf]

/-- Equivariant pushforward evaluates by applying the additive homomorphism to each value. -/
@[simp]
theorem mapAddEquivariant_apply {B : Type*} [AddCommGroup B]
    (actionB : G →* Multiplicative (AddAut B)) (f : A →+ B)
    (hf : ∀ g a, f (action g a) = actionB g (f a))
    (d : CrossedHom action) (g : G) :
    d.mapAddEquivariant actionB f hf g = f (d g) :=
  rfl

/-- Crossed homomorphisms agreeing on a set agree on the subgroup it generates. -/
theorem eqOn_closure (d e : CrossedHom action) {s : Set G}
    (hs : Set.EqOn d e s) :
    Set.EqOn d e ((Subgroup.closure s : Subgroup G) : Set G) := by
  intro g hg
  exact Subgroup.closure_induction
    (p := fun g _ => d g = e g)
    (fun x hx => hs hx)
    (by
      rw [d.map_one, e.map_one])
    (fun x y _ _ hx hy => by
      rw [d.map_mul x y, e.map_mul x y, hx, hy])
    (fun x _ hx => by
      rw [d.map_inv x, e.map_inv x, hx]) hg

/-- Crossed homomorphisms are determined by their values on a generating set. -/
theorem eq_of_closure_eq_top (d e : CrossedHom action) {s : Set G}
    (hsgen : Subgroup.closure s = ⊤) (hs : Set.EqOn d e s) : d = e := by
  apply CrossedHom.ext
  intro g
  exact d.eqOn_closure e hs (by simp only [hsgen, Subgroup.coe_top, Set.mem_univ])

/-- The zero crossed homomorphism. -/
instance instZero : Zero (CrossedHom action) where
  zero := ⟨fun _ => 0, by intro g h; simp only [map_zero, add_zero]⟩

/-- Pointwise addition of crossed homomorphisms. -/
instance instAdd : Add (CrossedHom action) where
  add d e := ⟨fun g => d g + e g, by
    intro g h
    rw [d.map_mul g h, e.map_mul g h, map_add]
    ac_rfl⟩

/-- The zero crossed homomorphism vanishes at every group element. -/
@[simp]
theorem zero_apply (g : G) : (0 : CrossedHom action) g = 0 := rfl

/-- Addition of crossed homomorphisms is computed pointwise. -/
@[simp]
theorem add_apply (d e : CrossedHom action) (g : G) : (d + e) g = d g + e g := rfl

/-- Natural-number scalar multiplication of crossed homomorphisms is repeated pointwise addition. -/
instance instSMulNat : SMul ℕ (CrossedHom action) := ⟨nsmulRec⟩

/-- Natural-number scalar multiplication of crossed homomorphisms is computed pointwise. -/
@[simp]
theorem nsmul_apply (n : ℕ) (d : CrossedHom action) (g : G) :
    (n • d) g = n • d g := by
  change (nsmulRec n d).toFun g = n • d g
  induction n with
  | zero => simp only [zero_nsmul]; rfl
  | succ n ih =>
      rw [nsmulRec, succ_nsmul]
      change (nsmulRec n d).toFun g + d.toFun g = n • d.toFun g + d.toFun g
      simpa only [toFun_apply] using congrArg (fun x : A => x + d.toFun g) ih

/-- A temporary additive-monoid structure used while constructing the stronger additive group. -/
local instance instAddCommMonoid : AddCommMonoid (CrossedHom action) :=
  Function.Injective.addCommMonoid
    (fun d : CrossedHom action => d.toFun)
    (by intro d e h; exact CrossedHom.ext (congrFun h))
    rfl (fun _ _ => rfl) (fun d n => by funext g; exact nsmul_apply n d g)

/-- Negation of crossed homomorphisms is computed pointwise. -/
instance instNeg : Neg (CrossedHom action) where
  neg d := ⟨fun g => -d g, by
    intro g h
    rw [d.map_mul g h, map_neg]
    simp only [neg_add_rev, add_comm]⟩

/-- Subtraction of crossed homomorphisms is computed pointwise. -/
instance instSub : Sub (CrossedHom action) where
  sub d e := ⟨fun g => d g - e g, by
    intro g h
    rw [d.map_mul g h, e.map_mul g h, map_sub]
    simp only [sub_eq_add_neg, neg_add_rev]
    ac_rfl⟩

/-- Evaluating a negated crossed homomorphism negates its value. -/
@[simp]
theorem neg_apply (d : CrossedHom action) (g : G) : (-d) g = -d g := rfl

/-- Evaluating a difference of crossed homomorphisms subtracts their values. -/
@[simp]
theorem sub_apply (d e : CrossedHom action) (g : G) : (d - e) g = d g - e g := rfl

/-- Integer scalar multiplication of crossed homomorphisms is repeated pointwise addition or
subtraction. -/
instance instSMulInt : SMul ℤ (CrossedHom action) :=
  ⟨zsmulRec (nsmul := nsmulRec)⟩

/-- Integer scalar multiplication of crossed homomorphisms is computed pointwise. -/
@[simp]
theorem zsmul_apply (z : ℤ) (d : CrossedHom action) (g : G) :
    (z • d) g = z • d g := by
  change (zsmulRec (nsmul := nsmulRec) z d).toFun g = z • d g
  cases z with
  | ofNat n => rw [zsmulRec]; change (n • d) g = (n : ℤ) • d g; rw [nsmul_apply, natCast_zsmul]
  | negSucc n =>
      rw [zsmulRec]
      change (-(n.succ • d)) g = Int.negSucc n • d g
      rw [neg_apply, nsmul_apply, negSucc_zsmul]

/-- Pointwise operations make crossed homomorphisms an additive commutative group. -/
instance instAddCommGroup : AddCommGroup (CrossedHom action) :=
  Function.Injective.addCommGroup
    (fun d : CrossedHom action => d.toFun)
    (by intro d e h; exact CrossedHom.ext (congrFun h))
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun d n => by funext g; exact nsmul_apply n d g)
    (fun d z => by funext g; exact zsmul_apply z d g)

end CrossedHom

namespace ScalarCrossedHom

variable {R G A : Type*} [Semiring R] [Group G] [AddCommGroup A] [Module R A]
variable {coeff : G →* R}

/-- Scalar crossed homomorphisms satisfy the scalar Fox--Leibniz product rule. -/
@[simp]
theorem map_mul (d : ScalarCrossedHom coeff A) (g h : G) :
    d (g * h) = d g + coeff g • d h := by
  simpa only [scalarCrossedAction_apply] using CrossedHom.map_mul d g h

/-- A scalar crossed homomorphism vanishes at the identity. -/
@[simp]
theorem map_one (d : ScalarCrossedHom coeff A) : d 1 = 0 :=
  CrossedHom.map_one d

/-- The value of a scalar crossed homomorphism at an inverse is the transported negative value. -/
theorem map_inv (d : ScalarCrossedHom coeff A) (g : G) :
    d g⁻¹ = -(coeff g⁻¹ • d g) := by
  simpa only [scalarCrossedAction_apply] using CrossedHom.map_inv d g

/-- Formula for a scalar crossed homomorphism on a product with an inverse on the left. -/
theorem map_inv_mul (d : ScalarCrossedHom coeff A) (g h : G) :
    d (g⁻¹ * h) = -(coeff g⁻¹ • d g) + coeff g⁻¹ • d h := by
  simpa only [scalarCrossedAction_apply] using CrossedHom.map_inv_mul d g h

/-- Formula for a scalar crossed homomorphism on a product with an inverse on the right. -/
theorem map_mul_inv (d : ScalarCrossedHom coeff A) (g h : G) :
    d (g * h⁻¹) = d g - coeff (g * h⁻¹) • d h := by
  simpa only [scalarCrossedAction_apply] using CrossedHom.map_mul_inv d g h

/-- The scalar Fox rule written for group division. -/
theorem map_div (d : ScalarCrossedHom coeff A) (g h : G) :
    d (g / h) = d g - coeff (g / h) • d h := by
  simpa only [scalarCrossedAction_apply] using CrossedHom.map_div d g h

/-- The scalar crossed-homomorphism formula for a conjugate. -/
theorem map_conj (d : ScalarCrossedHom coeff A) (g h : G) :
    d (g * h * g⁻¹) = d g + coeff g • d h - coeff (g * h * g⁻¹) • d g := by
  simpa only [scalarCrossedAction_apply] using CrossedHom.map_conj d g h

/-- The scalar crossed-homomorphism formula for a commutator. -/
theorem map_commutator (d : ScalarCrossedHom coeff A) (g h : G) :
    d ⁅g, h⁆ = d g + coeff g • d h - coeff (g * h * g⁻¹) • d g -
      coeff ⁅g, h⁆ • d h := by
  simpa only [scalarCrossedAction_apply] using CrossedHom.map_commutator d g h

/-- The value on a positive power is the sum of the translates of the value on its base. -/
theorem map_pow (d : ScalarCrossedHom coeff A) (g : G) (n : ℕ) :
    d (g ^ n) = (Finset.range n).sum (fun k => coeff (g ^ k) • d g) := by
  simpa only [scalarCrossedAction_apply] using CrossedHom.map_pow d g n

/-- Restrict a scalar crossed homomorphism to a subgroup on which its coefficient is trivial. -/
def restrictTrivialSubgroupAddMonoidHom
    (d : ScalarCrossedHom coeff A) (N : Subgroup G)
    (hN : ∀ n : N, coeff n = 1) :
    Additive N →+ A where
  toFun n := d ((Additive.toMul n : N) : G)
  map_zero' := by
    change d (1 : G) = 0
    exact map_one d
  map_add' g h := by
    change d (((Additive.toMul g : N) * (Additive.toMul h : N) : N) : G) =
      d ((Additive.toMul g : N) : G) + d ((Additive.toMul h : N) : G)
    have hmul :=
      d.map_mul ((Additive.toMul g : N) : G) ((Additive.toMul h : N) : G)
    simpa only [Subgroup.coe_mul, hN (Additive.toMul g), one_smul] using hmul

/-- Restriction to a coefficient-trivial subgroup evaluates as the original crossed homomorphism. -/
@[simp]
theorem restrictTrivialSubgroupAddMonoidHom_apply
    (d : ScalarCrossedHom coeff A) (N : Subgroup G)
    (hN : ∀ n : N, coeff n = 1) (g : N) :
    restrictTrivialSubgroupAddMonoidHom d N hN (Additive.ofMul g) = d g :=
  rfl

/-- A linear map is equivariant for scalar crossed actions and hence maps scalar crossed
homomorphisms to scalar crossed homomorphisms. -/
def mapLinear (d : ScalarCrossedHom coeff A) {B : Type*} [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) : ScalarCrossedHom coeff B :=
  d.mapAddEquivariant (scalarCrossedAction (A := B) coeff) f.toAddMonoidHom
    (by
      intro g a
      change f (coeff g • a) = coeff g • f a
      exact f.map_smul (coeff g) a)

/-- Linear pushforward evaluates by applying the linear map to each crossed-homomorphism value. -/
@[simp]
theorem mapLinear_apply {B : Type*} [AddCommGroup B] [Module R B]
    (d : ScalarCrossedHom coeff A) (f : A →ₗ[R] B) (g : G) :
    d.mapLinear f g = f (d g) :=
  rfl

/-- Pull back a scalar crossed homomorphism while retaining its scalar specialization. -/
def compMonoidHom {K : Type*} [Group K]
    (d : ScalarCrossedHom coeff A) (φ : K →* G) : ScalarCrossedHom (coeff.comp φ) A where
  toFun k := d (φ k)
  map_mul' := by
    intro g h
    change d (φ (g * h)) = d (φ g) + coeff (φ g) • d (φ h)
    rw [φ.map_mul]
    exact d.map_mul (φ g) (φ h)

/-- Pullback of a scalar crossed homomorphism evaluates by precomposition. -/
@[simp]
theorem compMonoidHom_apply {K : Type*} [Group K]
    (d : ScalarCrossedHom coeff A) (φ : K →* G) (k : K) :
    d.compMonoidHom φ k = d (φ k) :=
  rfl

end ScalarCrossedHom

end FoxDifferential
