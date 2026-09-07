import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.System.Basic

set_option autoImplicit false

/-!
# Fox differential: coefficient rings — mod-\(n\) completed group algebra — system — add comm group

The principal declarations in this module are:

- `instAddCommGroupModNCompletedGroupAlgebraStage`
  Each finite mod-\(n\) group-algebra stage carries its standard additive commutative group.
- `instAddCommGroupModNCompletedGroupAlgebraFamily`
  The dependent family of finite mod-\(n\) group-algebra stages carries the pointwise additive
  commutative group structure.
- `coe_zero_modNCompletedGroupAlgebra`
  The inclusion of the mod-\(n\) completed group algebra into the ambient completed group algebra
  preserves zero.
- `coe_add_modNCompletedGroupAlgebra`
  The inclusion of the mod-\(n\) completed group algebra into the ambient completed group algebra
  preserves addition.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u


variable (n : ℕ) [Fact (0 < n)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The zero element is defined coordinatewise as the compatible family of zero elements at all
finite stages.
-/
instance instZeroModNCompletedGroupAlgebra : Zero (ModNCompletedGroupAlgebra n G) where
  zero := ⟨fun U => (0 : ModNCompletedGroupAlgebraStage n G U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransition n G hUV
      (0 : ModNCompletedGroupAlgebraStage n G V) = 0
    exact map_zero (modNCompletedGroupAlgebraTransition n G hUV)⟩

/--
Addition in the mod-\(n\) completed group algebra is defined coordinatewise through finite-stage
group-algebra additions.
-/
instance instAddModNCompletedGroupAlgebra : Add (ModNCompletedGroupAlgebra n G) where
  add x y := ⟨fun U =>
      (show ModNCompletedGroupAlgebraStage n G U from x.1 U) +
        (show ModNCompletedGroupAlgebraStage n G U from y.1 U), by
    intro U V hUV
    calc
      modNCompletedGroupAlgebraTransition n G hUV
          ((show ModNCompletedGroupAlgebraStage n G V from x.1 V) +
            (show ModNCompletedGroupAlgebraStage n G V from y.1 V))
        =
          modNCompletedGroupAlgebraTransition n G hUV
              (show ModNCompletedGroupAlgebraStage n G V from x.1 V) +
            modNCompletedGroupAlgebraTransition n G hUV
              (show ModNCompletedGroupAlgebraStage n G V from y.1 V) := by
            rw [map_add]
      _ =
          (show ModNCompletedGroupAlgebraStage n G U from x.1 U) +
            (show ModNCompletedGroupAlgebraStage n G U from y.1 U) := by
            exact congrArg₂ HAdd.hAdd (x.2 U V hUV) (y.2 U V hUV)⟩

/--
Coordinatewise zero and addition on the mod-\(n\) completed group algebra satisfy the left and
right zero laws.
-/
instance instAddZeroClassModNCompletedGroupAlgebra :
    AddZeroClass (ModNCompletedGroupAlgebra n G) where
  zero := 0
  add := (· + ·)
  zero_add x := by
    apply Subtype.ext
    funext U
    change (0 : ModNCompletedGroupAlgebraStage n G U) +
      (show ModNCompletedGroupAlgebraStage n G U from x.1 U) =
        (show ModNCompletedGroupAlgebraStage n G U from x.1 U)
    exact zero_add (show ModNCompletedGroupAlgebraStage n G U from x.1 U)
  add_zero x := by
    apply Subtype.ext
    funext U
    change (show ModNCompletedGroupAlgebraStage n G U from x.1 U) +
      (0 : ModNCompletedGroupAlgebraStage n G U) =
        (show ModNCompletedGroupAlgebraStage n G U from x.1 U)
    exact add_zero (show ModNCompletedGroupAlgebraStage n G U from x.1 U)

/--
Negation on the mod-\(n\) completed group algebra is defined coordinatewise through finite-stage
group-algebra negations.
-/
instance instNegModNCompletedGroupAlgebra : Neg (ModNCompletedGroupAlgebra n G) where
  neg x := ⟨fun U => -(show ModNCompletedGroupAlgebraStage n G U from x.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransition n G hUV
        (-(show ModNCompletedGroupAlgebraStage n G V from x.1 V)) =
      -(show ModNCompletedGroupAlgebraStage n G U from x.1 U)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 U V hUV)⟩

/--
Subtraction on the completed group algebra is defined coordinatewise through the finite-stage
group-algebra subtractions.
-/
instance instSubModNCompletedGroupAlgebra : Sub (ModNCompletedGroupAlgebra n G) where
  sub x y := ⟨fun U =>
      (show ModNCompletedGroupAlgebraStage n G U from x.1 U) -
        (show ModNCompletedGroupAlgebraStage n G U from y.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransition n G hUV
        ((show ModNCompletedGroupAlgebraStage n G V from x.1 V) -
          (show ModNCompletedGroupAlgebraStage n G V from y.1 V)) =
      (show ModNCompletedGroupAlgebraStage n G U from x.1 U) -
        (show ModNCompletedGroupAlgebraStage n G U from y.1 U)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 U V hUV) (y.2 U V hUV)⟩

/--
The completed group algebra carries coefficient-ring scalar multiplication by applying the
scalar action at every finite quotient stage.
-/
instance instSMulNatModNCompletedGroupAlgebra : SMul ℕ (ModNCompletedGroupAlgebra n G) where
  smul m x := ⟨fun U => m • (show ModNCompletedGroupAlgebraStage n G U from x.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransition n G hUV
        (m • (show ModNCompletedGroupAlgebraStage n G V from x.1 V)) =
      m • (show ModNCompletedGroupAlgebraStage n G U from x.1 U)
    rw [map_nsmul]
    exact congrArg (m • ·) (x.2 U V hUV)⟩

/--
The completed group algebra carries coefficient-ring scalar multiplication by applying the
scalar action at every finite quotient stage.
-/
instance instSMulIntModNCompletedGroupAlgebra : SMul ℤ (ModNCompletedGroupAlgebra n G) where
  smul m x := ⟨fun U => m • (show ModNCompletedGroupAlgebraStage n G U from x.1 U), by
    intro U V hUV
    change modNCompletedGroupAlgebraTransition n G hUV
        (m • (show ModNCompletedGroupAlgebraStage n G V from x.1 V)) =
      m • (show ModNCompletedGroupAlgebraStage n G U from x.1 U)
    rw [map_zsmul]
    exact congrArg (m • ·) (x.2 U V hUV)⟩

/-- Each finite mod-\(n\) group-algebra stage carries its standard additive commutative group. -/
@[reducible]
private def instAddCommGroupModNCompletedGroupAlgebraStage (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    AddCommGroup ((modNCompletedGroupAlgebraSystem n G).X U) := by
  dsimp [modNCompletedGroupAlgebraSystem, ModNCompletedGroupAlgebraStage]
  infer_instance
attribute [local instance] instAddCommGroupModNCompletedGroupAlgebraStage

/--
The dependent family of finite mod-\(n\) group-algebra stages carries the pointwise additive
commutative group structure.
-/
@[reducible]
private def instAddCommGroupModNCompletedGroupAlgebraFamily :
    AddCommGroup ((i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) →
        (modNCompletedGroupAlgebraSystem n G).X i) :=
  inferInstance
attribute [local instance] instAddCommGroupModNCompletedGroupAlgebraFamily

omit [Fact (0 < n)] in
/--
The inclusion of the mod-\(n\) completed group algebra into the ambient completed group algebra
preserves zero.
-/
@[simp]
theorem coe_zero_modNCompletedGroupAlgebra :
    ((0 : ModNCompletedGroupAlgebra n G) :
      (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) →
          (modNCompletedGroupAlgebraSystem n G).X i) = 0 := by
  funext U
  rfl

omit [Fact (0 < n)] in
/--
The inclusion of the mod-\(n\) completed group algebra into the ambient completed group algebra
preserves addition.
-/
@[simp]
theorem coe_add_modNCompletedGroupAlgebra
    (x y : ModNCompletedGroupAlgebra n G) :
    ((x + y : ModNCompletedGroupAlgebra n G) :
      (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) →
          (modNCompletedGroupAlgebraSystem n G).X i) =
      x + y := by
  funext U
  rfl

omit [Fact (0 < n)] in
/--
The inclusion of the mod-\(n\) completed group algebra into the ambient completed group algebra
preserves negation.
-/
@[simp]
theorem coe_neg_modNCompletedGroupAlgebra
    (x : ModNCompletedGroupAlgebra n G) :
    ((-x : ModNCompletedGroupAlgebra n G) :
      (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) →
          (modNCompletedGroupAlgebraSystem n G).X i) =
      -x := by
  funext U
  rfl

omit [Fact (0 < n)] in
/--
The inclusion of the mod-\(n\) completed group algebra into the ambient completed group algebra
preserves subtraction.
-/
@[simp]
theorem coe_sub_modNCompletedGroupAlgebra
    (x y : ModNCompletedGroupAlgebra n G) :
    ((x - y : ModNCompletedGroupAlgebra n G) :
      (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) →
          (modNCompletedGroupAlgebraSystem n G).X i) =
      x - y := by
  funext U
  rfl

omit [Fact (0 < n)] in
/--
The inclusion of the mod-\(n\) completed group algebra into the ambient completed group algebra
preserves natural-number scalar multiplication.
-/
@[simp]
theorem coe_nsmul_modNCompletedGroupAlgebra
    (m : ℕ) (x : ModNCompletedGroupAlgebra n G) :
    ((m • x : ModNCompletedGroupAlgebra n G) :
      (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) →
          (modNCompletedGroupAlgebraSystem n G).X i) =
      m • x := by
  funext U
  rfl

omit [Fact (0 < n)] in
/--
The inclusion of the mod-\(n\) completed group algebra into the ambient completed group algebra
preserves integer scalar multiplication.
-/
@[simp]
theorem coe_zsmul_modNCompletedGroupAlgebra
    (m : ℤ) (x : ModNCompletedGroupAlgebra n G) :
    ((m • x : ModNCompletedGroupAlgebra n G) :
      (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) →
          (modNCompletedGroupAlgebraSystem n G).X i) =
      m • x := by
  funext U
  rfl

/--
The mod-\(n\) completion inherits an additive commutative group structure from its injective
inclusion into the family of finite stages.
-/
instance instAddCommGroupModNCompletedGroupAlgebra :
    AddCommGroup (ModNCompletedGroupAlgebra n G) :=
  Function.Injective.addCommGroup
    (fun x : ModNCompletedGroupAlgebra n G =>
      (x : (i : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) →
          (modNCompletedGroupAlgebraSystem n G).X i))
    Subtype.val_injective
    (coe_zero_modNCompletedGroupAlgebra (n := n) (G := G))
    (coe_add_modNCompletedGroupAlgebra (n := n) (G := G))
    (coe_neg_modNCompletedGroupAlgebra (n := n) (G := G))
    (coe_sub_modNCompletedGroupAlgebra (n := n) (G := G))
    (fun x m => coe_nsmul_modNCompletedGroupAlgebra (n := n) (G := G) m x)
    (fun x m => coe_zsmul_modNCompletedGroupAlgebra (n := n) (G := G) m x)

omit [Fact (0 < n)] in
/-- The finite-stage projection sends \(0\) to \(0\). -/
@[simp]
theorem modNCompletedGroupAlgebraProjection_zero (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    modNCompletedGroupAlgebraProjection n G U (0 : ModNCompletedGroupAlgebra n G) = 0 := by
  change (0 : ModNCompletedGroupAlgebraStage n G U) = 0
  rfl

omit [Fact (0 < n)] in
/-- The mod-\(n\) finite-stage projection preserves addition. -/
@[simp]
theorem modNCompletedGroupAlgebraProjection_add (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G)
    (x y : ModNCompletedGroupAlgebra n G) :
    modNCompletedGroupAlgebraProjection n G U (x + y) =
      modNCompletedGroupAlgebraProjection n G U x +
        modNCompletedGroupAlgebraProjection n G U y := by
  change (show ModNCompletedGroupAlgebraStage n G U from (x + y).1 U) =
    (show ModNCompletedGroupAlgebraStage n G U from x.1 U) +
      (show ModNCompletedGroupAlgebraStage n G U from y.1 U)
  rfl

omit [Fact (0 < n)] in
/-- The mod-\(n\) finite-stage projection preserves negation. -/
@[simp]
theorem modNCompletedGroupAlgebraProjection_neg (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G)
    (x : ModNCompletedGroupAlgebra n G) :
    modNCompletedGroupAlgebraProjection n G U (-x) =
      -modNCompletedGroupAlgebraProjection n G U x := by
  change (show ModNCompletedGroupAlgebraStage n G U from (-x).1 U) =
    -(show ModNCompletedGroupAlgebraStage n G U from x.1 U)
  rfl

omit [Fact (0 < n)] in
/-- The mod-\(n\) finite-stage projection preserves subtraction. -/
@[simp]
theorem modNCompletedGroupAlgebraProjection_sub (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G)
    (x y : ModNCompletedGroupAlgebra n G) :
    modNCompletedGroupAlgebraProjection n G U (x - y) =
      modNCompletedGroupAlgebraProjection n G U x -
        modNCompletedGroupAlgebraProjection n G U y := by
  change (show ModNCompletedGroupAlgebraStage n G U from (x - y).1 U) =
    (show ModNCompletedGroupAlgebraStage n G U from x.1 U) -
      (show ModNCompletedGroupAlgebraStage n G U from y.1 U)
  rfl

omit [Fact (0 < n)] in
end

end FoxDifferential
