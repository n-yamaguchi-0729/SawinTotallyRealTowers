import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.System.CompletionMap

set_option autoImplicit false

/-!
# Fox differential: completed — coefficient rings — mod-\(n\) completed group algebra — augmentation

The principal declarations in this module are:

- `modNCompletedGroupAlgebraStageAugmentation`
  The augmentation on one residue-coefficient finite stage.
- `modNCompletedGroupAlgebraAugmentationAt`
  The augmentation value of a residue-coefficient completed point, read at one finite stage.
- `modNCompletedGroupAlgebraStageAugmentation_of`
  The finite-stage \(n\)-modular augmentation sends every group-like basis element to \(1\).
- `modNCompletedGroupAlgebraStageAugmentation_compatible`
  Finite-stage \(n\)-modular augmentations are compatible with group-quotient transition maps.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u


variable (n : ℕ) [Fact (0 < n)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The augmentation on one residue-coefficient finite stage. -/
def modNCompletedGroupAlgebraStageAugmentation (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    ModNCompletedGroupAlgebraStage n G U →+* ModNCompletedCoeff n :=
  MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
    (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)
    (1 : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U →* ModNCompletedCoeff n)

omit [Fact (0 < n)] in
/-- The finite-stage \(n\)-modular augmentation sends every group-like basis element to \(1\). -/
@[simp]
theorem modNCompletedGroupAlgebraStageAugmentation_of
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (q :
        _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U) :
    modNCompletedGroupAlgebraStageAugmentation n G U
        (MonoidAlgebra.of (ModNCompletedCoeff n) _ q) = 1 := by
  change
    MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
        (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)
        (1 : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U →*
          ModNCompletedCoeff n)
        (MonoidAlgebra.of (ModNCompletedCoeff n) _ q) = 1
  rw [MonoidAlgebra.lift_of]
  exact MonoidHom.one_apply q

omit [Fact (0 < n)] in
/-- Finite-stage \(n\)-modular augmentations are compatible with group-quotient transition maps. -/
@[simp 900]
theorem modNCompletedGroupAlgebraStageAugmentation_compatible
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (modNCompletedGroupAlgebraStageAugmentation n G U).comp
        (modNCompletedGroupAlgebraTransition n G hUV) =
      modNCompletedGroupAlgebraStageAugmentation n G V := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
          (modNCompletedGroupAlgebraTransition n G hUV)) x =
        modNCompletedGroupAlgebraStageAugmentation n G V x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, modNCompletedGroupAlgebraTransition_of]
    change
      MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)
          (1 : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U →*
            ModNCompletedCoeff n)
          (MonoidAlgebra.single
            ((OpenNormalSubgroupInClass.map
              (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
              (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) 1) =
        MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G V)
          (1 : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G V →*
            ModNCompletedCoeff n)
          (MonoidAlgebra.of (ModNCompletedCoeff n) _ q)
    erw [MonoidAlgebra.lift_single, MonoidAlgebra.lift_of]
    change (1 : ModNCompletedCoeff n) • 1 = 1
    exact one_smul _ _
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    have hcoeff :
        ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
            (modNCompletedGroupAlgebraTransition n G hUV))
            (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupAlgebraStage n G V) a) =
          (modNCompletedGroupAlgebraStageAugmentation n G V)
            (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupAlgebraStage n G V) a) := by
      rw [RingHom.comp_apply]
      change
        MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
            (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)
            (1 : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U →*
              ModNCompletedCoeff n)
            (MonoidAlgebra.mapDomain _
              (algebraMap (ModNCompletedCoeff n)
                (ModNCompletedGroupAlgebraStage n G V) a)) =
          MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
            (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G V)
            (1 : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G V →*
              ModNCompletedCoeff n)
            (algebraMap (ModNCompletedCoeff n)
              (ModNCompletedGroupAlgebraStage n G V) a)
      erw [MonoidAlgebra.mapDomain_algebraMap]
      exact
        (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
            (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)
            (1 : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U →*
              ModNCompletedCoeff n)).commutes a |>.trans
          ((MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
            (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G V)
            (1 : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G V →*
              ModNCompletedCoeff n)).commutes a).symm
    rw [hcoeff]

omit [Fact (0 < n)] in
/--
Composing the finite-stage \(n\)-modular augmentation with the dense stage map gives the
ordinary \(n\)-modular group-algebra augmentation.
-/
@[simp 900]
theorem modNCompletedGroupAlgebraStageAugmentation_comp_stageMap
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    (modNCompletedGroupAlgebraStageAugmentation n G U).comp
        (modNCompletedGroupAlgebraStageMap n G U) =
      MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
        (1 : G →* ModNCompletedCoeff n) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
          (modNCompletedGroupAlgebraStageMap n G U)) x =
        (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
          (1 : G →* ModNCompletedCoeff n)) x)
    x ?_ ?_ ?_
  · intro g
    rw [RingHom.comp_apply, modNCompletedGroupAlgebraStageMap_of]
    change
      MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)
          (1 : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U →*
            ModNCompletedCoeff n)
          (MonoidAlgebra.single
            (openNormalSubgroupInClassProj
              (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) 1) =
        MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
          (1 : G →* ModNCompletedCoeff n)
          (MonoidAlgebra.of (ModNCompletedCoeff n) G g)
    erw [MonoidAlgebra.lift_single, MonoidAlgebra.lift_of]
    change (1 : ModNCompletedCoeff n) • 1 = 1
    exact one_smul _ _
  · intro x y hx hy
    simp only [hx, hy, map_add]
  · intro a x hx
    have hcoeff :
        ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
            (modNCompletedGroupAlgebraStageMap n G U))
            (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) = a := by
      rw [RingHom.comp_apply]
      change
        modNCompletedGroupAlgebraStageAugmentation n G U
            (MonoidAlgebra.mapDomain _
              (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a)) = a
      erw [MonoidAlgebra.mapDomain_algebraMap]
      change
        MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
            (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)
            (1 : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U →*
              ModNCompletedCoeff n)
            (algebraMap (ModNCompletedCoeff n)
              (ModNCompletedGroupAlgebraStage n G U) a) = a
      simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
        (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)
          (1 : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U →*
            ModNCompletedCoeff n)).commutes a
    have hcoeff' :
        ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
            (modNCompletedGroupAlgebraStageMap n G U))
            (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) =
          (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
            (1 : G →* ModNCompletedCoeff n))
            (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) := by
      rw [hcoeff]
      simp only [MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id,
          Function.comp_apply, id_eq,
  MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]
    rw [Algebra.smul_def]
    calc
      ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
          (modNCompletedGroupAlgebraStageMap n G U))
          ((algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) * x)
        =
          ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
              (modNCompletedGroupAlgebraStageMap n G U))
              (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) *
            ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
              (modNCompletedGroupAlgebraStageMap n G U)) x := by
            rw [RingHom.map_mul]
      _ =
          ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
              (modNCompletedGroupAlgebraStageMap n G U))
              (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) *
            (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
              (1 : G →* ModNCompletedCoeff n)) x := by
            rw [hx]
      _ =
          (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
              (1 : G →* ModNCompletedCoeff n))
              (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) *
            (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
              (1 : G →* ModNCompletedCoeff n)) x := by
            rw [hcoeff']
      _ =
          (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
            (1 : G →* ModNCompletedCoeff n))
            ((algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) * x) := by
            exact
              (map_mul
                (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
                  (1 : G →* ModNCompletedCoeff n))
                (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) x).symm

/-- The augmentation value of a residue-coefficient completed point, read at one finite stage. -/
def modNCompletedGroupAlgebraAugmentationAt (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    ModNCompletedGroupAlgebra n G → ModNCompletedCoeff n :=
  fun x => modNCompletedGroupAlgebraStageAugmentation n G U
    (modNCompletedGroupAlgebraProjection n G U x)

omit [Fact (0 < n)] in
/--
The finite coordinate used to compute the \(n\)-modular completed augmentation is independent of
passing to a finer quotient stage.
-/
@[simp 900]
theorem modNCompletedGroupAlgebraAugmentationAt_eq_of_le
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) (x :
        ModNCompletedGroupAlgebra n G) :
    modNCompletedGroupAlgebraAugmentationAt n G U x =
      modNCompletedGroupAlgebraAugmentationAt n G V x := by
  unfold modNCompletedGroupAlgebraAugmentationAt
  have hcomp := congrFun
    (congrArg DFunLike.coe
      (modNCompletedGroupAlgebraStageAugmentation_compatible
        (n := n) (G := G) (U := U) (V := V) hUV))
    (modNCompletedGroupAlgebraProjection n G V x)
  calc
    modNCompletedGroupAlgebraStageAugmentation n G U
        (modNCompletedGroupAlgebraProjection n G U x)
      =
    modNCompletedGroupAlgebraStageAugmentation n G U
      (modNCompletedGroupAlgebraTransition n G hUV
        (modNCompletedGroupAlgebraProjection n G V x)) := by
          have hx := x.2 U V hUV
          change modNCompletedGroupAlgebraTransition n G hUV
              (modNCompletedGroupAlgebraProjection n G V x) =
            modNCompletedGroupAlgebraProjection n G U x at hx
          exact congrArg
            (modNCompletedGroupAlgebraStageAugmentation n G U) hx.symm
    _ = modNCompletedGroupAlgebraStageAugmentation n G V
          (modNCompletedGroupAlgebraProjection n G V x) := by
          exact hcomp

/-- The canonical augmentation on the residue-coefficient completed group algebra. -/
def modNCompletedGroupAlgebraAugmentation :
    ModNCompletedGroupAlgebra n G → ModNCompletedCoeff n :=
  modNCompletedGroupAlgebraAugmentationAt n G
      (_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G)

omit [Fact (0 < n)] in
/-- The \(n\)-modular completed augmentation is computed at any finite quotient stage. -/
@[simp]
theorem modNCompletedGroupAlgebraAugmentation_eq_at
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (x :
        ModNCompletedGroupAlgebra n G) :
    modNCompletedGroupAlgebraAugmentation n G x =
      modNCompletedGroupAlgebraAugmentationAt n G U x := by
  exact modNCompletedGroupAlgebraAugmentationAt_eq_of_le
    (n := n) (G := G)
    (U := _root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G) (V := U)
    (_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex_le (G := G) U) x

omit [Fact (0 < n)] in
/--
The \(n\)-modular completed augmentation extends the abstract \(n\)-modular group-algebra
augmentation through the dense map.
-/
@[simp]
theorem modNCompletedGroupAlgebraAugmentation_toCompleted
    (x : ModNCompletedGroupRing n G) :
    modNCompletedGroupAlgebraAugmentation n G (toModNCompletedGroupAlgebra n G x) =
      MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
        (1 : G →* ModNCompletedCoeff n) x := by
  unfold modNCompletedGroupAlgebraAugmentation modNCompletedGroupAlgebraAugmentationAt
  rw [modNCompletedGroupAlgebraProjection_toCompleted]
  exact congrFun
    (congrArg DFunLike.coe
      (modNCompletedGroupAlgebraStageAugmentation_comp_stageMap
        (n := n) (G := G) (_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G)))
    x

end

end FoxDifferential
