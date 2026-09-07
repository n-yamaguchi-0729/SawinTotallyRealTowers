import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Basic.Augmentation
import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Basic.StageCoeffMap.Coeff

set_option autoImplicit false

/-!
# Fox differential: coefficient rings — prime-power completed group algebra — system — basic

The principal declarations in this module are:

- `PrimePowerCompletedGroupAlgebraStage`
  The stage at index \((a,U)\), namely \((\mathrm{ZMod}\,\ell^a)[G/U]\).
- `primePowerCompletedGroupAlgebraTransition`
  The combined transition map for the two-parameter prime-power stage calculus.
- `primePowerCompletedGroupAlgebraTransition_of`
  The transition map sends a group-like basis element to the basis element supported at its image in
  the coarser quotient in the Fox differential construction.
- `primePowerCompletedGroupAlgebraTransition_eq`
  The transition map for the prime-power completed group algebra commutes with the finite-stage
  coordinate maps.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < ℓ)] in
/-- The stage at index \((a,U)\), namely \((\mathrm{ZMod}\,\ell^a)[G/U]\). -/
abbrev PrimePowerCompletedGroupAlgebraStage
    (i : PrimePowerCompletedGroupAlgebraIndex G) : Type _ :=
  ModNCompletedGroupAlgebraStage (ℓ ^ i.1) G i.2

/-- Each prime-power completed group-algebra stage is finite. -/
instance instFinitePrimePowerCompletedGroupAlgebraStage
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    Finite (PrimePowerCompletedGroupAlgebraStage ℓ G i) := by
  let : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
  exact instFiniteModNCompletedGroupAlgebraStage (n := ℓ ^ i.1) (G := G) i.2

omit [Fact (0 < ℓ)] in
/-- The combined transition map for the two-parameter prime-power stage calculus. -/
def primePowerCompletedGroupAlgebraTransition
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j) :
    PrimePowerCompletedGroupAlgebraStage ℓ G j →+* PrimePowerCompletedGroupAlgebraStage ℓ G i := by
  exact
    (modNCompletedGroupAlgebraStageCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) i.2
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
      (modNCompletedGroupAlgebraTransition (ℓ ^ j.1) G hij.2)

omit [Fact (0 < ℓ)] in
/--
The transition map sends a group-like basis element to the basis element supported at its image
in the coarser quotient in the Fox differential construction.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraTransition_of
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j)
    (q : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G j.2) :
    primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1)) _ q) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1)) _
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q) := by
  rw [primePowerCompletedGroupAlgebraTransition, RingHom.comp_apply,
    modNCompletedGroupAlgebraTransition_of]
  change
    (modNCompletedGroupAlgebraStageCoeffMap
      (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) i.2
      (primePow_dvd_primePow (ℓ := ℓ) hij.1))
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1)) _
          ((OpenNormalSubgroupInClass.map
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
            (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q)) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1)) _
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q)
  exact modNCompletedGroupAlgebraStageCoeffMap_of
    (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) (U := i.2)
    (primePow_dvd_primePow (ℓ := ℓ) hij.1)
    ((OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q)

omit [Fact (0 < ℓ)] in
/--
The transition map for the prime-power completed group algebra commutes with the finite-stage
coordinate maps.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraTransition_eq
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j) :
    primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij =
      (modNCompletedGroupAlgebraStageCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) i.2
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
        (modNCompletedGroupAlgebraTransition (ℓ ^ j.1) G hij.2) := by
  rfl

omit [Fact (0 < ℓ)] in
/--
The same combined transition can also be read as coefficient reduction at the source stage
followed by the quotient-direction transition at the smaller modulus.
-/
theorem primePowerCompletedGroupAlgebraTransition_eq'
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j) :
    primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij =
      (modNCompletedGroupAlgebraTransition (ℓ ^ i.1) G hij.2).comp
        (modNCompletedGroupAlgebraStageCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) j.2
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)) := by
  rw [primePowerCompletedGroupAlgebraTransition_eq]
  exact modNCompletedGroupAlgebraStageCoeffMap_compatible
    (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) (U := i.2) (V := j.2)
    hij.2 (primePow_dvd_primePow (ℓ := ℓ) hij.1)

omit [Fact (0 < ℓ)] in
/--
The transition map attached to the identity refinement is the identity homomorphism in the Fox
differential construction.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraTransition_id
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) (le_rfl : i ≤ i) =
      RingHom.id _ := by
  rw [primePowerCompletedGroupAlgebraTransition_eq]
  rw [modNCompletedGroupAlgebraTransition_id, modNCompletedGroupAlgebraStageCoeffMap_rfl]
  simp only [RingHomCompTriple.comp_eq]

omit [Fact (0 < ℓ)] in
/--
Prime-power completed group-algebra transitions compose along a chain of quotient refinements.
-/
@[simp 900]
theorem primePowerCompletedGroupAlgebraTransition_comp
    {i j k : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j) (hjk : j ≤ k) :
    (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij).comp
        (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hjk) =
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) (hij.trans hjk) := by
  calc
    (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij).comp
        (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hjk)
      =
    ((modNCompletedGroupAlgebraStageCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) i.2
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
        (modNCompletedGroupAlgebraTransition (ℓ ^ j.1) G hij.2)).comp
      ((modNCompletedGroupAlgebraTransition (ℓ ^ j.1) G hjk.2).comp
        (modNCompletedGroupAlgebraStageCoeffMap
          (n := ℓ ^ j.1) (m := ℓ ^ k.1) (G := G) k.2
          (primePow_dvd_primePow (ℓ := ℓ) hjk.1))) := by
          rw [primePowerCompletedGroupAlgebraTransition_eq,
            primePowerCompletedGroupAlgebraTransition_eq']
    _ =
    (modNCompletedGroupAlgebraStageCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) i.2
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
      (((modNCompletedGroupAlgebraTransition (ℓ ^ j.1) G hij.2).comp
          (modNCompletedGroupAlgebraTransition (ℓ ^ j.1) G hjk.2)).comp
        (modNCompletedGroupAlgebraStageCoeffMap
          (n := ℓ ^ j.1) (m := ℓ ^ k.1) (G := G) k.2
          (primePow_dvd_primePow (ℓ := ℓ) hjk.1))) := by
          apply RingHom.ext
          intro x
          rfl
    _ =
    (modNCompletedGroupAlgebraStageCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) i.2
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
      ((modNCompletedGroupAlgebraTransition (ℓ ^ j.1) G (hij.2.trans hjk.2)).comp
        (modNCompletedGroupAlgebraStageCoeffMap
          (n := ℓ ^ j.1) (m := ℓ ^ k.1) (G := G) k.2
          (primePow_dvd_primePow (ℓ := ℓ) hjk.1))) := by
          rw [modNCompletedGroupAlgebraTransition_comp]
    _ =
    ((modNCompletedGroupAlgebraStageCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) i.2
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
        (modNCompletedGroupAlgebraTransition (ℓ ^ j.1) G (hij.2.trans hjk.2))).comp
      (modNCompletedGroupAlgebraStageCoeffMap
        (n := ℓ ^ j.1) (m := ℓ ^ k.1) (G := G) k.2
        (primePow_dvd_primePow (ℓ := ℓ) hjk.1)) := by
          rw [← RingHom.comp_assoc]
    _ =
    ((modNCompletedGroupAlgebraTransition (ℓ ^ i.1) G (hij.2.trans hjk.2)).comp
        (modNCompletedGroupAlgebraStageCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) k.2
          (primePow_dvd_primePow (ℓ := ℓ) hij.1))).comp
      (modNCompletedGroupAlgebraStageCoeffMap
        (n := ℓ ^ j.1) (m := ℓ ^ k.1) (G := G) k.2
        (primePow_dvd_primePow (ℓ := ℓ) hjk.1)) := by
          rw [modNCompletedGroupAlgebraStageCoeffMap_compatible
            (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G)
            (U := i.2) (V := k.2) (hUV := hij.2.trans hjk.2)
            (hnm := primePow_dvd_primePow (ℓ := ℓ) hij.1)]
    _ =
    (modNCompletedGroupAlgebraTransition (ℓ ^ i.1) G (hij.2.trans hjk.2)).comp
      ((modNCompletedGroupAlgebraStageCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) k.2
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
        (modNCompletedGroupAlgebraStageCoeffMap
          (n := ℓ ^ j.1) (m := ℓ ^ k.1) (G := G) k.2
          (primePow_dvd_primePow (ℓ := ℓ) hjk.1))) := by
          rw [RingHom.comp_assoc]
    _ =
    (modNCompletedGroupAlgebraTransition (ℓ ^ i.1) G (hij.2.trans hjk.2)).comp
      (modNCompletedGroupAlgebraStageCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ k.1) (G := G) k.2
        (primePow_dvd_primePow (ℓ := ℓ) (hij.trans hjk).1)) := by
          rw [modNCompletedGroupAlgebraStageCoeffMap_comp
            (n := ℓ ^ i.1) (m := ℓ ^ j.1) (k := ℓ ^ k.1) (G := G) (U := k.2)
            (hnm := primePow_dvd_primePow (ℓ := ℓ) hij.1)
            (hmk := primePow_dvd_primePow (ℓ := ℓ) hjk.1)]
    _ =
    primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) (hij.trans hjk) := by
          rw [← primePowerCompletedGroupAlgebraTransition_eq'
            (ℓ := ℓ) (G := G) (hij := hij.trans hjk)]

omit [Fact (0 < ℓ)] in
/-- The inverse system indexed by prime powers and finite quotients. -/
def primePowerCompletedGroupAlgebraSystem :
    InverseSystem (I := PrimePowerCompletedGroupAlgebraIndex G) where
  X := PrimePowerCompletedGroupAlgebraStage ℓ G
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij => primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
  continuous_map := by
    intro i j hij
    let : TopologicalSpace (PrimePowerCompletedGroupAlgebraStage ℓ G i) := ⊥
    let : TopologicalSpace (PrimePowerCompletedGroupAlgebraStage ℓ G j) := ⊥
    let : DiscreteTopology (PrimePowerCompletedGroupAlgebraStage ℓ G j) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (primePowerCompletedGroupAlgebraTransition_id (ℓ := ℓ) (G := G) i)) x
  map_comp := by
    intro i j k hij hjk
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (primePowerCompletedGroupAlgebraTransition_comp (ℓ := ℓ) (G := G) hij hjk)) x

omit [Fact (0 < ℓ)] in
/-- The inverse-limit object of the prime-power finite-stage system. -/
abbrev PrimePowerCompletedGroupAlgebra :=
  (primePowerCompletedGroupAlgebraSystem ℓ G).inverseLimit

omit [Fact (0 < ℓ)] in
/-- The projection from the prime-power completed group algebra to one finite stage. -/
abbrev primePowerCompletedGroupAlgebraProjection (i : PrimePowerCompletedGroupAlgebraIndex G) :
    PrimePowerCompletedGroupAlgebra ℓ G → PrimePowerCompletedGroupAlgebraStage ℓ G i :=
  (primePowerCompletedGroupAlgebraSystem ℓ G).projection i

omit [IsTopologicalGroup G] in
/-- The prime-power group-algebra index family is directed under the componentwise order. -/
theorem directed_primePowerCompletedGroupAlgebraIndex :
    Directed (· ≤ ·) (id : PrimePowerCompletedGroupAlgebraIndex G →
      PrimePowerCompletedGroupAlgebraIndex G) := by
  intro i j
  rcases directed_openNormalSubgroupInClass
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      ProCGroups.FiniteGroupClass.allFinite_formation i.2 j.2 with ⟨U, hiU, hjU⟩
  refine ⟨(max i.1 j.1, U), ?_, ?_⟩
  · exact ⟨le_max_left _ _, hiU⟩
  · exact ⟨le_max_right _ _, hjU⟩

omit [Fact (0 < ℓ)] in
/-- Every transition in the prime-power completed group-algebra system is surjective. -/
theorem primePowerCompletedGroupAlgebraTransition_surjective
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j) :
    Function.Surjective
      (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij) := by
  intro x
  rcases modNCompletedGroupAlgebraStageCoeffMap_surjective
      (n := ℓ ^ i.1) (m := ℓ ^ j.1) (G := G) i.2
      (primePow_dvd_primePow (ℓ := ℓ) hij.1) x with
    ⟨y, hy⟩
  rcases modNCompletedGroupAlgebraTransition_surjective
      (n := ℓ ^ j.1) (G := G) hij.2 y with
    ⟨z, hz⟩
  refine ⟨z, ?_⟩
  rw [primePowerCompletedGroupAlgebraTransition_eq, RingHom.comp_apply, hz, hy]

/-- Every finite-stage projection from the prime-power completed group algebra is surjective. -/
theorem primePowerCompletedGroupAlgebraProjection_surjective
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    Function.Surjective (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i) := by
  let S := primePowerCompletedGroupAlgebraSystem ℓ G
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, TopologicalSpace (S.X i) :=
    fun i => S.topologicalSpace i
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, DiscreteTopology (S.X i) :=
    fun _ => ⟨rfl⟩
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, CompactSpace (S.X i) :=
    fun i => by
      let : Finite (S.X i) := by
        dsimp [S, primePowerCompletedGroupAlgebraSystem]
        infer_instance
      let : Fintype (S.X i) := Fintype.ofFinite _
      infer_instance
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, T2Space (S.X i) :=
    fun _ => inferInstance
  change Function.Surjective (S.projection i)
  exact
    S.surjective_π
      (directed_primePowerCompletedGroupAlgebraIndex (G := G))
      (fun {i j} hij =>
        primePowerCompletedGroupAlgebraTransition_surjective (ℓ := ℓ) (G := G) hij)
      i

end

end FoxDifferential
