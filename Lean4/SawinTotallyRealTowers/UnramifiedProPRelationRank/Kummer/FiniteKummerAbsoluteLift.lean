import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteUnitBoundaryMuPPrimitive
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerMuPCoefficients
import GaloisCohomology.ProP.H2CocycleExtensionPullback

set_option autoImplicit false
/-!
# Absolute lifts of finite Kummer cocycle extensions

A finite field-unit primitive is first corrected, by the proved Hilbert-90
construction, to a continuous natural `mu_p` primitive.  The existing
primitive-root trivialization then turns it into a lifted `ZMod p`
primitive.  Its negative coefficient coordinate gives an explicit
continuous homomorphism into the finite cocycle extension.

The final endpoint accepts exactly the ordinary field-unit boundary
supplied by the supported-idele and degree-two injection results.  The
normalized cocycle is packaged here as an ordinary two-cocycle; no
unproved comparison or existence hypothesis is introduced.
No new instances are introduced.
-/

open scoped Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory ClassFieldTower.ProP FreeProPH2Cocycle

variable (K : Type) [Field K] [CharZero K]
variable (p : ℕ+) [Fact (p : ℕ).Prime]
variable (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))

omit [CharZero K] in
/-- Continuous restriction from the absolute Galois group to an actual
finite Galois intermediate field. -/
def absoluteFiniteGaloisRestriction :
    Field.absoluteGaloisGroup K →ₜ* Gal(E/K) where
  toFun s := AlgEquiv.restrictNormalHom E.toIntermediateField
    (absoluteGaloisGroupContinuousMulEquiv K s)
  map_one' := by simp
  map_mul' s t := by simp
  continuous_toFun :=
    (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField).comp
      (absoluteGaloisGroupContinuousMulEquiv K).continuous

/-- A finite unit primitive yields a continuous lifted `ZMod p` primitive
when the base contains the supplied primitive root. -/
theorem exists_absoluteZModP_primitive_of_finiteKummerUnit_boundary
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (c : Gal(E/K) → Gal(E/K) → ULift.{0} (ZMod (p : ℕ)))
    (b : Gal(E/K) → Eˣ)
    (hb : ∀ s t : Gal(E/K),
      Units.map s (b t) * b s / b (s * t) =
        (finiteKummerCoefficientAddHom K E p hmu (c s t)).toMul) :
    ∃ a : C(Field.absoluteGaloisGroup K, ULift.{0} (ZMod (p : ℕ))),
      ∀ s t, a t + a s - a (s * t) =
        c (absoluteFiniteGaloisRestriction K E s)
          (absoluteFiniteGaloisRestriction K E t) := by
  let cm : Gal(E/K) → Gal(E/K) → nthRootsSubgroup E (p : ℕ) := fun s t =>
    ⟨(finiteKummerCoefficientAddHom K E p hmu (c s t)).toMul,
      finiteKummerCoefficientAddHom_pow_eq_one K E p hmu (c s t)⟩
  obtain ⟨a, ha⟩ := exists_absoluteMuP_primitive_of_finiteUnit_boundary
    K (p : ℕ) E cm b hb
  let e := absoluteMuPContinuousLinearEquivZMod K (p : ℕ) hmu
  let f : C(Field.absoluteGaloisGroup K, ULift.{0} (ZMod (p : ℕ))) :=
    ⟨fun s => ULift.up (e (a s)),
      (show Continuous (fun z : ZMod (p : ℕ) => ULift.up.{0} z) from
        continuous_of_discreteTopology).comp
          (e.continuous.comp a.continuous)⟩
  refine ⟨f, ?_⟩
  intro s t
  apply ULift.ext
  change e (a t) + e (a s) - e (a (s * t)) =
    (c (absoluteFiniteGaloisRestriction K E s)
      (absoluteFiniteGaloisRestriction K E t)).down
  apply e.symm.injective
  simp only [map_sub, map_add, ContinuousLinearEquiv.symm_apply_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  change (a t).toMul.1 * (a s).toMul.1 / (a (s * t)).toMul.1 =
    ((absoluteMuPLinearEquivZMod K (p : ℕ) hmu).symm
      (c (absoluteFiniteGaloisRestriction K E s)
        (absoluteFiniteGaloisRestriction K E t)).down).toMul.1
  rw [absoluteMuPLinearEquivZMod_symm_coe K p hmu]
  rw [← finiteKummerCoefficientAddHom_map K p E.val hmu]
  have hfixed := congrArg (fun x : AbsoluteMuP K (p : ℕ) => x.toMul.1)
    (absoluteMuPAction_eq_self_of_primitiveRoots K (p : ℕ) hmu s (a t))
  change (absoluteGaloisGroupContinuousMulEquiv K s) • (a t).toMul.1 =
    (a t).toMul.1 at hfixed
  have h := ha s t
  rw [hfixed] at h
  exact h

/-- The corrected primitive gives a genuine continuous lift into the
cocycle extension, with the prescribed finite restriction as projection. -/
theorem exists_absoluteLift_of_finiteKummerUnit_boundary
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (z : Cohomology.trivialZModPCocyclesLifted (p : ℕ) Gal(E/K) 2)
    (b : Gal(E/K) → Eˣ)
    (hb : ∀ s t : Gal(E/K),
      Units.map s (b t) * b s / b (s * t) =
        (finiteKummerCoefficientAddHom K E p hmu
          (normalizedCocycle z s t)).toMul) :
    ∃ s : Field.absoluteGaloisGroup K →ₜ* H2CocycleExtension z,
      (H2CocycleExtension.projection z).comp s =
        absoluteFiniteGaloisRestriction K E := by
  obtain ⟨a, ha⟩ := exists_absoluteZModP_primitive_of_finiteKummerUnit_boundary
    K p E hmu (normalizedCocycle z) b hb
  let r := absoluteFiniteGaloisRestriction K E
  let s : Field.absoluteGaloisGroup K →ₜ* H2CocycleExtension z :=
    { toFun := fun g => ⟨-a g, r g⟩
      map_one' := by
        apply H2CocycleExtension.ext
        · change -a 1 = 0
          have h := ha 1 1
          rw [map_one (absoluteFiniteGaloisRestriction K E),
            normalizedCocycle_one_left, one_mul] at h
          have hz : a 1 = 0 := by simpa only [add_sub_cancel_right] using h
          rw [hz, neg_zero]
        · exact r.map_one
      map_mul' g h := by
        apply H2CocycleExtension.ext
        · change -a (g * h) = -a g + -a h + normalizedCocycle z (r g) (r h)
          rw [← ha g h]
          abel
        · exact r.map_mul g h
      continuous_toFun := by
        rw [continuous_induced_rng]
        exact a.continuous.neg.prodMk r.continuous_toFun }
  exact ⟨s, rfl⟩

omit [CharZero K] in
/-- The normalized continuous cocycle, viewed in the ordinary pair-shaped
degree-two cochain model used by finite Kummer coefficient change. -/
def normalizedFiniteKummerTwoCocycle
    (z : Cohomology.trivialZModPCocyclesLifted (p : ℕ) Gal(E/K) 2) :
    groupCohomology.cocycles₂
      (Rep.trivial ℤ Gal(E/K) (ULift.{0} (ZMod (p : ℕ)))) := by
  refine ⟨fun gh => normalizedCocycle z gh.1 gh.2, ?_⟩
  apply (groupCohomology.mem_cocycles₂_iff _).mpr
  intro g h k
  change normalizedCocycle z (g * h) k + normalizedCocycle z g h =
    normalizedCocycle z h k + normalizedCocycle z g (h * k)
  rw [add_comm]
  exact normalizedCocycle_cocycle z g h k

/-- A boundary in the actual field-unit representation supplies the
continuous absolute lift of the original central cocycle extension. -/
theorem exists_absoluteLift_of_finiteKummerTwoCocycle_boundary
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (z : Cohomology.trivialZModPCocyclesLifted (p : ℕ) Gal(E/K) 2)
    (b : Gal(E/K) → Additive Eˣ)
    (hb : (groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits K E)).hom b =
      (groupCohomology.mapCocycles₂ (MonoidHom.id Gal(E/K))
        (finiteKummerCoefficientRepHom K E p hmu)
        (normalizedFiniteKummerTwoCocycle K p E z)).1) :
    ∃ s : Field.absoluteGaloisGroup K →ₜ* H2CocycleExtension z,
      (H2CocycleExtension.projection z).comp s =
        absoluteFiniteGaloisRestriction K E := by
  apply exists_absoluteLift_of_finiteKummerUnit_boundary K p E hmu z
    (fun s => (b s).toMul)
  intro s t
  have h := congrArg Additive.toMul (congrFun hb (s, t))
  change Units.map s (b t).toMul / (b (s * t)).toMul * (b s).toMul =
    (finiteKummerCoefficientAddHom K E p hmu (normalizedCocycle z s t)).toMul at h
  simpa only [div_mul_eq_mul_div] using h

end ClassFieldTower.Martinet.Shafarevich
