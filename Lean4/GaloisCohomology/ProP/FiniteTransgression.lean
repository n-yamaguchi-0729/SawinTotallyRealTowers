import GaloisCohomology.ProP.TrivialZModP
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

set_option autoImplicit false
/-!
# Finite transgression factor sets

An ambient-conjugation-invariant ZMod p character on a normal subgroup determines the usual
factor-set homogeneous two-cocycle on the discrete quotient, and hence a continuous degree-two
cohomology class with universe-lifted trivial coefficients.
-/

open CategoryTheory TopRep ContRepresentation
open scoped Topology

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

variable {p : ℕ}
variable {P : Type u} [Group P]

local instance quotientTopology (N : Subgroup P) : TopologicalSpace (P ⧸ N) := ⊥
local instance quotientDiscrete (N : Subgroup P) : DiscreteTopology (P ⧸ N) :=
  discreteTopology_bot _

/-- The factor of the chosen quotient representatives. -/
noncomputable def quotientSectionFactor (N : Subgroup P) [N.Normal]
    (q r : P ⧸ N) : N :=
  ⟨Quotient.out q * Quotient.out r * (Quotient.out (q * r))⁻¹, by
    rw [← QuotientGroup.eq_one_iff]
    simp⟩

@[simp]
theorem quotientSectionFactor_apply (N : Subgroup P) [N.Normal]
    (q r : P ⧸ N) :
    (quotientSectionFactor N q r : P) =
      Quotient.out q * Quotient.out r * (Quotient.out (q * r))⁻¹ :=
  rfl

theorem quotientSectionFactor_cocycle_identity (N : Subgroup P) [N.Normal]
    (q r s : P ⧸ N) :
    quotientSectionFactor N q r * quotientSectionFactor N (q * r) s =
      MulAut.conjNormal (Quotient.out q) (quotientSectionFactor N r s) *
        quotientSectionFactor N q (r * s) := by
  apply Subtype.ext
  simp [quotientSectionFactor]
  group

/-- The additive factor set obtained by evaluating an invariant character. -/
noncomputable def transgressionFactor (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (q r : P ⧸ N) : ZMod p :=
  (χ (quotientSectionFactor N q r)).toAdd

theorem transgressionFactor_cocycle
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (hχ : ∀ (g : P) (n : N), χ (MulAut.conjNormal g n) = χ n)
    (q r s : P ⧸ N) :
    transgressionFactor N χ r s - transgressionFactor N χ (q * r) s +
        transgressionFactor N χ q (r * s) - transgressionFactor N χ q r = 0 := by
  have hfac := quotientSectionFactor_cocycle_identity N q r s
  have hmap := congrArg (fun n : N ↦ χ n) hfac
  simp only [map_mul] at hmap
  rw [hχ (Quotient.out q) (quotientSectionFactor N r s)] at hmap
  have hadd := congrArg Multiplicative.toAdd hmap
  change transgressionFactor N χ q r + transgressionFactor N χ (q * r) s =
    transgressionFactor N χ r s + transgressionFactor N χ q (r * s) at hadd
  calc
    transgressionFactor N χ r s - transgressionFactor N χ (q * r) s +
          transgressionFactor N χ q (r * s) - transgressionFactor N χ q r =
        (transgressionFactor N χ r s + transgressionFactor N χ q (r * s)) -
          (transgressionFactor N χ q r + transgressionFactor N χ (q * r) s) := by
            abel
    _ = 0 := by rw [← hadd]; simp

/-- The homogeneous degree-two cochain associated to a finite quotient factor set. -/
noncomputable def transgressionHomogeneousCochain
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p))) :
    (TopRep.homogeneousCochains
      (trivialZModPLifted (p := p) (P ⧸ N))).X 2 := by
  let σ : C(P ⧸ N, C(P ⧸ N, C(P ⧸ N, ULift.{u} (ZMod p)))) :=
    ⟨fun a ↦
      ⟨fun b ↦
        ⟨fun c ↦ ULift.up
            (transgressionFactor N χ (a⁻¹ * b) (b⁻¹ * c)),
          continuous_of_discreteTopology⟩,
        continuous_of_discreteTopology⟩,
      continuous_of_discreteTopology⟩
  exact ⟨σ, by
    intro g
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b
    apply ContinuousMap.ext
    intro c
    change ULift.up
        (transgressionFactor N χ ((g⁻¹ * a)⁻¹ * (g⁻¹ * b))
          ((g⁻¹ * b)⁻¹ * (g⁻¹ * c))) =
      ULift.up (transgressionFactor N χ (a⁻¹ * b) (b⁻¹ * c))
    have hab : (g⁻¹ * a)⁻¹ * (g⁻¹ * b) = a⁻¹ * b := by group
    have hbc : (g⁻¹ * b)⁻¹ * (g⁻¹ * c) = b⁻¹ * c := by group
    rw [hab, hbc]⟩

@[simp]
theorem transgressionHomogeneousCochain_apply
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (a b c : P ⧸ N) :
    (transgressionHomogeneousCochain N χ).1 a b c =
      ULift.up (transgressionFactor N χ (a⁻¹ * b) (b⁻¹ * c)) :=
  rfl

theorem transgressionHomogeneousCochain_mem_cycles
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (hχ : ∀ (g : P) (n : N), χ (MulAut.conjNormal g n) = χ n) :
    ((TopRep.homogeneousCochains
      (trivialZModPLifted (p := p) (P ⧸ N))).d 2 3).hom
        (transgressionHomogeneousCochain N χ) = 0 := by
  change _ =
    (0 : (TopRep.resolutionX (trivialZModPLifted (p := p) (P ⧸ N)) 4).ρ.invariants)
  apply Subtype.ext
  ext a b c d
  have hd := TopRep.homogeneousCochains.d_apply
    (trivialZModPLifted (p := p) (P ⧸ N)) 2
      (transgressionHomogeneousCochain N χ)
  have hdabcd := congrArg (fun τ ↦ τ a b c d) hd
  rw [hdabcd]
  simp [TopRep.d_succ, TopRep.d_zero, TopRep.hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun]
  dsimp only [transgressionHomogeneousCochain]
  let e : ULift.{u} (ZMod p) ≃ₗ[ZMod p] ZMod p := ULift.moduleEquiv
  let C := transgressionFactor N χ (b⁻¹ * c) (c⁻¹ * d)
  let D := transgressionFactor N χ (a⁻¹ * c) (c⁻¹ * d)
  let E := transgressionFactor N χ (a⁻¹ * b) (b⁻¹ * d)
  let A := transgressionFactor N χ (a⁻¹ * b) (b⁻¹ * c)
  have hbase : C - D + E - A = 0 := by
    dsimp only [C, D, E, A]
    simpa only [show (a⁻¹ * b) * (b⁻¹ * c) = a⁻¹ * c by group,
      show (b⁻¹ * c) * (c⁻¹ * d) = b⁻¹ * d by group] using
      transgressionFactor_cocycle N χ hχ (a⁻¹ * b) (b⁻¹ * c) (c⁻¹ * d)
  change e.symm C - (e.symm D - (e.symm E - e.symm A)) = 0
  calc
    e.symm C - (e.symm D - (e.symm E - e.symm A)) =
        e.symm (C - D + E - A) := by
          simp only [map_sub, map_add]
          abel
    _ = e.symm 0 := congrArg e.symm hbase
    _ = 0 := map_zero e.symm

/-- Construct a continuous homogeneous cocycle from an element killed by the next differential. -/
noncomputable def homogeneousCocycleOfElement
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : TopRep.{u} (ZMod p) G) (n : ℕ)
    (x : (TopRep.homogeneousCochains A).X n)
    (hx : ((TopRep.homogeneousCochains A).d n (n + 1)).hom x = 0) :
    ContinuousCohomology.cocycles A n := by
  let B := trivialZModPLifted p G
  let K := TopRep.homogeneousCochains A
  let scalarDown : B.V →L[ZMod p] ZMod p := by
    change ULift.{u} (ZMod p) →L[ZMod p] ZMod p
    exact
      { toLinearMap := (ULift.moduleEquiv (R := ZMod p) :
          ULift.{u} (ZMod p) ≃ₗ[ZMod p] ZMod p).toLinearMap
        cont := continuous_of_discreteTopology }
  let k : TopModuleCat.of (ZMod p) B.V ⟶ K.X n :=
    TopModuleCat.ofHom (scalarDown.smulRight x)
  have hk : k ≫ K.d n (n + 1) = 0 := by
    ext r
    change ((K.d n (n + 1)).hom) (r.down • x) = 0
    rw [map_smul, hx, smul_zero]
  let one : B.V := by
    change ULift.{u} (ZMod p)
    exact ULift.up 1
  exact K.liftCycles k (n + 1) (by simp) hk one

@[simp]
theorem iCycles_homogeneousCocycleOfElement
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : TopRep.{u} (ZMod p) G) (n : ℕ)
    (x : (TopRep.homogeneousCochains A).X n)
    (hx : ((TopRep.homogeneousCochains A).d n (n + 1)).hom x = 0) :
    (TopRep.homogeneousCochains A).iCycles n
        (homogeneousCocycleOfElement A n x hx) = x := by
  let B := trivialZModPLifted p G
  let K := TopRep.homogeneousCochains A
  let scalarDown : B.V →L[ZMod p] ZMod p := by
    change ULift.{u} (ZMod p) →L[ZMod p] ZMod p
    exact
      { toLinearMap := (ULift.moduleEquiv (R := ZMod p) :
          ULift.{u} (ZMod p) ≃ₗ[ZMod p] ZMod p).toLinearMap
        cont := continuous_of_discreteTopology }
  let k : TopModuleCat.of (ZMod p) B.V ⟶ K.X n :=
    TopModuleCat.ofHom (scalarDown.smulRight x)
  have hk : k ≫ K.d n (n + 1) = 0 := by
    ext r
    change ((K.d n (n + 1)).hom) (r.down • x) = 0
    rw [map_smul, hx, smul_zero]
  let one : B.V := by
    change ULift.{u} (ZMod p)
    exact ULift.up 1
  have h := K.liftCycles_i k (n + 1) (by simp) hk
  have h1 := ConcreteCategory.congr_hom h one
  have h2 :
      (K.iCycles n).hom ((K.liftCycles k (n + 1) (by simp) hk).hom one) =
        k.hom one := by
    change ((K.liftCycles k (n + 1) (by simp) hk ≫ K.iCycles n).hom) one = k.hom one
    exact h1
  change (K.iCycles n) (K.liftCycles k (n + 1) (by simp) hk one) = x
  rw [h2]
  change (1 : ZMod p) • x = x
  simp

/-- The factor-set cochain as a continuous homogeneous degree-two cocycle. -/
noncomputable def transgressionHomogeneousCocycle
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (hχ : ∀ (g : P) (n : N), χ (MulAut.conjNormal g n) = χ n) :
    ContinuousCohomology.cocycles
      (trivialZModPLifted (p := p) (P ⧸ N)) 2 :=
  homogeneousCocycleOfElement (trivialZModPLifted (p := p) (P ⧸ N)) 2
    (transgressionHomogeneousCochain N χ)
    (transgressionHomogeneousCochain_mem_cycles N χ hχ)

@[simp]
theorem iCycles_transgressionHomogeneousCocycle
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (hχ : ∀ (g : P) (n : N), χ (MulAut.conjNormal g n) = χ n) :
    (TopRep.homogeneousCochains
      (trivialZModPLifted (p := p) (P ⧸ N))).iCycles 2
        (transgressionHomogeneousCocycle N χ hχ) =
      transgressionHomogeneousCochain N χ :=
  iCycles_homogeneousCocycleOfElement _ _ _ _

/-- The continuous degree-two class of the finite quotient factor set. -/
noncomputable def finiteTransgressionClass
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (hχ : ∀ (g : P) (n : N), χ (MulAut.conjNormal g n) = χ n) :
    continuousCohomology 2 (trivialZModPLifted (p := p) (P ⧸ N)) :=
  ContinuousCohomology.π (trivialZModPLifted (p := p) (P ⧸ N)) 2
    (transgressionHomogeneousCocycle N χ hχ)

end

end ClassFieldTower.Cohomology
