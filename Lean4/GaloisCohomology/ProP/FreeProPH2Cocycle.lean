import GaloisCohomology.ProP.ContinuousH1Bridge

set_option autoImplicit false
/-!
# Normalized cocycles and primitives for free pro-p degree-two cohomology

This helper leaf converts homogeneous degree-two cocycles with lifted trivial `ZMod p`
coefficients into normalized inhomogeneous cocycles and constructs the homogeneous
degree-one primitive associated to a continuous coboundary.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CategoryTheory TopRep ContRepresentation

namespace FreeProPH2Cocycle

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

/-- The universe-lifted coefficient module used by the cocycle formulas. -/
abbrev A (p : ℕ) := ULift.{u} (ZMod p)

private def cocycleValue
    (z : Cohomology.trivialZModPCocyclesLifted p F 2)
    (x₀ x₁ x₂ : F) : A p :=
  (((Cohomology.trivialZModPCochainsLifted p F).iCycles 2).hom z).1 x₀ x₁ x₂

/-- The normalized inhomogeneous cocycle associated to a homogeneous
degree-two cocycle. -/
def normalizedCocycle
    (z : Cohomology.trivialZModPCocyclesLifted p F 2) (g h : F) : A p :=
  cocycleValue z 1 g (g * h) - cocycleValue z 1 1 1

omit [Fact p.Prime] in
theorem normalizedCocycle_continuous
    [LocallyCompactSpace F]
    (z : Cohomology.trivialZModPCocyclesLifted p F 2) :
    Continuous fun gh : F × F => normalizedCocycle z gh.1 gh.2 := by
  let X := Cohomology.trivialZModPLifted p F
  let z₀ := ((Cohomology.trivialZModPCochainsLifted p F).iCycles 2).hom z
  change (TopRep.resolutionX X 3).ρ.invariants at z₀
  let zfun : C(F, C(F, C(F, A p))) := z₀.1
  change Continuous fun gh : F × F => zfun 1 gh.1 (gh.1 * gh.2) - zfun 1 1 1
  fun_prop

omit [Fact p.Prime] in
private theorem homogeneousCocycleEquation
    (z : Cohomology.trivialZModPCocyclesLifted p F 2)
    (x₀ x₁ x₂ x₃ : F) :
    (((Cohomology.trivialZModPCochainsLifted p F).iCycles 2).hom z).1 x₁ x₂ x₃ -
        (((Cohomology.trivialZModPCochainsLifted p F).iCycles 2).hom z).1 x₀ x₂ x₃ +
        (((Cohomology.trivialZModPCochainsLifted p F).iCycles 2).hom z).1 x₀ x₁ x₃ -
      (((Cohomology.trivialZModPCochainsLifted p F).iCycles 2).hom z).1 x₀ x₁ x₂ = 0 := by
  let X := Cohomology.trivialZModPLifted p F
  let C := Cohomology.trivialZModPCochainsLifted p F
  let z₀ : C.X 2 := (C.iCycles 2).hom z
  have hz : (C.d 2 3).hom z₀ = 0 := by
    have h := congrArg (fun f ↦ TopModuleCat.Hom.hom f z) (C.iCycles_d 2 3)
    simpa only [z₀, TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply,
      TopModuleCat.hom_zero, _root_.zero_apply] using h
  have hzEval := congrArg (fun τ : C.X 3 => τ.1 x₀ x₁ x₂ x₃) hz
  have hd := TopRep.homogeneousCochains.d_apply X 2 z₀
  have hdEval := congrArg (fun τ => τ x₀ x₁ x₂ x₃) hd
  rw [hdEval] at hzEval
  simp [X, C, z₀, d_succ, d_zero, hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun] at hzEval
  abel_nf at hzEval ⊢
  exact hzEval

omit [Fact p.Prime] in
private theorem homogeneousCocycle_leftInvariant
    (z : Cohomology.trivialZModPCocyclesLifted p F 2)
    (g x₀ x₁ x₂ : F) :
    (((Cohomology.trivialZModPCochainsLifted p F).iCycles 2).hom z).1
        (g * x₀) (g * x₁) (g * x₂) =
      (((Cohomology.trivialZModPCochainsLifted p F).iCycles 2).hom z).1
        x₀ x₁ x₂ := by
  let X := Cohomology.trivialZModPLifted p F
  let C := Cohomology.trivialZModPCochainsLifted p F
  let z₀ := (C.iCycles 2).hom z
  change (TopRep.resolutionX X 3).ρ.invariants at z₀
  have h := congrArg (fun τ => τ (g * x₀) (g * x₁) (g * x₂)) (z₀.2 g)
  change z₀.1 (g⁻¹ * (g * x₀)) (g⁻¹ * (g * x₁)) (g⁻¹ * (g * x₂)) =
    z₀.1 (g * x₀) (g * x₁) (g * x₂) at h
  simpa only [inv_mul_cancel_left] using h.symm

omit [Fact p.Prime] in
theorem normalizedCocycle_cocycle
    (z : Cohomology.trivialZModPCocyclesLifted p F 2)
    (g h k : F) :
    normalizedCocycle z g h + normalizedCocycle z (g * h) k =
      normalizedCocycle z h k + normalizedCocycle z g (h * k) := by
  have hz := homogeneousCocycleEquation z 1 g (g * h) (g * h * k)
  have hinv := homogeneousCocycle_leftInvariant z g 1 h (h * k)
  simp only [mul_one, mul_assoc] at hz hinv
  rw [hinv] at hz
  let q (x y w : F) : A p :=
    (((Cohomology.trivialZModPCochainsLifted p F).iCycles 2).hom z).1 x y w
  let a := q 1 h (h * k)
  let b := q 1 (g * h) (g * (h * k))
  let c := q 1 g (g * (h * k))
  let d := q 1 g (g * h)
  let t := q 1 1 1
  change a - b + c - d = 0 at hz
  have hraw : d + b = a + c := by
    have hzero : d + b - (a + c) = 0 := by
      calc
        d + b - (a + c) = -(a - b + c - d) := by abel
        _ = 0 := by rw [hz]; simp
    exact sub_eq_zero.mp hzero
  unfold normalizedCocycle
  simp only [mul_assoc]
  change (d - t) + (b - t) = (a - t) + (c - t)
  calc
    (d - t) + (b - t) = (d + b) - (t + t) := by abel
    _ = (a + c) - (t + t) := by rw [hraw]
    _ = (a - t) + (c - t) := by abel

omit [Fact p.Prime] in
theorem normalizedCocycle_one_left
    (z : Cohomology.trivialZModPCocyclesLifted p F 2) (h : F) :
    normalizedCocycle z 1 h = 0 := by
  have hz := homogeneousCocycleEquation z 1 1 1 h
  simp only at hz
  unfold normalizedCocycle
  simp only [one_mul]
  abel_nf at hz ⊢
  exact hz

omit [Fact p.Prime] in
theorem normalizedCocycle_one_right
    (z : Cohomology.trivialZModPCocyclesLifted p F 2) (g : F) :
    normalizedCocycle z g 1 = 0 := by
  have hc := normalizedCocycle_cocycle z g 1 1
  rw [one_mul, mul_one, normalizedCocycle_one_left] at hc
  have hc' : normalizedCocycle z g 1 + normalizedCocycle z g 1 =
      normalizedCocycle z g 1 + 0 := by simpa using hc
  exact add_left_cancel hc'

omit [Fact p.Prime] in
private theorem homogeneousCocycle_eq_normalized
    (z : Cohomology.trivialZModPCocyclesLifted p F 2)
    (x₀ x₁ x₂ : F) :
    cocycleValue z x₀ x₁ x₂ = cocycleValue z 1 1 1 +
        normalizedCocycle z (x₀⁻¹ * x₁) (x₁⁻¹ * x₂) := by
  have hinv := homogeneousCocycle_leftInvariant z x₀⁻¹ x₀ x₁ x₂
  have h02 : (x₀⁻¹ * x₁) * (x₁⁻¹ * x₂) = x₀⁻¹ * x₂ := by group
  simp only [inv_mul_cancel] at hinv
  unfold normalizedCocycle cocycleValue
  rw [h02]
  rw [← hinv]
  abel

/-- The homogeneous degree-one cochain associated to a continuous primitive
of the normalized cocycle. -/
def homogeneousPrimitive
    [LocallyCompactSpace F]
    (z : Cohomology.trivialZModPCocyclesLifted p F 2)
    (b : C(F, A p)) :
    (Cohomology.trivialZModPCochainsLifted p F).X 1 := by
  let a₀ : A p :=
    cocycleValue z 1 1 1
  let σ : C(F, C(F, A p)) := ContinuousMap.curry
    ⟨fun xy : F × F => a₀ - b (xy.1⁻¹ * xy.2),
      continuous_const.sub <| b.continuous_toFun.comp <| by fun_prop⟩
  exact ⟨σ, by
    intro g
    apply ContinuousMap.ext
    intro x
    apply ContinuousMap.ext
    intro y
    change a₀ - b ((g⁻¹ * x)⁻¹ * (g⁻¹ * y)) = a₀ - b (x⁻¹ * y)
    congr 2
    group⟩

omit [Fact p.Prime] in
@[simp]
private theorem homogeneousPrimitive_apply
    [LocallyCompactSpace F]
    (z : Cohomology.trivialZModPCocyclesLifted p F 2)
    (b : C(F, A p)) (x y : F) :
    (((homogeneousPrimitive z b).1 : C(F, C(F, A p))) x y) =
      cocycleValue z 1 1 1 - b (x⁻¹ * y) :=
  rfl

omit [Fact p.Prime] in
theorem homogeneousPrimitive_boundary
    [LocallyCompactSpace F]
    (z : Cohomology.trivialZModPCocyclesLifted p F 2)
    (b : C(F, A p))
    (hb : ∀ g h, b (g * h) = b g + b h + normalizedCocycle z g h) :
    ((Cohomology.trivialZModPCochainsLifted p F).d 1 2).hom
        (homogeneousPrimitive z b) =
      ((Cohomology.trivialZModPCochainsLifted p F).iCycles 2).hom z := by
  let X := Cohomology.trivialZModPLifted p F
  let C := Cohomology.trivialZModPCochainsLifted p F
  let t : C.X 1 := homogeneousPrimitive z b
  change (C.d 1 2).hom t = (C.iCycles 2).hom z
  apply Subtype.ext
  ext x₀ x₁ x₂
  have hd := TopRep.homogeneousCochains.d_apply X 1 t
  have hdpoint := congrArg (fun τ => τ x₀ x₁ x₂) hd
  rw [hdpoint]
  simp [X, C, t, d_succ, d_zero, hom_sub, ContIntertwiningMap.sub_apply,
    coind₁ι_toFun, coind₁Map_toFun]
  rw [homogeneousPrimitive_apply z b x₁ x₂,
    homogeneousPrimitive_apply z b x₀ x₂,
    homogeneousPrimitive_apply z b x₀ x₁]
  change _ = cocycleValue z x₀ x₁ x₂
  have hprod : (x₀⁻¹ * x₁) * (x₁⁻¹ * x₂) = x₀⁻¹ * x₂ := by group
  have hb' := hb (x₀⁻¹ * x₁) (x₁⁻¹ * x₂)
  rw [hprod] at hb'
  have hcalc :
      (cocycleValue z 1 1 1 - b (x₁⁻¹ * x₂)) -
          ((cocycleValue z 1 1 1 - b (x₀⁻¹ * x₂)) -
            (cocycleValue z 1 1 1 - b (x₀⁻¹ * x₁))) =
        cocycleValue z 1 1 1 +
          normalizedCocycle z (x₀⁻¹ * x₁) (x₁⁻¹ * x₂) := by
    rw [hb']
    abel
  rw [homogeneousCocycle_eq_normalized z x₀ x₁ x₂]
  exact hcalc

end

end FreeProPH2Cocycle

end ClassFieldTower.ProP
