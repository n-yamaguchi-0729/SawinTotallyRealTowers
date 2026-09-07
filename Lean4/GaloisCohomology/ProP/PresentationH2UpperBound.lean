import GaloisCohomology.ProP.PresentationH2KernelCharacter

set_option autoImplicit false
/-!
# The presentation upper bound for degree-two continuous cohomology

If the extracted kernel character vanishes, the normalized free-source primitive descends along
the presentation quotient.  Its homogeneous lift is a target primitive, proving injectivity into
the invariant kernel character space and hence the displayed relation-cardinality bound.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CategoryTheory TopRep ContRepresentation
open ProCGroups
open PresentationH2Aux

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {d r : ℕ}
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}

local instance presentationUpperContinuousH1Module
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := H)) :=
  continuousH1ZModModule

namespace PresentationH2Aux

/-- The normalized primitive as a continuous map on the free source. -/
def presentationNormalizedPrimitiveContinuousMap
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2) :
    C(sourceData.carrier, ZMod p) where
  toFun := presentationNormalizedPrimitiveValue P x
  continuous_toFun :=
    ((ContinuousLinearEquiv.ulift :
      ULift.{u} (ZMod p) ≃L[ZMod p] ZMod p).continuous).comp <|
      (((presentationPrimitive P x).1 1).continuous).sub continuous_const

theorem presentationNormalizedPrimitive_factors
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (hx : presentationH2ToInvariantKernelH1 P x = 0) :
    Function.FactorsThrough (presentationNormalizedPrimitiveContinuousMap P x) P.quotient := by
  have hkernel : ∀ n : P.quotient.toMonoidHom.ker,
      presentationNormalizedPrimitiveValue P x n = 0 := by
    intro n
    have h := congrArg
      (fun η : InvariantKernelH1 P ↦ η.1 (Additive.ofMul n)) hx
    change presentationNormalizedPrimitiveValue P x n = 0 at h
    exact h
  intro a b hab
  change P.quotient.toMonoidHom a = P.quotient.toMonoidHom b at hab
  let n : P.quotient.toMonoidHom.ker := ⟨a⁻¹ * b, by
    change P.quotient.toMonoidHom (a⁻¹ * b) = 1
    rw [map_mul, map_inv, hab]
    simp⟩
  have hn : P.quotient (n : sourceData.carrier) = 1 := n.2
  have hmul := presentationNormalizedPrimitive_mul_of_right_kernel P x a n hn
  have habn : a * (n : sourceData.carrier) = b := by
    change a * (a⁻¹ * b) = b
    group
  rw [habn, hkernel n, add_zero] at hmul
  exact hmul.symm

/-- Descend a normalized primitive whose kernel character vanishes to the presentation target. -/
noncomputable def presentationDescendedNormalizedPrimitive
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (hx : presentationH2ToInvariantKernelH1 P x = 0) : C(G, ZMod p) := by
  let q : C(sourceData.carrier, G) := P.quotient.toContinuousMap
  let hq : Topology.IsQuotientMap q :=
    Topology.IsQuotientMap.of_surjective_continuous
      P.quotient_surjective P.quotient.continuous_toFun
  have hfac : Function.FactorsThrough
      (presentationNormalizedPrimitiveContinuousMap P x) q :=
    presentationNormalizedPrimitive_factors P x hx
  exact hq.lift (presentationNormalizedPrimitiveContinuousMap P x) hfac

@[simp]
theorem presentationDescendedNormalizedPrimitive_comp
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (hx : presentationH2ToInvariantKernelH1 P x = 0)
    (f : sourceData.carrier) :
    presentationDescendedNormalizedPrimitive P x hx (P.quotient f) =
      presentationNormalizedPrimitiveValue P x f := by
  let q : C(sourceData.carrier, G) := P.quotient.toContinuousMap
  let hq : Topology.IsQuotientMap q :=
    Topology.IsQuotientMap.of_surjective_continuous
      P.quotient_surjective P.quotient.continuous_toFun
  have hfac : Function.FactorsThrough
      (presentationNormalizedPrimitiveContinuousMap P x) q :=
    presentationNormalizedPrimitive_factors P x hx
  change (hq.lift (presentationNormalizedPrimitiveContinuousMap P x) hfac) (q f) = _
  have h := hq.lift_comp (presentationNormalizedPrimitiveContinuousMap P x) hfac
  exact ContinuousMap.congr_fun h f

/-- The homogeneous target primitive reconstructed from the descended normalized value. -/
noncomputable def presentationDescendedPrimitive
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (hx : presentationH2ToInvariantKernelH1 P x = 0) :
    (Cohomology.trivialZModPCochainsLifted p G).X 1 := by
  let b := presentationDescendedNormalizedPrimitive P x hx
  let t : ULift.{u} (ZMod p) :=
    ULift.up ((presentationPrimitive P x).1 1 1).down
  let σ : C(G, C(G, ULift.{u} (ZMod p))) := ContinuousMap.curry
    ⟨fun gh : G × G ↦ t + ULift.up (b (gh.1⁻¹ * gh.2)),
      continuous_const.add <|
        ((ContinuousLinearEquiv.ulift :
          ULift.{u} (ZMod p) ≃L[ZMod p] ZMod p).symm.continuous).comp <|
            b.continuous_toFun.comp <| by fun_prop⟩
  exact ⟨σ, by
    intro g
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro c
    change t + ULift.up (b ((g⁻¹ * a)⁻¹ * (g⁻¹ * c))) =
      t + ULift.up (b (a⁻¹ * c))
    congr 3
    group⟩

@[simp]
theorem presentationDescendedPrimitive_apply
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (hx : presentationH2ToInvariantKernelH1 P x = 0)
    (g h : G) :
    (presentationDescendedPrimitive P x hx).1 g h =
      ULift.up ((presentationPrimitive P x).1 1 1).down +
        ULift.up (presentationDescendedNormalizedPrimitive P x hx (g⁻¹ * h)) :=
  rfl

theorem presentationDescendedPrimitive_pullback_apply
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (hx : presentationH2ToInvariantKernelH1 P x = 0)
    (f g : sourceData.carrier) :
    (presentationDescendedPrimitive P x hx).1 (P.quotient f) (P.quotient g) =
      (presentationPrimitive P x).1 f g := by
  rw [presentationDescendedPrimitive_apply]
  have hq : (P.quotient f)⁻¹ * P.quotient g = P.quotient (f⁻¹ * g) := by
    change (P.quotient.toMonoidHom f)⁻¹ * P.quotient.toMonoidHom g =
      P.quotient.toMonoidHom (f⁻¹ * g)
    rw [← map_inv]
    exact (map_mul P.quotient.toMonoidHom f⁻¹ g).symm
  let cVal : sourceData.carrier → sourceData.carrier →
      ULift.{u} (ZMod p) :=
    fun a b ↦ (presentationPrimitive P x).1 a b
  rw [hq, presentationDescendedNormalizedPrimitive_comp]
  unfold presentationNormalizedPrimitiveValue
  change
    ULift.up (cVal 1 1).down +
        ULift.up ((cVal 1 (f⁻¹ * g) - cVal 1 1).down) =
      cVal f g
  rw [ULift.up_down]
  have hinv := presentationPrimitive_leftInvariant P x f f g
  change cVal (f⁻¹ * f) (f⁻¹ * g) = cVal f g at hinv
  calc
    _ = cVal 1 (f⁻¹ * g) := by
      apply ULift.ext
      change
        (cVal 1 1).down +
            ((cVal 1 (f⁻¹ * g)).down - (cVal 1 1).down) =
          (cVal 1 (f⁻¹ * g)).down
      abel
    _ = _ := by
      simpa only [inv_mul_cancel] using hinv

theorem presentationDescendedPrimitive_boundary
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (hx : presentationH2ToInvariantKernelH1 P x = 0) :
    ((Cohomology.trivialZModPCochainsLifted p G).d 1 2).hom
        (presentationDescendedPrimitive P x hx) =
      ((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom
        (targetCocycleSection x) := by
  apply Subtype.ext
  ext g₀ g₁ g₂
  obtain ⟨f₀, rfl⟩ := P.quotient_surjective g₀
  obtain ⟨f₁, rfl⟩ := P.quotient_surjective g₁
  obtain ⟨f₂, rfl⟩ := P.quotient_surjective g₂
  have hd := TopRep.homogeneousCochains.d_apply
    (Cohomology.trivialZModPLifted p G) 1
      (presentationDescendedPrimitive P x hx)
  have hdpoint := congrArg (fun τ ↦ τ (P.quotient f₀) (P.quotient f₁) (P.quotient f₂)) hd
  rw [hdpoint]
  simp [TopRep.d_succ, TopRep.d_zero, TopRep.hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun]
  rw [presentationDescendedPrimitive_pullback_apply P x hx,
    presentationDescendedPrimitive_pullback_apply P x hx,
    presentationDescendedPrimitive_pullback_apply P x hx]
  exact presentationPrimitive_boundary_apply P x f₀ f₁ f₂

theorem eq_zero_of_presentationH2ToInvariantKernelH1_eq_zero
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (hx : presentationH2ToInvariantKernelH1 P x = 0) : x = 0 := by
  let K := Cohomology.trivialZModPCochainsLifted p G
  let c : K.X 1 := presentationDescendedPrimitive P x hx
  have hc : (K.d 1 2).hom c = (K.iCycles 2).hom (targetCocycleSection x) :=
    presentationDescendedPrimitive_boundary P x hx
  have hzc : (K.toCycles 1 2).hom c = targetCocycleSection x := by
    apply Cohomology.topModule_mono_injective_lifted (K.iCycles 2)
    calc
      (K.iCycles 2).hom ((K.toCycles 1 2).hom c) = (K.d 1 2).hom c := by
        have hcomp := ConcreteCategory.congr_hom (K.toCycles_i 1 2) c
        exact hcomp
      _ = (K.iCycles 2).hom (targetCocycleSection x) := hc
  have hπ : ContinuousCohomology.π (Cohomology.trivialZModPLifted p G) 2
      (targetCocycleSection x) = 0 := by
    rw [← hzc]
    exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ 1 2) c
  calc
    x = ContinuousCohomology.π (Cohomology.trivialZModPLifted p G) 2
        (targetCocycleSection x) := (targetCocycleSection_π x).symm
    _ = 0 := hπ

end PresentationH2Aux

/-- The presentation kernel character remembers every degree-two target class. -/
theorem presentationH2ToInvariantKernelH1_injective
    (P : FiniteProPPresentation p d r sourceData G) :
    Function.Injective (presentationH2ToInvariantKernelH1 P) := by
  intro x y hxy
  have hzero : presentationH2ToInvariantKernelH1 P (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp
    (eq_zero_of_presentationH2ToInvariantKernelH1_eq_zero P (x - y) hzero)

/-- Degree-two continuous cohomology is finite-dimensional for a finite presentation target. -/
theorem presentationH2_finiteDimensional
    (P : FiniteProPPresentation p d r sourceData G) :
    FiniteDimensional (ZMod p)
      (Cohomology.continuousCohomologyZModPLifted p G 2) := by
  let : FiniteDimensional (ZMod p) (InvariantKernelH1 P) :=
    invariantKernelH1_finiteDimensional P
  exact FiniteDimensional.of_injective (presentationH2ToInvariantKernelH1 P)
    (presentationH2ToInvariantKernelH1_injective P)

/-- The degree-two mod-`p` cohomology rank is at most the displayed relation count. -/
theorem finrank_continuousCohomologyZModPLifted_degree_two_le_relationCard
    (P : FiniteProPPresentation p d r sourceData G) :
    Module.finrank (ZMod p)
        (Cohomology.continuousCohomologyZModPLifted p G 2) ≤ r := by
  let : FiniteDimensional (ZMod p) (InvariantKernelH1 P) :=
    invariantKernelH1_finiteDimensional P
  let : FiniteDimensional (ZMod p)
      (Cohomology.continuousCohomologyZModPLifted p G 2) :=
    presentationH2_finiteDimensional P
  exact (presentationH2ToInvariantKernelH1 P).finrank_le_finrank_of_injective
      (presentationH2ToInvariantKernelH1_injective P) |>.trans
    (finrank_invariantKernelH1_le_relationCard P)

end

end ClassFieldTower.ProP
