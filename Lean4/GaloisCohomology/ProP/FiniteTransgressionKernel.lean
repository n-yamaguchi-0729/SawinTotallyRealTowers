import GaloisCohomology.ProP.FiniteTransgression

set_option autoImplicit false
/-!
# Kernel exactness for finite transgression

If the explicit factor-set class of an invariant character vanishes, an elementwise boundary
calculation constructs an extension of that character to the ambient group.  This is the kernel
half of the low-degree transgression exact sequence needed for relation-rank comparison.
-/

open CategoryTheory TopRep ContRepresentation
open scoped Topology

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

variable {p : ℕ}
variable {P : Type u} [Group P]

local instance kernelQuotientTopology (N : Subgroup P) : TopologicalSpace (P ⧸ N) := ⊥
local instance kernelQuotientDiscrete (N : Subgroup P) : DiscreteTopology (P ⧸ N) :=
  discreteTopology_bot _

/-- The kernel residue left after removing the chosen quotient representative. -/
noncomputable def quotientSectionResidue (N : Subgroup P) [N.Normal]
    (g : P) : N :=
  ⟨g * (Quotient.out (QuotientGroup.mk' N g : P ⧸ N))⁻¹, by
    rw [← QuotientGroup.eq_one_iff]
    simp⟩

@[simp]
theorem quotientSectionResidue_apply (N : Subgroup P) [N.Normal]
    (g : P) :
    (quotientSectionResidue N g : P) =
      g * (Quotient.out (QuotientGroup.mk' N g : P ⧸ N))⁻¹ :=
  rfl

/-- Multiplication of residues differs by conjugation and the quotient factor set. -/
theorem quotientSectionResidue_mul_identity (N : Subgroup P) [N.Normal]
    (g h : P) :
    quotientSectionResidue N g *
          MulAut.conjNormal
            (Quotient.out (QuotientGroup.mk' N g : P ⧸ N))
            (quotientSectionResidue N h) *
        quotientSectionFactor N (QuotientGroup.mk' N g) (QuotientGroup.mk' N h) =
      quotientSectionResidue N (g * h) := by
  apply Subtype.ext
  simp [quotientSectionResidue, quotientSectionFactor]
  group

/-- Applying an invariant character to the residue multiplication identity. -/
theorem character_quotientSectionResidue_mul
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (hχ : ∀ (g : P) (n : N), χ (MulAut.conjNormal g n) = χ n)
    (g h : P) :
    (χ (quotientSectionResidue N (g * h))).toAdd =
      (χ (quotientSectionResidue N g)).toAdd +
        (χ (quotientSectionResidue N h)).toAdd +
          transgressionFactor N χ (QuotientGroup.mk' N g) (QuotientGroup.mk' N h) := by
  have hid := quotientSectionResidue_mul_identity N g h
  have hmap := congrArg (fun n : N ↦ χ n) hid
  simp only [map_mul] at hmap
  rw [hχ (Quotient.out (QuotientGroup.mk' N g : P ⧸ N))
    (quotientSectionResidue N h)] at hmap
  have hadd := congrArg Multiplicative.toAdd hmap
  exact hadd.symm

/-- An invariant kernel character extends whenever its factor set is a coboundary. -/
noncomputable def transgressionKernelExtension
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (hχ : ∀ (g : P) (n : N), χ (MulAut.conjNormal g n) = χ n)
    (b : P ⧸ N → ZMod p)
    (hb : ∀ q r,
      b r - b (q * r) + b q = transgressionFactor N χ q r) :
    MonoidHom P (Multiplicative (ZMod p)) where
  toFun g := Multiplicative.ofAdd
    ((χ (quotientSectionResidue N g)).toAdd + b (QuotientGroup.mk' N g))
  map_one' := by
    change Multiplicative.ofAdd
      ((χ (quotientSectionResidue N 1)).toAdd + b 1) = 1
    have hres : quotientSectionResidue N 1 =
        (quotientSectionFactor N 1 1)⁻¹ := by
      apply Subtype.ext
      simp [quotientSectionResidue, quotientSectionFactor]
    have hb11 := hb 1 1
    simp only [one_mul, sub_self, zero_add] at hb11
    rw [hres, map_inv]
    change Multiplicative.ofAdd
      (-(χ (quotientSectionFactor N 1 1)).toAdd + b 1) = 1
    rw [hb11]
    simp [transgressionFactor]
  map_mul' g h := by
    change (χ (quotientSectionResidue N (g * h))).toAdd +
        b (QuotientGroup.mk' N (g * h)) =
      ((χ (quotientSectionResidue N g)).toAdd + b (QuotientGroup.mk' N g)) +
        ((χ (quotientSectionResidue N h)).toAdd + b (QuotientGroup.mk' N h))
    rw [character_quotientSectionResidue_mul N χ hχ]
    have hmk : QuotientGroup.mk' N (g * h) =
        QuotientGroup.mk' N g * QuotientGroup.mk' N h :=
      map_mul (QuotientGroup.mk' N) g h
    rw [hmk]
    have hbgh := hb (QuotientGroup.mk' N g) (QuotientGroup.mk' N h)
    calc
      (χ (quotientSectionResidue N g)).toAdd +
            (χ (quotientSectionResidue N h)).toAdd +
            transgressionFactor N χ (QuotientGroup.mk' N g) (QuotientGroup.mk' N h) +
          b (QuotientGroup.mk' N g * QuotientGroup.mk' N h) =
        (χ (quotientSectionResidue N g)).toAdd +
          b (QuotientGroup.mk' N g) +
          ((χ (quotientSectionResidue N h)).toAdd +
            b (QuotientGroup.mk' N h)) := by
              rw [← hbgh]
              abel

/-- The coboundary extension restricts to the original kernel character. -/
theorem transgressionKernelExtension_restrict
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (hχ : ∀ (g : P) (n : N), χ (MulAut.conjNormal g n) = χ n)
    (b : P ⧸ N → ZMod p)
    (hb : ∀ q r,
      b r - b (q * r) + b q = transgressionFactor N χ q r) :
    (transgressionKernelExtension N χ hχ b hb).comp N.subtype = χ := by
  ext n
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  dsimp only [transgressionKernelExtension]
  change Multiplicative.toAdd (Multiplicative.ofAdd
    ((χ (quotientSectionResidue N (n : P))).toAdd +
      b (QuotientGroup.mk' N (n : P)))) = (χ n).toAdd
  rw [show QuotientGroup.mk' N (n : P) = 1 by
    change ((n : P) : P ⧸ N) = 1
    exact (QuotientGroup.eq_one_iff (N := N) (n : P)).2 n.2]
  change (χ (quotientSectionResidue N n)).toAdd + b 1 = (χ n).toAdd
  have hnq : QuotientGroup.mk' N (n : P) = 1 := by
    change ((n : P) : P ⧸ N) = 1
    exact (QuotientGroup.eq_one_iff (N := N) (n : P)).2 n.2
  have hres : quotientSectionResidue N n =
      n * (quotientSectionFactor N 1 1)⁻¹ := by
    apply Subtype.ext
    simp [quotientSectionResidue, quotientSectionFactor, hnq]
  have hb11 := hb 1 1
  simp only [one_mul, sub_self, zero_add] at hb11
  rw [hres, map_mul, map_inv]
  rw [toAdd_mul, toAdd_inv]
  rw [hb11]
  simp [transgressionFactor]

/-- The normalized inhomogeneous value of a homogeneous degree-one cochain. -/
def homogeneousOneCochainNormalizedValue
    (N : Subgroup P) [N.Normal]
    (c : (TopRep.homogeneousCochains
      (trivialZModPLifted (p := p) (P ⧸ N))).X 1)
    (q : P ⧸ N) : ZMod p :=
  (c.1 1 q).down

/-- Homogeneous degree-one cochains are invariant under simultaneous left translation. -/
theorem homogeneousOneCochain_invariant
    (N : Subgroup P) [N.Normal]
    (c : (TopRep.homogeneousCochains
      (trivialZModPLifted (p := p) (P ⧸ N))).X 1)
    (a q r : P ⧸ N) :
    c.1 (a⁻¹ * q) (a⁻¹ * r) = c.1 q r := by
  have hc := c.2 a
  have hcr := congrArg (fun τ ↦ τ q r) hc
  have hcr' :
      (trivialZModPLifted p (P ⧸ N)).ρ a
          (c.1 (a⁻¹ * q) (a⁻¹ * r)) = c.1 q r := by
    simpa only [ContRepresentation.coind₁_apply_apply] using hcr
  exact (trivialZModPLifted_action p (P ⧸ N) a _).symm.trans hcr'

/-- A homogeneous primitive of the factor cochain yields its inhomogeneous coboundary formula. -/
theorem homogeneousOneCochainNormalizedValue_primitive
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (c : (TopRep.homogeneousCochains
      (trivialZModPLifted (p := p) (P ⧸ N))).X 1)
    (hc : ((TopRep.homogeneousCochains
      (trivialZModPLifted (p := p) (P ⧸ N))).d 1 2).hom c =
        transgressionHomogeneousCochain N χ)
    (q r : P ⧸ N) :
    homogeneousOneCochainNormalizedValue N c r -
        homogeneousOneCochainNormalizedValue N c (q * r) +
          homogeneousOneCochainNormalizedValue N c q =
      transgressionFactor N χ q r := by
  have hd := TopRep.homogeneousCochains.d_apply
    (trivialZModPLifted (p := p) (P ⧸ N)) 1 c
  have hdpoint := congrArg (fun τ ↦ τ 1 q (q * r)) hd
  have hcpoint := congrArg (fun τ ↦ τ.1 1 q (q * r)) hc
  rw [hdpoint] at hcpoint
  simp [TopRep.d_succ, TopRep.d_zero, TopRep.hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun] at hcpoint
  have hinv := homogeneousOneCochain_invariant N c q q (q * r)
  have hinv' : c.1 q (q * r) = c.1 1 r := by
    convert hinv.symm using 1
    all_goals group
  rw [hinv'] at hcpoint
  have htrans : (transgressionHomogeneousCochain N χ).1 1 q (q * r) =
      ULift.up (transgressionFactor N χ q r) := by
    rw [transgressionHomogeneousCochain_apply]
    congr 1
    all_goals group
  rw [htrans] at hcpoint
  let e : ULift.{u} (ZMod p) ≃ₗ[ZMod p] ZMod p := ULift.moduleEquiv
  change e (c.1 1 r) - e (c.1 1 (q * r)) + e (c.1 1 q) =
    transgressionFactor N χ q r
  calc
    e (c.1 1 r) - e (c.1 1 (q * r)) + e (c.1 1 q) =
        e (c.1 1 r) - (e (c.1 1 (q * r)) - e (c.1 1 q)) := by abel
    _ = e (c.1 1 r) - e (c.1 1 (q * r) - c.1 1 q) :=
      congrArg (fun t ↦ e (c.1 1 r) - t)
        (e.map_sub (c.1 1 (q * r)) (c.1 1 q)).symm
    _ = e (c.1 1 r - (c.1 1 (q * r) - c.1 1 q)) :=
      (e.map_sub (c.1 1 r) (c.1 1 (q * r) - c.1 1 q)).symm
    _ = e (ULift.up (transgressionFactor N χ q r)) := congrArg e hcpoint
    _ = transgressionFactor N χ q r := rfl

/-- Extract an elementwise boundary from a cocycle whose homology class vanishes. -/
theorem exists_boundary_of_homologyπ_apply_eq_zero
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : TopRep.{u} (ZMod p) G) (n : ℕ)
    (z : ContinuousCohomology.cocycles A (n + 1))
    (hz : ContinuousCohomology.π A (n + 1) z = 0) :
    ∃ c : (TopRep.homogeneousCochains A).X n,
      ((TopRep.homogeneousCochains A).d n (n + 1)).hom c =
        ((TopRep.homogeneousCochains A).iCycles (n + 1)).hom z := by
  let K := TopRep.homogeneousCochains A
  let S : ShortComplex (TopModuleCat (ZMod p)) :=
    ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
      (K.toCycles_comp_homologyπ n (n + 1))
  have hS : S.Exact :=
    ShortComplex.exact_of_g_is_cokernel S
      (K.homologyIsCokernel n (n + 1) (by simp))
  let F := forget₂ (TopModuleCat (ZMod p)) (ModuleCat (ZMod p))
  have hSM : (S.map F).Exact := hS.map F
  have hz' : (S.map F).g z = 0 := hz
  obtain ⟨c, hc⟩ := ((S.map F).exact_iff_of_hasForget.mp hSM) z hz'
  refine ⟨c, ?_⟩
  rw [← K.toCycles_i n (n + 1)]
  have hc' : (K.toCycles n (n + 1)).hom c = z := hc
  exact congrArg (fun w ↦ (K.iCycles (n + 1)).hom w) hc'

/-- Vanishing of the finite factor-set class forces the invariant kernel character to extend. -/
theorem exists_extension_of_finiteTransgressionClass_eq_zero
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (hχ : ∀ (g : P) (n : N), χ (MulAut.conjNormal g n) = χ n)
    (hzero : finiteTransgressionClass N χ hχ = 0) :
    ∃ ψ : MonoidHom P (Multiplicative (ZMod p)), ψ.comp N.subtype = χ := by
  obtain ⟨c, hc⟩ := exists_boundary_of_homologyπ_apply_eq_zero
    (trivialZModPLifted (p := p) (P ⧸ N)) 1
      (transgressionHomogeneousCocycle N χ hχ) hzero
  have hc' :
      ((TopRep.homogeneousCochains
        (trivialZModPLifted (p := p) (P ⧸ N))).d 1 2).hom c =
        transgressionHomogeneousCochain N χ := by
    rw [hc, iCycles_transgressionHomogeneousCocycle]
  let b : P ⧸ N → ZMod p := homogeneousOneCochainNormalizedValue N c
  have hb : ∀ q r, b r - b (q * r) + b q =
      transgressionFactor N χ q r := by
    exact homogeneousOneCochainNormalizedValue_primitive N χ c hc'
  exact ⟨transgressionKernelExtension N χ hχ b hb,
    transgressionKernelExtension_restrict N χ hχ b hb⟩

end

end ClassFieldTower.Cohomology
