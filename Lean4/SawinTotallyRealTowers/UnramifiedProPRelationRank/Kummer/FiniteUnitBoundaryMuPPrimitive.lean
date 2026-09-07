import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
import GaloisCohomology.Kummer.Concrete.GaloisCohomology

set_option autoImplicit false
/-!
# Correcting finite unit boundaries to absolute roots-of-unity boundaries

Suppose a finite Galois two-cochain with values in `mu_p` is the boundary
of a unit-valued one-cochain `b`.  Then `b^p` is a crossed homomorphism.
Noether's Hilbert 90 produces its primitive `u`; a `p`-th root of `u`
in the algebraic closure corrects `b` to a `mu_p`-valued primitive.

The resulting absolute primitive is continuous: both finite restriction
and the orbit map of the chosen algebraic root are locally constant.
The statement uses the natural Galois action and does not assume that
the base contains `mu_p` or that the finite Galois group is a `p`-group.
No new instances are introduced.
-/

open scoped Pointwise Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory groupCohomology

variable (K : Type) [Field K] [CharZero K]
variable (p : ℕ) [Fact p.Prime]
variable (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))

omit [CharZero K] [Fact p.Prime] in
private theorem finiteBoundary_power_isMulCocycle
    (c : Gal(E/K) → Gal(E/K) → nthRootsSubgroup E p)
    (b : Gal(E/K) → Eˣ)
    (hb : ∀ s t : Gal(E/K),
      Units.map s (b t) * b s / b (s * t) = (c s t).1) :
    IsMulCocycle₁ (fun s => b s ^ p) := by
  intro s t
  have h := congrArg (fun x : Eˣ => x ^ p) (hb s t)
  rw [div_pow, mul_pow,
    (mem_nthRootsSubgroup_iff E).mp (c s t).2] at h
  rw [smul_pow', AlgEquiv.smul_units_def]
  exact (div_eq_one.mp h).symm

private theorem absoluteUnit_orbit_isLocallyConstant (u : (AlgebraicClosure K)ˣ) :
    IsLocallyConstant (fun sigma : Gal(AlgebraicClosure K/K) => sigma • u) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro sigma
  let D := FiniteGaloisIntermediateField.adjoin K {(u : AlgebraicClosure K)}
  let H : Set Gal(AlgebraicClosure K/K) := D.fixingSubgroup
  refine ⟨sigma • H, (IntermediateField.fixingSubgroup_isOpen
    D.toIntermediateField).leftCoset sigma, ?_, ?_⟩
  · exact ⟨1, D.fixingSubgroup.one_mem, mul_one sigma⟩
  · intro tau htau
    rcases htau with ⟨h, hh, htau⟩
    have hfix : h • u = u := by
      apply Units.ext
      exact ((IntermediateField.mem_fixingSubgroup_iff D.toIntermediateField h).mp hh)
        (u : AlgebraicClosure K)
        (FiniteGaloisIntermediateField.subset_adjoin K {(u : AlgebraicClosure K)}
          (Set.mem_singleton _))
    change sigma * h = tau at htau
    rw [← htau, mul_smul, hfix]

omit [CharZero K] in
private theorem finiteUnitInclusion_restriction_smul
    (sigma : Gal(AlgebraicClosure K/K)) (u : Eˣ) :
    Units.map E.val.toMonoidHom
        (AlgEquiv.restrictNormalHom E.toIntermediateField sigma • u) =
      sigma • Units.map E.val.toMonoidHom u := by
  apply Units.ext
  exact AlgEquiv.restrictNormal_commutes sigma E.toIntermediateField (u : E)

omit [CharZero K] in
private theorem exists_absoluteUnit_root (u : Eˣ) :
    ∃ v : (AlgebraicClosure K)ˣ,
      v ^ p = Units.map E.val.toMonoidHom u := by
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq
    (E.val (u : E)) (Fact.out : p.Prime).pos
  have hv0 : v ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (Fact.out : p.Prime).ne_zero] at hv
    exact Units.ne_zero (Units.map E.val.toMonoidHom u) hv.symm
  refine ⟨Units.mk0 v hv0, ?_⟩
  apply Units.ext
  exact hv

private theorem divCochain_mulDiv {M : Type*} [CommGroup M] (a b c x y : M) :
    (a / x) * (b / y) / (c / (x * y)) = a * b / c := by
  rw [div_mul_div_comm, div_div_div_cancel_right]

/-- A supplied finite unit boundary of a roots-of-unity two-cochain yields
an actual continuous roots-of-unity primitive on the absolute Galois group.
The boundary identity is recorded in the ambient unit group, whose
inclusion of `mu_p` is injective. -/
theorem exists_absoluteMuP_primitive_of_finiteUnit_boundary
    (c : Gal(E/K) → Gal(E/K) → nthRootsSubgroup E p)
    (b : Gal(E/K) → Eˣ)
    (hb : ∀ s t : Gal(E/K),
      Units.map s (b t) * b s / b (s * t) = (c s t).1) :
    ∃ a : C(Field.absoluteGaloisGroup K, AbsoluteMuP K p),
      ∀ s t : Field.absoluteGaloisGroup K,
        ((absoluteGaloisGroupContinuousMulEquiv K s) • (a t).toMul.1 :
            (AlgebraicClosure K)ˣ) *
            (a s).toMul.1 / (a (s * t)).toMul.1 =
          Units.map E.val.toMonoidHom
            (c (AlgEquiv.restrictNormalHom E.toIntermediateField
                (absoluteGaloisGroupContinuousMulEquiv K s))
              (AlgEquiv.restrictNormalHom E.toIntermediateField
                (absoluteGaloisGroupContinuousMulEquiv K t))).1 := by
  obtain ⟨u, hu⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
    (fun s => b s ^ p) (finiteBoundary_power_isMulCocycle K p E c b hb)
  obtain ⟨v, hv⟩ := exists_absoluteUnit_root K p E u
  let r : Gal(AlgebraicClosure K/K) →* Gal(E/K) :=
    AlgEquiv.restrictNormalHom E.toIntermediateField
  let i : Eˣ →* (AlgebraicClosure K)ˣ := Units.map E.val.toMonoidHom
  let q : Gal(AlgebraicClosure K/K) → (AlgebraicClosure K)ˣ :=
    fun s => i (b (r s)) / rootQuotient (K := K) v s
  have hq (s : Gal(AlgebraicClosure K/K)) : q s ^ p = 1 := by
    dsimp only [q, rootQuotient]
    rw [div_pow, div_pow, ← map_pow, ← smul_pow', hv,
      ← finiteUnitInclusion_restriction_smul K E, ← map_div, hu]
    exact div_self' _
  let a : Field.absoluteGaloisGroup K → AbsoluteMuP K p := fun s =>
    Additive.ofMul ⟨q (absoluteGaloisGroupContinuousMulEquiv K s),
      (mem_nthRootsSubgroup_iff (AlgebraicClosure K)).mpr
        (hq (absoluteGaloisGroupContinuousMulEquiv K s))⟩
  have hbLC : IsLocallyConstant (fun s : Gal(AlgebraicClosure K/K) => i (b (r s))) :=
    (IsLocallyConstant.of_discrete (fun t : Gal(E/K) => i (b t))).comp_continuous
      (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField)
  have hqLC : IsLocallyConstant q :=
    hbLC.div ((absoluteUnit_orbit_isLocallyConstant K v).div
      (IsLocallyConstant.const v))
  have haLC : IsLocallyConstant a :=
    IsLocallyConstant.desc a (fun x : AbsoluteMuP K p => x.toMul.1)
      (hqLC.comp_continuous (absoluteGaloisGroupContinuousMulEquiv K).continuous)
      (fun x y h => Additive.toMul.injective (Subtype.ext h))
  refine ⟨⟨a, haLC.continuous⟩, ?_⟩
  intro s t
  change (absoluteGaloisGroupContinuousMulEquiv K s) •
      q (absoluteGaloisGroupContinuousMulEquiv K t) *
        q (absoluteGaloisGroupContinuousMulEquiv K s) /
          q (absoluteGaloisGroupContinuousMulEquiv K (s * t)) = _
  let s' : Gal(AlgebraicClosure K/K) := absoluteGaloisGroupContinuousMulEquiv K s
  let t' : Gal(AlgebraicClosure K/K) := absoluteGaloisGroupContinuousMulEquiv K t
  change s' • q t' * q s' / q (s' * t') = i (c (r s') (r t')).1
  dsimp only [q]
  rw [smul_div', ← finiteUnitInclusion_restriction_smul K E, map_mul r,
    rootQuotient_mul, divCochain_mulDiv, ← map_mul i, ← map_div i,
    AlgEquiv.smul_units_def, hb]

end ClassFieldTower.Martinet.Shafarevich
