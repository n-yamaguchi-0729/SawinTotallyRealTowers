import ValuedFieldTheory.Ramification.HilbertRamification.BaseChange

set_option autoImplicit false
/-!
# Valuation inertia under algebra equivalences

An algebra equivalence transports the ambient copy of valuation-subring inertia to the
corresponding ambient inertia subgroup for the pulled-back valuation subring.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open HilbertRamification

universe u v w

/-- Conjugation by an algebra equivalence sends ambient valuation inertia to ambient valuation
inertia for the transported valuation subring. -/
theorem autCongr_mem_valuationInertiaGroupInAut
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [Normal K M]
    (e : L ≃ₐ[K] M) (B : ValuationSubring M)
    (sigma : L ≃ₐ[K] L)
    (hsigma : sigma ∈
      RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut K
        (B.comap e.toRingHom)) :
    AlgEquiv.autCongr e sigma ∈
      RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut K B := by
  let A : ValuationSubring L := B.comap e.toRingHom
  change sigma ∈
      RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut K A at hsigma
  rcases hsigma with ⟨delta, hdelta, hdelta_sigma⟩
  let eta : RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K A :=
    ⟨delta, hdelta⟩
  have hsquare :
      e.symm.toRingHom.comp (algebraMap K M) =
        (algebraMap K L).comp (RingHom.id K) := by
    ext x
    simp
  let etaRaw :=
    HilbertRamification.ValuationSubring.galoisPullback_inertiaGroupMap
      (RingHom.id K) e.symm.toRingHom hsquare A eta
  have hAB : A.comap e.symm.toRingHom = B := by
    ext y
    change e (e.symm y) ∈ B ↔ y ∈ B
    simp
  have hraw :
      (((etaRaw :
          RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K
            (A.comap e.symm.toRingHom)) :
          RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
            (A.comap e.symm.toRingHom)) : M ≃ₐ[K] M) =
        AlgEquiv.autCongr e sigma := by
    ext y
    apply e.symm.injective
    change e.symm.toRingHom
        ((HilbertRamification.galoisPullback_galoisPullback
          (RingHom.id K) e.symm.toRingHom hsquare
          (((eta :
              RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K A) :
              RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K A) :
              L ≃ₐ[K] L)) y) = e.symm.toRingHom _
    rw [HilbertRamification.galoisPullback_galoisPullback_commutes]
    have happ := DFunLike.congr_fun hdelta_sigma (e.symm y)
    change
      ((RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K A).subtype
        delta) (e.symm y) = _
    rw [happ]
    simp [AlgEquiv.autCongr_apply]
  rw [← hAB]
  refine ⟨(etaRaw :
      RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
        (A.comap e.symm.toRingHom)), etaRaw.property, ?_⟩
  exact hraw

/-- Membership in ambient valuation inertia is invariant under conjugation by an algebra
equivalence. -/
theorem autCongr_mem_valuationInertiaGroupInAut_iff
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [Normal K L] [Normal K M]
    (e : L ≃ₐ[K] M) (B : ValuationSubring M)
    (sigma : L ≃ₐ[K] L) :
    AlgEquiv.autCongr e sigma ∈
        RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut K B ↔
      sigma ∈
        RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut K
          (B.comap e.toRingHom) := by
  let A : ValuationSubring L := B.comap e.toRingHom
  have hAB : A.comap e.symm.toRingHom = B := by
    ext y
    change e (e.symm y) ∈ B ↔ y ∈ B
    simp
  constructor
  · intro hsigma
    have hsigma' : AlgEquiv.autCongr e sigma ∈
        RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut K
          (A.comap e.symm.toRingHom) := by
      rw [hAB]
      exact hsigma
    have h := autCongr_mem_valuationInertiaGroupInAut
      e.symm A (AlgEquiv.autCongr e sigma) hsigma'
    change (AlgEquiv.autCongr e).symm (AlgEquiv.autCongr e sigma) ∈
      RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut K A at h
    rw [(AlgEquiv.autCongr e).symm_apply_apply sigma] at h
    exact h
  · intro hsigma
    exact autCongr_mem_valuationInertiaGroupInAut e B sigma hsigma

/-- Conjugation by an algebra equivalence maps the whole ambient valuation-inertia subgroup
onto the target ambient inertia subgroup. -/
theorem valuationInertiaGroupInAut_map_autCongr
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [Normal K L] [Normal K M]
    (e : L ≃ₐ[K] M) (B : ValuationSubring M) :
    Subgroup.map (AlgEquiv.autCongr e).toMonoidHom
        (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut K
          (B.comap e.toRingHom)) =
      RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut K B := by
  ext tau
  constructor
  · rintro ⟨sigma, hsigma, rfl⟩
    exact (autCongr_mem_valuationInertiaGroupInAut_iff e B sigma).2 hsigma
  · intro htau
    let sigma : L ≃ₐ[K] L := (AlgEquiv.autCongr e).symm tau
    refine ⟨sigma, ?_, (AlgEquiv.autCongr e).apply_symm_apply tau⟩
    apply (autCongr_mem_valuationInertiaGroupInAut_iff e B sigma).1
    have hsigma : AlgEquiv.autCongr e sigma = tau :=
      (AlgEquiv.autCongr e).apply_symm_apply tau
    rw [hsigma]
    exact htau

end ClassFieldTower.Martinet.Shafarevich
