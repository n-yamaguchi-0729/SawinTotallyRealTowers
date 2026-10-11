/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.LocalComplement
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

/-!
# Density and connectedness of divisor complements

The complement of an effective Cartier divisor is dense, without a reducedness
hypothesis. A dense open subset of a connected space is connected if every
point of its complement admits an irreducible open neighborhood.

For a locally Noetherian scheme, an irreducible neighborhood is constructed
from a domain stalk: the image of its local spectrum is irreducible and
contains all generizations, so only one irreducible component passes through
the point on an affine chart. Removing the other finitely many components
produces the required neighborhood.

The algebraic implication from `IsRegularLocalRing` to `IsDomain` is not
assumed or axiomatized here. These lemmas do not by themselves complete the
regular-boundary case until that implication is available.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set

namespace PrimeSpectrum

universe u

/-- A principal open defined by a non-zero-divisor is dense. -/
theorem dense_basicOpen_of_isRegular
    {R : Type u} [CommRing R] {f : R} (hf : IsRegular f) :
    Dense (basicOpen f : Set (PrimeSpectrum R)) := by
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f)
      (Submonoid.powers_le.mpr hf.mem_nonZeroDivisors)
  have hker : RingHom.ker (algebraMap R (Localization.Away f)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot
      (algebraMap R (Localization.Away f))).mp hinj
  have hdense : DenseRange (comap (algebraMap R (Localization.Away f))) := by
    apply (denseRange_comap_iff_ker_le_nilRadical _).2
    rw [hker]
    exact bot_le
  change Dense (Set.range (comap (algebraMap R (Localization.Away f)))) at hdense
  rw [localization_away_comap_range (Localization.Away f) f] at hdense
  exact hdense

end PrimeSpectrum

namespace SchemeTheory

universe u

/-- Irreducible neighborhoods at the missing points prevent a dense open
subset of a connected space from disconnecting. -/
theorem connectedSpace_open_of_dense_of_irreducible_boundary_neighborhoods
    {X : Type u} [TopologicalSpace X] [ConnectedSpace X]
    (U : Set X) (hU : IsOpen U) (hdense : Dense U)
    (hlocal : ∀ x ∉ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsIrreducible V) :
    ConnectedSpace U := by
  apply isConnected_iff_connectedSpace.mp
  refine ⟨hdense.nonempty, ?_⟩
  intro A B hA hB hcover hUA hUB
  by_contra hdisjoint
  let S := U ∩ A
  let T := U ∩ B
  have hS : IsOpen S := hU.inter hA
  have hT : IsOpen T := hU.inter hB
  have hUT : U = S ∪ T := by
    ext x
    constructor
    · intro hx
      rcases hcover hx with hxA | hxB
      · exact Or.inl ⟨hx, hxA⟩
      · exact Or.inr ⟨hx, hxB⟩
    · intro hx
      exact hx.elim (fun h => h.1) (fun h => h.1)
  have hclosedCover : (univ : Set X) ⊆ closure S ∪ closure T := by
    intro x _
    have hx := hdense x
    rw [hUT, closure_union] at hx
    exact hx
  obtain ⟨x, _, hxS, hxT⟩ :=
    isPreconnected_closed_iff.mp isPreconnected_univ
      (closure S) (closure T) isClosed_closure isClosed_closure hclosedCover
      (by rcases hUA with ⟨a, ha⟩; exact ⟨a, mem_univ a, subset_closure ha⟩)
      (by rcases hUB with ⟨b, hb⟩; exact ⟨b, mem_univ b, subset_closure hb⟩)
  have no_common : ∀ z, z ∈ S → z ∈ T → False := by
    intro z hzS hzT
    exact hdisjoint ⟨z, hzS.1, hzS.2, hzT.2⟩
  by_cases hxU : x ∈ U
  · rcases hcover hxU with hxA | hxB
    · obtain ⟨z, hzS, hzT⟩ := mem_closure_iff.mp hxT S hS ⟨hxU, hxA⟩
      exact no_common z hzS hzT
    · obtain ⟨z, hzT, hzS⟩ := mem_closure_iff.mp hxS T hT ⟨hxU, hxB⟩
      exact no_common z hzS hzT
  · obtain ⟨V, hV, hxV, hirred⟩ := hlocal x hxU
    obtain ⟨z, _, hzS, hzT⟩ := hirred.2 S T hS hT
      (mem_closure_iff.mp hxS V hV hxV)
      (mem_closure_iff.mp hxT V hV hxV)
    exact no_common z hzS hzT

private theorem exists_irreducible_open_of_generizations_subset
    {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]
    (x : X) (S : Set X) (hS : IsIrreducible S)
    (hgen : ∀ y, y ⤳ x → y ∈ S) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsIrreducible V := by
  obtain ⟨Z, hZ, hSZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible S hS
  have hunique : ∀ W ∈ irreducibleComponents X, x ∈ W → W = Z := by
    intro W hW hxW
    have hgeneric := hW.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents W hW)
    have hpoint : hW.1.genericPoint ∈ Z :=
      hSZ (hgen _ (hgeneric.specializes hxW))
    have hWZ : W ⊆ Z := by
      rw [← hW.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents W hW)]
      exact closure_minimal (singleton_subset_iff.mpr hpoint)
        (isClosed_of_mem_irreducibleComponents Z hZ)
    exact subset_antisymm hWZ (hW.2 hZ.1 hWZ)
  let V : Set X := (⋃₀ (irreducibleComponents X \ {Z}))ᶜ
  have hV : IsOpen V := by
    change IsOpen (⋃₀ (irreducibleComponents X \ {Z}))ᶜ
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
  have hxV : x ∈ V := by
    rintro ⟨W, hW, hxW⟩
    exact hW.2 (mem_singleton_iff.mpr (hunique W hW.1 hxW))
  refine ⟨V, hV, hxV, isIrreducible_iff_closure.mp ?_⟩
  have hclosure : closure V = Z :=
    closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents Z hZ
  rw [hclosure]
  exact hZ.1

end SchemeTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- An effective Cartier divisor misses a dense open subset of its ambient scheme. -/
theorem EffectiveCartierDivisor.dense_supportComplement
    {X : Scheme.{u}} (D : X.EffectiveCartierDivisor) :
    Dense (D.1.supportComplement : Set X) := by
  apply dense_iff_inter_open.mpr
  intro V hV hVne
  obtain ⟨x, hxV⟩ := hVne
  obtain ⟨U, hxU, f, hf, hI⟩ := D.2 x
  have hxRange : x ∈ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    exact hxU
  obtain ⟨p, hp⟩ := hxRange
  have hpre : (U.2.fromSpec ⁻¹' V).Nonempty := by
    refine ⟨p, ?_⟩
    change U.2.fromSpec p ∈ V
    rw [hp]
    exact hxV
  obtain ⟨q, hqV, hqf⟩ :=
    (PrimeSpectrum.dense_basicOpen_of_isRegular hf).inter_open_nonempty
      (U.2.fromSpec ⁻¹' V) (hV.preimage U.2.fromSpec.continuous) hpre
  refine ⟨U.2.fromSpec q, hqV, ?_⟩
  change U.2.fromSpec q ∉ D.1.support
  intro hqD
  have hqU : U.2.fromSpec q ∈ U.1 := by
    change (U.2.isoSpec.inv q).1 ∈ U.1
    exact (U.2.isoSpec.inv q).2
  have hqZero := (D.1.mem_support_iff_of_mem (U := U) hqU).mp hqD
  have hzero : q ∈ PrimeSpectrum.zeroLocus (D.1.ideal U : Set Γ(X, U.1)) :=
    (Set.ext_iff.mp (U.2.fromSpec_preimage_zeroLocus (D.1.ideal U : Set Γ(X, U.1))) q).mp
      hqZero
  rw [hI] at hzero
  exact hqf (hzero (Ideal.subset_span (mem_singleton f)))

/-- A domain stalk on a locally Noetherian scheme has an irreducible open neighborhood. -/
theorem exists_isIrreducible_open_of_isDomain_stalk
    {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X)
    [IsDomain (X.presheaf.stalk x)] :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsIrreducible V := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) (mem_univ x)
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
  let : QuasiSober U := U.ι.isOpenEmbedding.quasiSober
  let l : Spec (X.presheaf.stalk x) ⟶ U := U.fromSpecStalkOfMem x hxU
  have hS : IsIrreducible (Set.range l) := by
    simpa only [image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Spec (X.presheaf.stalk x))).image
        l l.continuous.continuousOn
  have hgen : ∀ y : U, y ⤳ (⟨x, hxU⟩ : U) → y ∈ Set.range l := by
    intro y hy
    have hyX : (y : X) ⤳ x := hy.map U.ι.continuous
    have hyRange : (y : X) ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact hyX
    obtain ⟨q, hq⟩ := hyRange
    refine ⟨q, Subtype.ext ?_⟩
    exact (congrArg (fun f : Spec (X.presheaf.stalk x) ⟶ X => f q)
      (U.fromSpecStalkOfMem_ι x hxU)).trans hq
  obtain ⟨W, hW, hxW, hirred⟩ :=
    SchemeTheory.exists_irreducible_open_of_generizations_subset
      (X := U) (⟨x, hxU⟩ : U) (Set.range l) hS hgen
  refine ⟨U.ι '' W, U.ι.isOpenEmbedding.isOpenMap W hW, ⟨⟨x, hxU⟩, hxW, rfl⟩, ?_⟩
  exact hirred.image U.ι U.ι.continuous.continuousOn

/-- For a divisor whose boundary stalks are domains, the dense open complement
is connected. This does not assume integrality or normality away from the boundary. -/
theorem EffectiveCartierDivisor.connectedSpace_supportComplement_of_domain_stalks
    {X : Scheme.{u}} [ConnectedSpace X] [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor)
    (hD : ∀ x ∈ D.1.support, IsDomain (X.presheaf.stalk x)) :
    ConnectedSpace D.1.supportComplement := by
  apply SchemeTheory.connectedSpace_open_of_dense_of_irreducible_boundary_neighborhoods
    (D.1.supportComplement : Set X) D.1.supportComplement.isOpen D.dense_supportComplement
  intro x hx
  have hxD : x ∈ D.1.support := not_not.mp hx
  let : IsDomain (X.presheaf.stalk x) := hD x hxD
  exact exists_isIrreducible_open_of_isDomain_stalk x

end AlgebraicGeometry.Scheme
