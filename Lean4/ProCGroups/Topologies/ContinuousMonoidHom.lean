import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient

set_option autoImplicit false

/-!
# Continuous group homomorphisms

This file provides standard continuous homomorphisms involving subgroups and quotients, proves an
open-mapping criterion for compact-to-Hausdorff surjections, and develops range restrictions.
Kernels and ranges are shown closed under the expected separation hypotheses.
-/

namespace ProCGroups

namespace MonoidHom

universe u v

/--
A homomorphism from a topological group to a discrete group is continuous if its kernel is open.
-/
theorem continuous_of_isOpen_ker_to_discrete
    {G : Type u} {Q : Type v}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →* Q) (hker : IsOpen ((f.ker : Subgroup G) : Set G)) : Continuous f := by
  classical
  rw [continuous_discrete_rng]
  intro y
  by_cases hy : ∃ x : G, f x = y
  · rcases hy with ⟨x, hx⟩
    have hEq :
        f ⁻¹' ({y} : Set Q) = (fun z : G => x * z) '' ((f.ker : Subgroup G) : Set G) := by
      ext z
      constructor
      · intro hz
        have hz' : f z = y := by simpa using hz
        refine ⟨x⁻¹ * z, ?_, by simp only [mul_inv_cancel_left]⟩
        change f (x⁻¹ * z) = 1
        simp only [map_mul, map_inv, hx, hz', inv_mul_cancel]
      · rintro ⟨k, hk, rfl⟩
        change f (x * k) = y
        rw [map_mul, hx]
        simpa using hk
    rw [hEq]
    exact isOpenMap_mul_left x _ hker
  · have hEq : f ⁻¹' ({y} : Set Q) = ∅ := by
      ext z
      constructor
      · intro hz
        exact False.elim (hy ⟨z, hz⟩)
      · intro hz
        simp only [Set.mem_empty_iff_false] at hz
    rw [hEq]
    exact isOpen_empty

end MonoidHom

namespace ContinuousMonoidHom

universe u v

section Group

variable {G : Type u} {H : Type v}
variable [Group G] [TopologicalSpace G]
variable [Group H] [TopologicalSpace H]

/-- The inclusion of a subgroup, as a continuous monoid homomorphism for the subtype topology. -/
def subtype (K : Subgroup G) : K →ₜ* G where
  toMonoidHom := K.subtype
  continuous_toFun := continuous_subtype_val

/--
The continuous homomorphism induced by a subgroup inclusion evaluates to the underlying subgroup
element.
-/
@[simp] theorem subtype_apply (K : Subgroup G) (x : K) :
    subtype K x = x :=
  rfl

/--
The quotient projection \(G \to G/K\), bundled as a continuous monoid homomorphism for the
quotient topology.
-/
def quotientMk (K : Subgroup G) [K.Normal] : G →ₜ* G ⧸ K where
  toMonoidHom := QuotientGroup.mk' K
  continuous_toFun := continuous_quotient_mk'

/--
The continuous quotient homomorphism evaluates by taking the quotient class of the input
element.
-/
@[simp] theorem quotientMk_apply (K : Subgroup G) [K.Normal] (x : G) :
    quotientMk K x = QuotientGroup.mk' K x :=
  rfl

/--
A continuous surjective homomorphism from a compact group to a Hausdorff topological group is an
open map.
-/
theorem isOpenMap_of_surjective_compact_t2
    [IsTopologicalGroup G] [CompactSpace G] [T2Space H]
    (f : G →ₜ* H) (hf : Function.Surjective f) :
    IsOpenMap f := by
  intro U hU
  have hq : Topology.IsQuotientMap f :=
    f.continuous_toFun.isClosedMap.isQuotientMap f.continuous_toFun hf
  refine (hq.isOpen_preimage).1 ?_
  have hpre :
      f ⁻¹' (f '' U) =
        ⋃ k : f.toMonoidHom.ker, (fun x : G => x * k.1) '' U := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨u, huU, huf⟩
      refine Set.mem_iUnion.2
        ⟨⟨u⁻¹ * z, ?_⟩, ⟨u, huU, by simp only [mul_inv_cancel_left]⟩⟩
      change f.toMonoidHom (u⁻¹ * z) = 1
      simp only [_root_.ContinuousMonoidHom.coe_toMonoidHom, map_mul, map_inv,
          MonoidHom.coe_coe, huf, inv_mul_cancel]
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨k, hk⟩
      rcases hk with ⟨u, huU, rfl⟩
      exact ⟨u, huU, by
        change f.toMonoidHom u = f.toMonoidHom (u * k.1)
        rw [map_mul, show f.toMonoidHom k.1 = 1 from k.2, mul_one]⟩
  rw [hpre]
  exact isOpen_iUnion fun k => isOpenMap_mul_right k.1 U hU

/-- A continuous homomorphism restricts to its range with the induced subtype topology. -/
def rangeRestrict (f : G →ₜ* H) : G →ₜ* f.toMonoidHom.range where
  toMonoidHom := f.toMonoidHom.rangeRestrict
  continuous_toFun := Continuous.subtype_mk f.continuous_toFun fun x => ⟨x, rfl⟩

/--
The range-restricted continuous homomorphism evaluates to the image element together with its
range-membership certificate.
-/
@[simp] theorem rangeRestrict_apply (f : G →ₜ* H) (x : G) :
    f.rangeRestrict x = f.toMonoidHom.rangeRestrict x :=
  rfl

/--
Coercing the range-restricted homomorphism back to the codomain recovers the original
homomorphism value.
-/
@[simp] theorem coe_rangeRestrict_apply (f : G →ₜ* H) (x : G) :
    (f.rangeRestrict x : H) = f x :=
  rfl

/-- The kernel of a continuous homomorphism to a \(T_1\) group is closed. -/
theorem isClosed_ker [T1Space H] (f : G →ₜ* H) :
    IsClosed ((f.toMonoidHom.ker : Subgroup G) : Set G) := by
  have hker :
      ((f.toMonoidHom.ker : Subgroup G) : Set G) =
        f ⁻¹' ({1} : Set H) := by
    ext x
    change (f x = 1) ↔ f x ∈ ({1} : Set H)
    simp only [Set.mem_singleton_iff]
  rw [hker]
  exact (isClosed_singleton (x := (1 : H))).preimage f.continuous_toFun

/-- The range of a continuous homomorphism from a compact space to a Hausdorff space is closed. -/
theorem isClosed_range [CompactSpace G] [T2Space H] (f : G →ₜ* H) :
    IsClosed ((f.toMonoidHom.range : Subgroup H) : Set H) := by
  have himage : IsCompact (f '' (Set.univ : Set G)) :=
    isCompact_univ.image f.continuous_toFun
  have hEq : f '' (Set.univ : Set G) = ((f.toMonoidHom.range : Subgroup H) : Set H) := by
    ext y
    constructor
    · rintro ⟨x, _hx, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, trivial, rfl⟩
  exact (hEq ▸ himage).isClosed

end Group

end ContinuousMonoidHom

end ProCGroups
