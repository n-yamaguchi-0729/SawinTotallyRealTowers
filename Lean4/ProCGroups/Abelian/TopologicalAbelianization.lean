import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import ProCGroups.Topologies.TopologicallyCharacteristicSubgroups

set_option autoImplicit false

/-!
# Topological abelianization

This module develops the canonical quotient by the closed commutator subgroup, its universal
property for continuous maps to Hausdorff commutative groups, and the induced quotient topology.
-/

open scoped Topology commutatorElement

namespace ProCGroups.Abelian

universe u v

namespace TopologicalAbelianization

/-- The natural continuous quotient map to the topological abelianization. -/
def mkₜ
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    G →ₜ* TopologicalAbelianization G :=
  { toMonoidHom := QuotientGroup.mk' (Subgroup.closedCommutator G)
    continuous_toFun := QuotientGroup.continuous_mk }

/-- The natural quotient homomorphism to the topological abelianization. -/
abbrev mk
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    G →* TopologicalAbelianization G :=
  (mkₜ G).toMonoidHom

/-- The kernel of the topological abelianization map is the closed commutator subgroup. -/
theorem ker_mk
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    (mk G).ker =
      Subgroup.closedCommutator G := by
  exact QuotientGroup.ker_mk' _

/--
A representative maps to \(1\) in the topological abelianization exactly when it lies in the
closed commutator subgroup.
-/
theorem mk_eq_one_iff
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {x : G} :
    mk G x = 1 ↔
      x ∈ Subgroup.closedCommutator G := by
  exact QuotientGroup.eq_one_iff (N := Subgroup.closedCommutator G) x

/-- In a commutative \(T_1\) topological group, the closed commutator subgroup is trivial. -/
@[simp] theorem closedCommutator_eq_bot_of_commGroup_t1
    (G : Type u) [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G] [T1Space G] :
    Subgroup.closedCommutator G = ⊥ := by
  have hcomm : commutator G = ⊥ := by
    rw [commutator_eq_bot_iff_center_eq_top, CommGroup.center_eq_top]
  rw [Subgroup.closedCommutator, hcomm]
  ext x
  change x ∈ closure ({(1 : G)} : Set G) ↔ x = 1
  rw [closure_singleton]
  simp only [Set.mem_singleton_iff]

/-- The canonical map to the topological abelianization is surjective. -/
theorem surjective_mk
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    Function.Surjective (mk G) :=
  QuotientGroup.mk'_surjective (Subgroup.closedCommutator G)

/--
The topological abelianization is Hausdorff because it is a quotient by the closed commutator
subgroup.
-/
instance instT2SpaceTopologicalAbelianization
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    T2Space (TopologicalAbelianization G) := by
  have : IsClosed (((Subgroup.closedCommutator G : Subgroup G) : Set G)) :=
    Subgroup.isClosed_closedCommutator G
  infer_instance

/--
A continuous homomorphism to a commutative \(T_1\) topological group factors through the
topological abelianization.
-/
noncomputable def lift
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {A : Type v} [TopologicalSpace A] [CommGroup A] [T1Space A]
    (f : G →ₜ* A) :
    TopologicalAbelianization G →ₜ* A := by
  have hclosedCommutator_le_ker :
      Subgroup.closedCommutator G ≤ f.toMonoidHom.ker := by
    have hcomm : commutator G ≤ f.toMonoidHom.ker := by
      rw [commutator_eq_closure]
      rw [Subgroup.closure_le]
      rintro x ⟨g, h, rfl⟩
      change f ⁅g, h⁆ = 1
      simp only [commutatorElement_def, mul_assoc, map_mul, map_inv, mul_inv_cancel_comm_assoc,
          mul_inv_cancel]
    have hkerClosed : IsClosed (((f.toMonoidHom.ker : Subgroup G) : Set G)) := by
      change IsClosed (f ⁻¹' ({1} : Set A))
      simpa using isClosed_singleton.preimage f.continuous_toFun
    exact Subgroup.topologicalClosure_minimal
      (s := commutator G) (t := f.toMonoidHom.ker) hcomm hkerClosed
  exact QuotientGroup.liftₜ (Subgroup.closedCommutator G) f hclosedCommutator_le_ker

/--
The lift from the topological abelianization evaluates on a quotient class by applying the
original homomorphism.
-/
@[simp] theorem lift_apply_mk
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {A : Type v} [TopologicalSpace A] [CommGroup A] [T1Space A]
    (f : G →ₜ* A) (x : G) :
    lift f (mk G x) = f x := by
  rfl

/--
Continuous homomorphisms out of the topological abelianization are equal when they agree after
the quotient map.
-/
@[ext] theorem hom_ext
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {A : Type v} [TopologicalSpace A] [Group A]
    (φ ψ : TopologicalAbelianization G →ₜ* A)
    (h : ∀ x : G, φ (mk G x) = ψ (mk G x)) :
    φ = ψ := by
  apply ContinuousMonoidHom.toMonoidHom_injective
  apply MonoidHom.ext
  intro x
  exact Quotient.inductionOn' x h

/--
The lift from the topological abelianization is uniquely determined by its composition with the
quotient map.
-/
theorem lift_unique
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {A : Type v} [TopologicalSpace A] [CommGroup A] [T1Space A]
    (f : G →ₜ* A)
    (φ : TopologicalAbelianization G →ₜ* A)
    (hφ : ∀ x : G, φ (mk G x) = f x) :
    φ = lift f := by
  apply hom_ext
  intro x
  calc
    φ (mk G x) = f x := hφ x
    _ = lift f (mk G x) := (lift_apply_mk f x).symm

/--
The universal property of topological abelianization as a Hom equivalence for commutative
\(T_1\) targets.
-/
noncomputable def homEquiv
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (A : Type v) [TopologicalSpace A] [CommGroup A] [T1Space A] :
    (TopologicalAbelianization G →ₜ* A) ≃ (G →ₜ* A) where
  toFun φ := φ.comp (mkₜ G)
  invFun f := lift f
  left_inv φ := by
    apply hom_ext
    intro x
    rfl
  right_inv f := by
    ext x
    rfl

/--
The Hom-equivalence is evaluated by composing a map out of the topological abelianization with
the quotient map from the original group.
-/
@[simp] theorem homEquiv_apply
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (A : Type v) [TopologicalSpace A] [CommGroup A] [T1Space A]
    (φ : TopologicalAbelianization G →ₜ* A) :
    homEquiv G A φ = φ.comp (mkₜ G) :=
  rfl

/--
The inverse Hom equivalence evaluates on the abelianization class of \(x\) as the original
continuous homomorphism evaluated at \(x\).
-/
@[simp] theorem homEquiv_symm_apply_mk
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (A : Type v) [TopologicalSpace A] [CommGroup A] [T1Space A]
    (f : G →ₜ* A) (x : G) :
    (homEquiv G A).symm f (mk G x) = f x :=
  rfl

/-- A continuous homomorphism induces a continuous homomorphism on topological abelianizations. -/
noncomputable def map
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Type v} [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (f : G →ₜ* H) :
    TopologicalAbelianization G →ₜ* TopologicalAbelianization H :=
  lift ((mkₜ H).comp f)

/-- The induced map on topological abelianizations is evaluated on quotient representatives. -/
@[simp] theorem map_apply_mk
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Type v} [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (f : G →ₜ* H) (x : G) :
    map f (mk G x) =
      mk H (f x) := by
  rfl

/--
Composing the abelianization map with the quotient map recovers the quotient map after applying
the original homomorphism.
-/
@[simp] theorem map_comp_mk
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Type v} [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (f : G →ₜ* H) :
    (map f).toMonoidHom.comp (mk G) =
      (mk H).comp f.toMonoidHom := by
  ext x
  rfl

/--
The map induced by the identity homomorphism is the identity on the topological abelianization.
-/
@[simp] theorem map_id
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    map
        (ContinuousMonoidHom.id G) =
      ContinuousMonoidHom.id (TopologicalAbelianization G) := by
  apply hom_ext
  intro g
  rfl

/-- Induced maps on topological abelianizations compose functorially. -/
@[simp] theorem map_comp
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Type v} [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    {K : Type _} [TopologicalSpace K] [Group K] [IsTopologicalGroup K]
    (g : H →ₜ* K) (f : G →ₜ* H) :
    map (g.comp f) =
      (map g).comp (map f) := by
  apply hom_ext
  intro a
  rfl

/-- A topological group isomorphism induces an isomorphism on topological abelianizations. -/
noncomputable def congr
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Type v} [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) :
    TopologicalAbelianization G ≃ₜ* TopologicalAbelianization H := by
  let f : TopologicalAbelianization G →ₜ* TopologicalAbelianization H :=
    map (ContinuousMonoidHom.toContinuousMonoidHom e)
  let g : TopologicalAbelianization H →ₜ* TopologicalAbelianization G :=
    map (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
  exact ContinuousMulEquiv.ofHomInv f g
    (by
      intro x
      refine Quotient.inductionOn' x ?_
      intro a
      change
        map (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
            (map (ContinuousMonoidHom.toContinuousMonoidHom e)
              (mk G a)) =
          mk G a
      rw [map_apply_mk, map_apply_mk]
      simp only [ContinuousMonoidHom.coe_toMonoidHom, ContinuousMonoidHom.coe_coe,
  ContinuousMulEquiv.symm_apply_apply, MonoidHom.coe_coe])
    (by
      intro y
      refine Quotient.inductionOn' y ?_
      intro b
      change
        map (ContinuousMonoidHom.toContinuousMonoidHom e)
            (map (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
              (mk H b)) =
          mk H b
      rw [map_apply_mk, map_apply_mk]
      simp only [ContinuousMonoidHom.coe_toMonoidHom, ContinuousMonoidHom.coe_coe,
  ContinuousMulEquiv.apply_symm_apply, MonoidHom.coe_coe])

/--
The abelianization congruence induced by a continuous equivalence sends representatives to
representatives.
-/
@[simp] theorem congr_apply_mk
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Type v} [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (x : G) :
    congr e (mk G x) =
      mk H (e x) := by
  rfl

/-- Surjective homomorphisms induce surjective maps on topological abelianizations. -/
theorem surjective_map_of_surjective
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Type v} [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (f : G →ₜ* H) (hf : Function.Surjective f) :
    Function.Surjective (map f) := by
  intro y
  refine Quotient.inductionOn' y ?_
  intro h
  rcases hf h with ⟨g, rfl⟩
  exact ⟨QuotientGroup.mk' (Subgroup.closedCommutator G) g, rfl⟩

/--
In a commutative \(T_1\) topological group, the natural map to the topological abelianization is
injective.
-/
theorem injective_mk_of_commGroup
    {G : Type u} [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G] [T1Space G] :
    Function.Injective (mk G) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [ker_mk, closedCommutator_eq_bot_of_commGroup_t1]

/-- The canonical continuous equivalence for commutative \(T_1\) groups. -/
noncomputable def continuousMulEquivOfCommGroup
    (G : Type u) [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G] [T1Space G] :
    _root_.TopologicalAbelianization G ≃ₜ* G := by
  let e : G ≃* _root_.TopologicalAbelianization G :=
    MulEquiv.ofBijective (mk G)
      ⟨injective_mk_of_commGroup (G := G),
        QuotientGroup.mk'_surjective (Subgroup.closedCommutator G)⟩
  refine
    { toMulEquiv := e.symm
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · refine
      (QuotientGroup.isQuotientMap_mk
        (Subgroup.closedCommutator G)).continuous_iff.2 ?_
    change Continuous fun x : G => e.symm (e x)
    have heq : (fun x : G => e.symm (e x)) = id := by
      funext x
      exact e.symm_apply_apply x
    rw [heq]
    exact continuous_id
  · change Continuous fun x : G => mk G x
    exact QuotientGroup.continuous_mk

end TopologicalAbelianization

end ProCGroups.Abelian
