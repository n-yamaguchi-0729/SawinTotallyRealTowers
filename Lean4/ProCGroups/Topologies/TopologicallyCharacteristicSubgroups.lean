import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.GroupTheory.Commutator.Basic
import ProCGroups.Topologies.QuotientMaps

set_option autoImplicit false

/-!
# Topologically characteristic subgroups

This file studies subgroups invariant under continuous automorphisms. It proves invariance of the
closed commutator subgroup, gives equivalent map and comap formulations, and establishes closure
of topologically characteristic subgroups under lattice operations and topological closure.
-/

universe u

namespace TopologicalGroup

/-- Identify the image of a subgroup with its Subgroup.map. -/
lemma image_subtype_eq_map
    {G : Type u} [Group G]
    {H : Type _} [Group H]
    (f : G →* H) (K : Subgroup G) :
    (fun x : G => f x) '' (K : Set G) = ((K.map f : Subgroup H) : Set H) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/--
Mapping a subgroup by the inverse of an automorphism agrees with comapping along the
automorphism itself.
-/
lemma map_symm_toMonoidHom_eq_comap
    {G : Type u} [Group G] (K : Subgroup G) (e : G ≃* G) :
    K.map e.symm.toMonoidHom = K.comap e.toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change e (e.symm y) ∈ K
    simpa using hy
  · intro hx
    have hx' : e x ∈ K := by
      simpa [Subgroup.mem_comap] using hx
    exact ⟨e x, hx', by simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        MulEquiv.symm_apply_apply]⟩

end TopologicalGroup

namespace Subgroup

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable {H K : Subgroup G}

/--
Continuous maps send the topological closure of a subgroup into a closed subgroup whenever they
send the subgroup itself into that closed subgroup.
-/
theorem map_topologicalClosure_le_of_map_le
    {G H : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace H] [Group H]
    {A : Subgroup G} {B : Subgroup H} {f : G →* H}
    (hf : Continuous f) (hAB : A.map f ≤ B) (hB : IsClosed (B : Set H)) :
    A.topologicalClosure.map f ≤ B := by
  have hMapsTo : Set.MapsTo (fun x : G => f x) (A : Set G) (B : Set H) := by
    intro x hx
    exact hAB ⟨x, hx, rfl⟩
  have hMapsTo_cl :
      Set.MapsTo (fun x : G => f x) (_root_.closure (A : Set G)) (B : Set H) :=
    Set.MapsTo.closure_left hMapsTo hf hB
  rintro y ⟨x, hx, rfl⟩
  exact hMapsTo_cl hx

/-- Homeomorphic group equivalences commute with topological closure of subgroups. -/
theorem map_topologicalClosure_eq_of_continuousMulEquiv
    {G H : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (A : Subgroup G) :
    A.topologicalClosure.map e.toMulEquiv.toMonoidHom =
      (A.map e.toMulEquiv.toMonoidHom).topologicalClosure := by
  apply SetLike.coe_injective
  calc
    ((A.topologicalClosure.map e.toMulEquiv.toMonoidHom : Subgroup H) : Set H) =
        e.toHomeomorph '' ((A.topologicalClosure : Subgroup G) : Set G) := by
          symm
          exact TopologicalGroup.image_subtype_eq_map
            (f := e.toMulEquiv.toMonoidHom) (K := A.topologicalClosure)
    _ = e.toHomeomorph '' (_root_.closure ((A : Subgroup G) : Set G)) := by
          rw [show ((A.topologicalClosure : Subgroup G) : Set G) =
              _root_.closure ((A : Set G)) by
            exact topologicalClosure_coe]
    _ = _root_.closure (e.toHomeomorph '' ((A : Subgroup G) : Set G)) := by
          exact e.toHomeomorph.image_closure ((A : Subgroup G) : Set G)
    _ = _root_.closure (((A.map e.toMulEquiv.toMonoidHom : Subgroup H) : Set H)) := by
          exact congrArg _root_.closure
            (TopologicalGroup.image_subtype_eq_map
              (f := e.toMulEquiv.toMonoidHom) (K := A))
    _ = (((A.map e.toMulEquiv.toMonoidHom).topologicalClosure : Subgroup H) : Set H) := by
          symm
          exact topologicalClosure_coe

/-- The closed commutator subgroup of a topological group. -/
abbrev closedCommutator (G : Type*) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] : Subgroup G :=
  (_root_.commutator G).topologicalClosure

/-- The closed commutator subgroup is closed. -/
@[simp] theorem isClosed_closedCommutator
    (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    IsClosed (closedCommutator G : Set G) :=
  isClosed_topologicalClosure (s := _root_.commutator G)

/-- The abstract commutator subgroup is contained in the closed commutator subgroup. -/
theorem commutator_le_closedCommutator
    (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    _root_.commutator G ≤ closedCommutator G :=
  le_topologicalClosure (_root_.commutator G)

/--
In a discrete topological group, the topological closure of a subgroup is the subgroup itself.
-/
@[simp] theorem topologicalClosure_eq_self_of_discrete
    (H : Subgroup G) [DiscreteTopology G] :
    H.topologicalClosure = H := by
  apply SetLike.coe_injective
  rw [topologicalClosure_coe, closure_discrete]

/--
For a discrete group, the closed commutator subgroup agrees with the ordinary commutator
subgroup.
-/
@[simp] theorem closedCommutator_eq_commutator_of_discrete
    (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [DiscreteTopology G] :
    closedCommutator G = _root_.commutator G := by
  simp only [closedCommutator, topologicalClosure_eq_self_of_discrete]

/-- Continuous homomorphisms send closed commutator subgroups into closed commutator subgroups. -/
theorem closedCommutator_map_le
    {G H : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (f : G →ₜ* H) :
    (closedCommutator G).map f.toMonoidHom ≤ closedCommutator H := by
  have hcomm : (_root_.commutator G).map f.toMonoidHom ≤ closedCommutator H := by
    have hmap : (_root_.commutator G).map f.toMonoidHom ≤ _root_.commutator H := by
      rw [_root_.map_commutator_eq]
      exact Subgroup.commutator_mono le_top le_top
    exact hmap.trans (commutator_le_closedCommutator H)
  exact map_topologicalClosure_le_of_map_le
    (f := f.toMonoidHom) f.continuous_toFun hcomm (isClosed_closedCommutator H)

/--
Continuous group equivalences map the closed commutator subgroup onto the closed commutator
subgroup.
-/
theorem closedCommutator_map_eq_of_equiv
    {G H : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) :
    (closedCommutator G).map e.toMulEquiv.toMonoidHom = closedCommutator H := by
  apply le_antisymm
  · exact closedCommutator_map_le
      { toMonoidHom := e.toMulEquiv.toMonoidHom
        continuous_toFun := e.continuous_toFun }
  · intro y hy
    have hy' :
        e.symm y ∈
          (closedCommutator H).map e.symm.toMulEquiv.toMonoidHom := ⟨y, hy, rfl⟩
    exact
      ⟨e.symm y,
        closedCommutator_map_le
          { toMonoidHom := e.symm.toMulEquiv.toMonoidHom
            continuous_toFun := e.symm.continuous_toFun } hy',
        e.apply_symm_apply y⟩

/-- The closed commutator subgroup is invariant under continuous automorphisms. -/
theorem closedCommutator_characteristic
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    ∀ e : G ≃ₜ* G,
      (closedCommutator G).map e.toMulEquiv.toMonoidHom = closedCommutator G :=
  fun e => closedCommutator_map_eq_of_equiv e

/-- A subgroup is topologically characteristic if every continuous automorphism preserves it. -/
structure TopologicallyCharacteristic
    (H : Subgroup G) : Prop where
  /-- Pulling back \(H\) along any continuous automorphism of \(G\) leaves \(H\) unchanged. -/
  comap_eq : ∀ e : G ≃ₜ* G, H.comap e.toMulEquiv.toMonoidHom = H

attribute [class] TopologicallyCharacteristic

/-- Every abstractly characteristic subgroup is invariant under continuous automorphisms. -/
instance topologicallyCharacteristic_of_characteristic
    [H.Characteristic] :
    H.TopologicallyCharacteristic := by
  refine ⟨?_⟩
  intro e
  simpa using
    (Subgroup.characteristic_iff_comap_eq.mp (show H.Characteristic by infer_instance)
      e.toMulEquiv)

omit [IsTopologicalGroup G] in
/--
Topological characteristicity is equivalent to invariance under comap by every continuous
automorphism.
-/
theorem topologicallyCharacteristic_iff_comap_eq :
    H.TopologicallyCharacteristic ↔
      ∀ e : G ≃ₜ* G, H.comap e.toMulEquiv.toMonoidHom = H :=
  ⟨TopologicallyCharacteristic.comap_eq, TopologicallyCharacteristic.mk⟩

omit [IsTopologicalGroup G] in
/--
A subgroup is topologically characteristic exactly when every automorphism comap is contained in
it.
-/
theorem topologicallyCharacteristic_iff_comap_le :
    H.TopologicallyCharacteristic ↔
      ∀ e : G ≃ₜ* G, H.comap e.toMulEquiv.toMonoidHom ≤ H :=
  topologicallyCharacteristic_iff_comap_eq.trans
    ⟨fun h e => le_of_eq (h e), fun h e =>
      le_antisymm (h e) fun g hg =>
        h e.symm ((congrArg (fun x => x ∈ H) (e.symm_apply_apply g)).mpr hg)⟩

omit [IsTopologicalGroup G] in
/--
A subgroup is topologically characteristic exactly when it is contained in every automorphism
comap.
-/
theorem topologicallyCharacteristic_iff_le_comap :
    H.TopologicallyCharacteristic ↔
      ∀ e : G ≃ₜ* G, H ≤ H.comap e.toMulEquiv.toMonoidHom :=
  topologicallyCharacteristic_iff_comap_eq.trans
    ⟨fun h e => ge_of_eq (h e), fun h e =>
      le_antisymm
        (fun g hg =>
          (congrArg (fun x => x ∈ H) (e.symm_apply_apply g)).mp (h e.symm hg))
        (h e)⟩

omit [IsTopologicalGroup G] in
/--
Topological characteristicity is equivalent to invariance under image by every continuous
automorphism.
-/
theorem topologicallyCharacteristic_iff_map_eq :
    H.TopologicallyCharacteristic ↔
      ∀ e : G ≃ₜ* G, H.map e.toMulEquiv.toMonoidHom = H := by
  simp_rw [map_equiv_eq_comap_symm']
  exact topologicallyCharacteristic_iff_comap_eq.trans
    ⟨fun h e => h e.symm, fun h e => h e.symm⟩

/-- The closed commutator subgroup is topologically characteristic. -/
theorem closedCommutator_topologicallyCharacteristic
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    (closedCommutator G).TopologicallyCharacteristic := by
  rw [topologicallyCharacteristic_iff_map_eq]
  exact closedCommutator_characteristic

omit [IsTopologicalGroup G] in
/--
A subgroup is topologically characteristic exactly when it is contained in every automorphism
image.
-/
theorem topologicallyCharacteristic_iff_le_map :
    H.TopologicallyCharacteristic ↔
      ∀ e : G ≃ₜ* G, H ≤ H.map e.toMulEquiv.toMonoidHom := by
  simp_rw [map_equiv_eq_comap_symm']
  exact topologicallyCharacteristic_iff_le_comap.trans
    ⟨fun h e => h e.symm, fun h e => h e.symm⟩

namespace TopologicallyCharacteristic

omit [IsTopologicalGroup G] in
/--
A topologically characteristic subgroup is fixed by the image of every continuous automorphism.
-/
lemma map_eq
    (hH : H.TopologicallyCharacteristic) (e : G ≃ₜ* G) :
    H.map (e.toMulEquiv.toMonoidHom) = H := by
  calc
    H.map (e.toMulEquiv.toMonoidHom)
        = H.comap (e.symm.toMulEquiv.toMonoidHom) := by
            ext x
            constructor
            · rintro ⟨y, hy, rfl⟩
              change e.symm (e y) ∈ H
              simpa using hy
            · intro hx
              change e.symm x ∈ H at hx
              exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    _ = H := hH.comap_eq e.symm

omit [IsTopologicalGroup G] in
/--
Membership in a topologically characteristic subgroup is invariant under applying a continuous
automorphism.
-/
lemma apply_mem_iff
    (hH : H.TopologicallyCharacteristic) (e : G ≃ₜ* G) {g : G} :
    e g ∈ H ↔ g ∈ H := by
  change g ∈ H.comap e.toMulEquiv.toMonoidHom ↔ g ∈ H
  rw [hH.comap_eq e]

omit [IsTopologicalGroup G] in
/-- Intersections of topologically characteristic subgroups are topologically characteristic. -/
theorem inf
    (hH : H.TopologicallyCharacteristic) (hK : K.TopologicallyCharacteristic) :
    (H ⊓ K).TopologicallyCharacteristic := by
  rw [topologicallyCharacteristic_iff_comap_eq]
  intro e
  calc
    (H ⊓ K).comap e.toMulEquiv.toMonoidHom =
        H.comap e.toMulEquiv.toMonoidHom ⊓ K.comap e.toMulEquiv.toMonoidHom := by
          simpa using Subgroup.comap_inf H K e.toMulEquiv.toMonoidHom
    _ = H ⊓ K := by rw [hH.comap_eq e, hK.comap_eq e]

omit [IsTopologicalGroup G] in
/-- Supremums of topologically characteristic subgroups are topologically characteristic. -/
theorem sup
    (hH : H.TopologicallyCharacteristic) (hK : K.TopologicallyCharacteristic) :
    (H ⊔ K).TopologicallyCharacteristic := by
  rw [topologicallyCharacteristic_iff_map_eq]
  intro e
  calc
    (H ⊔ K).map e.toMulEquiv.toMonoidHom = H.map e.toMulEquiv.toMonoidHom ⊔
        K.map e.toMulEquiv.toMonoidHom := by
          simpa using Subgroup.map_sup H K e.toMulEquiv.toMonoidHom
    _ = H ⊔ K := by rw [map_eq hH e, map_eq hK e]

omit [IsTopologicalGroup G] in
/--
Arbitrary intersections of topologically characteristic subgroups are topologically
characteristic.
-/
theorem sInf
    {S : Set (Subgroup G)}
    (hS : ∀ L ∈ S, L.TopologicallyCharacteristic) :
    (sInf S).TopologicallyCharacteristic := by
  rw [topologicallyCharacteristic_iff_comap_eq]
  intro e
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_sInf, Subgroup.mem_sInf]
  constructor
  · intro hg L hL
    exact (apply_mem_iff (hS L hL) e (g := g)).1 (hg L hL)
  · intro hg L hL
    exact (apply_mem_iff (hS L hL) e (g := g)).2 (hg L hL)

omit [IsTopologicalGroup G] in
/--
Indexed intersections of topologically characteristic subgroups are topologically
characteristic.
-/
theorem iInf
    {ι : Sort*} {S : ι → Subgroup G}
    (hS : ∀ i, (S i).TopologicallyCharacteristic) :
    (⨅ i, S i).TopologicallyCharacteristic := by
  rw [topologicallyCharacteristic_iff_comap_eq]
  intro e
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_iInf, Subgroup.mem_iInf]
  constructor
  · intro hg i
    exact (apply_mem_iff (hS i) e (g := g)).1 (hg i)
  · intro hg i
    exact (apply_mem_iff (hS i) e (g := g)).2 (hg i)

omit [IsTopologicalGroup G] in
/-- Indexed supremums of topologically characteristic subgroups are topologically characteristic. -/
theorem iSup
    {ι : Sort*} {S : ι → Subgroup G}
    (hS : ∀ i, (S i).TopologicallyCharacteristic) :
    (⨆ i, S i).TopologicallyCharacteristic := by
  rw [topologicallyCharacteristic_iff_map_eq]
  intro e
  calc
    (⨆ i, S i).map e.toMulEquiv.toMonoidHom = ⨆ i, (S i).map e.toMulEquiv.toMonoidHom := by
      simpa using Subgroup.map_iSup e.toMulEquiv.toMonoidHom S
    _ = ⨆ i, S i := by
      simpa using iSup_congr (fun i => map_eq (hS i) e)

/--
The topological closure of a topologically characteristic subgroup is topologically
characteristic.
-/
theorem topologicalClosure
    (hH : H.TopologicallyCharacteristic) :
    H.topologicalClosure.TopologicallyCharacteristic := by
  rw [topologicallyCharacteristic_iff_map_eq]
  intro e
  apply SetLike.coe_injective
  calc
    (((H.topologicalClosure).map e.toMulEquiv.toMonoidHom : Subgroup G) : Set G) =
        e.toHomeomorph '' ((H.topologicalClosure : Subgroup G) : Set G) := by
          symm
          exact TopologicalGroup.image_subtype_eq_map
            (f := e.toMulEquiv.toMonoidHom) (K := H.topologicalClosure)
    _ = e.toHomeomorph '' (_root_.closure ((H : Subgroup G) : Set G)) := by
          rw [show (((H.topologicalClosure : Subgroup G) : Set G)) = _root_.closure ((H : Set G)) by
            exact Subgroup.topologicalClosure_coe]
    _ = _root_.closure (e.toHomeomorph '' ((H : Subgroup G) : Set G)) := by
          exact e.toHomeomorph.image_closure ((H : Subgroup G) : Set G)
    _ = _root_.closure (((H.map e.toMulEquiv.toMonoidHom : Subgroup G) : Set G)) := by
          exact congrArg _root_.closure
            (TopologicalGroup.image_subtype_eq_map
              (f := e.toMulEquiv.toMonoidHom) (K := H))
    _ = _root_.closure ((H : Subgroup G) : Set G) := by
          simpa using congrArg _root_.closure
            (congrArg (fun L : Subgroup G => (L : Set G)) (map_eq hH e))
    _ = ((H.topologicalClosure : Subgroup G) : Set G) := by
          symm
          exact Subgroup.topologicalClosure_coe

end TopologicallyCharacteristic

/-- The bottom subgroup is topologically characteristic. -/
instance botTopologicallyCharacteristic :
    (⊥ : Subgroup G).TopologicallyCharacteristic := inferInstance

/-- The top subgroup is topologically characteristic. -/
instance topTopologicallyCharacteristic :
    (⊤ : Subgroup G).TopologicallyCharacteristic := inferInstance

/-- Commutators of topologically characteristic subgroups are topologically characteristic. -/
instance commutatorTopologicallyCharacteristic
    [H.TopologicallyCharacteristic] [K.TopologicallyCharacteristic] :
    (⁅H, K⁆).TopologicallyCharacteristic := by
  refine topologicallyCharacteristic_iff_le_map.mpr ?_
  intro e
  have hHle :
      H ≤ H.map e.toMulEquiv.toMonoidHom :=
    topologicallyCharacteristic_iff_le_map.mp
      (show H.TopologicallyCharacteristic by infer_instance) e
  have hKle :
      K ≤ K.map e.toMulEquiv.toMonoidHom :=
    topologicallyCharacteristic_iff_le_map.mp
      (show K.TopologicallyCharacteristic by infer_instance) e
  exact Subgroup.commutator_le_map_commutator
    hHle hKle

/-- The center is topologically characteristic. -/
instance centerTopologicallyCharacteristic :
    (center G).TopologicallyCharacteristic := inferInstance

/--
The centralizer of a topologically characteristic subgroup is again topologically
characteristic.
-/
instance topologicallyCharacteristic_centralizerInst
    [hH : H.TopologicallyCharacteristic] :
    (centralizer (H : Set G)).TopologicallyCharacteristic := by
  refine topologicallyCharacteristic_iff_comap_le.mpr ?_
  intro e g hg
  have hg' : e g ∈ centralizer (H : Set G) := hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  apply e.toMulEquiv.injective
  rw [e.toMulEquiv.map_mul, e.toMulEquiv.map_mul]
  exact
    hg' (e h) ((TopologicallyCharacteristic.apply_mem_iff (hH := inferInstance) e (g := h)).2 hh)

/-- Topologically characteristic subgroups are normal. -/
instance topologicallyCharacteristic_normalInst
    [H.TopologicallyCharacteristic] :
    H.Normal := by
  refine ⟨?_⟩
  intro x hx g
  let e : G ≃ₜ* G :=
    { toMulEquiv := MulAut.conj g
      continuous_toFun := by
        dsimp [MulAut.conj_apply]
        exact IsTopologicalGroup.continuous_conj (G := G) g
      continuous_invFun := by
        change Continuous fun h : G => g⁻¹ * h * g
        simpa only [inv_inv] using
          (IsTopologicalGroup.continuous_conj (G := G) (g := g⁻¹)) }
  have hmap : H.map (e.toMulEquiv.toMonoidHom) = H :=
    TopologicallyCharacteristic.map_eq (hH := inferInstance) e
  have hxmap : e x ∈ H.map (e.toMulEquiv.toMonoidHom) := ⟨x, hx, rfl⟩
  rw [hmap] at hxmap
  simpa [e, MulAut.conj_apply] using hxmap

namespace TopologicallyCharacteristic

/--
A continuous automorphism descends to the quotient by a topologically characteristic subgroup.
-/
noncomputable def quotientMulEquiv
    (hH : H.TopologicallyCharacteristic) (e : G ≃ₜ* G) :
    G ⧸ H ≃* G ⧸ H := by
  letI : H.Normal := by infer_instance
  exact QuotientGroup.congr H H e.toMulEquiv (map_eq hH e)

/--
The quotient equivalence induced by a topologically characteristic subgroup sends
representatives to representatives.
-/
@[simp] theorem quotientMulEquiv_mk
    (hH : H.TopologicallyCharacteristic) (e : G ≃ₜ* G) (g : G) :
    hH.quotientMulEquiv e (QuotientGroup.mk' H g) =
      QuotientGroup.mk' H (e g) := by
  rfl

/--
A topologically characteristic subgroup induces the corresponding continuous multiplicative
equivalence on quotients.
-/
noncomputable def quotientContinuousMulEquiv
    (hH : H.TopologicallyCharacteristic) (e : G ≃ₜ* G) :
    G ⧸ H ≃ₜ* G ⧸ H := by
  letI : H.Normal := by infer_instance
  exact ProCGroups.QuotientGroup.congrₜ H H e (map_eq hH e)

/--
The continuous quotient equivalence induced by a topologically characteristic subgroup sends
representatives to representatives.
-/
@[simp] theorem quotientContinuousMulEquiv_mk
    (hH : H.TopologicallyCharacteristic) (e : G ≃ₜ* G) (g : G) :
    hH.quotientContinuousMulEquiv e (QuotientGroup.mk' H g) =
      QuotientGroup.mk' H (e g) := by
  rfl

end TopologicallyCharacteristic

end Subgroup
