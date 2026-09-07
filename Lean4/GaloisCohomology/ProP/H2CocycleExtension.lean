import GaloisCohomology.ProP.FreeProPH2Cocycle

set_option autoImplicit false
/-!
# The central extension attached to a degree-two cocycle

A normalized continuous `ZMod p`-valued two-cocycle on a topological group `Q`
defines a twisted central extension of `Q`. This file packages that construction,
including its product topology, quotient projection, coefficient kernel, and the
finite `p`-group property needed for finite central embedding problems.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups
open FreeProPH2Cocycle

noncomputable section

universe u

variable {p : ℕ}
variable {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

/-- The twisted extension attached to a homogeneous degree-two cocycle.

Its underlying space is the product of the lifted additive coefficient group and
`Q`; its multiplication is twisted by the associated normalized cocycle. -/
structure H2CocycleExtension
    (z : Cohomology.trivialZModPCocyclesLifted p Q 2) where
  /-- The lifted `ZMod p` coefficient coordinate. -/
  left : A p
  /-- The base-group coordinate. -/
  right : Q

namespace H2CocycleExtension

variable (z : Cohomology.trivialZModPCocyclesLifted p Q 2)

@[ext]
theorem ext {x y : H2CocycleExtension z}
    (hleft : x.left = y.left) (hright : x.right = y.right) : x = y := by
  cases x
  cases y
  simp_all

@[reducible]
instance instGroup : Group (H2CocycleExtension z) where
  one := ⟨0, 1⟩
  mul x y :=
    ⟨x.left + y.left + normalizedCocycle z x.right y.right, x.right * y.right⟩
  inv x :=
    ⟨-x.left - normalizedCocycle z x.right⁻¹ x.right, x.right⁻¹⟩
  mul_assoc x y w := by
    apply ext
    · change
        (x.left + y.left + normalizedCocycle z x.right y.right) + w.left +
            normalizedCocycle z (x.right * y.right) w.right =
          x.left + (y.left + w.left + normalizedCocycle z y.right w.right) +
            normalizedCocycle z x.right (y.right * w.right)
      have hc := normalizedCocycle_cocycle z x.right y.right w.right
      calc
        _ = x.left + y.left + w.left +
            (normalizedCocycle z x.right y.right +
              normalizedCocycle z (x.right * y.right) w.right) := by abel
        _ = x.left + y.left + w.left +
            (normalizedCocycle z y.right w.right +
              normalizedCocycle z x.right (y.right * w.right)) := by rw [hc]
        _ = _ := by abel
    · exact mul_assoc _ _ _
  one_mul x := by
    apply ext
    · change 0 + x.left + normalizedCocycle z 1 x.right = x.left
      rw [normalizedCocycle_one_left]
      simp
    · exact one_mul _
  mul_one x := by
    apply ext
    · change x.left + 0 + normalizedCocycle z x.right 1 = x.left
      rw [normalizedCocycle_one_right]
      simp
    · exact mul_one _
  inv_mul_cancel x := by
    apply ext
    · change
        (-x.left - normalizedCocycle z x.right⁻¹ x.right) + x.left +
            normalizedCocycle z x.right⁻¹ x.right = 0
      abel
    · exact inv_mul_cancel _

/-- The underlying-type equivalence with the coefficient product. -/
def toProdEquiv : H2CocycleExtension z ≃ A p × Q where
  toFun x := (x.left, x.right)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instTopologicalSpace : TopologicalSpace (H2CocycleExtension z) :=
  TopologicalSpace.induced (toProdEquiv z) inferInstance

/-- The product-topology homeomorphism underlying the extension. -/
def toProdHomeomorph : H2CocycleExtension z ≃ₜ A p × Q :=
  (toProdEquiv z).toHomeomorphOfIsInducing
    (Topology.IsInducing.induced (toProdEquiv z))

instance instCompactSpace [Fact p.Prime] [CompactSpace Q] :
    CompactSpace (H2CocycleExtension z) :=
  (toProdHomeomorph z).symm.compactSpace

instance instT2Space [T2Space Q] : T2Space (H2CocycleExtension z) :=
  (toProdHomeomorph z).symm.t2Space

instance instTotallyDisconnectedSpace [TotallyDisconnectedSpace Q] :
    TotallyDisconnectedSpace (H2CocycleExtension z) :=
  (toProdHomeomorph z).symm.totallyDisconnectedSpace

instance instContinuousMul [LocallyCompactSpace Q] :
    ContinuousMul (H2CocycleExtension z) := ⟨by
  rw [continuous_induced_rng]
  change Continuous fun xy : H2CocycleExtension z × H2CocycleExtension z =>
    (xy.1.left + xy.2.left + normalizedCocycle z xy.1.right xy.2.right,
      xy.1.right * xy.2.right)
  have hecont : Continuous (toProdEquiv z) := continuous_induced_dom
  have hleft : Continuous fun x : H2CocycleExtension z => x.left :=
    continuous_fst.comp hecont
  have hright : Continuous fun x : H2CocycleExtension z => x.right :=
    continuous_snd.comp hecont
  have hc : Continuous fun xy : H2CocycleExtension z × H2CocycleExtension z =>
      normalizedCocycle z xy.1.right xy.2.right :=
    (normalizedCocycle_continuous z).comp
      ((hright.comp continuous_fst).prodMk (hright.comp continuous_snd))
  exact (((hleft.comp continuous_fst).add (hleft.comp continuous_snd)).add hc).prodMk
    ((hright.comp continuous_fst).mul (hright.comp continuous_snd))⟩

instance instContinuousInv [LocallyCompactSpace Q] :
    ContinuousInv (H2CocycleExtension z) := ⟨by
  rw [continuous_induced_rng]
  change Continuous fun x : H2CocycleExtension z =>
    (-x.left - normalizedCocycle z x.right⁻¹ x.right, x.right⁻¹)
  have hecont : Continuous (toProdEquiv z) := continuous_induced_dom
  have hleft : Continuous fun x : H2CocycleExtension z => x.left :=
    continuous_fst.comp hecont
  have hright : Continuous fun x : H2CocycleExtension z => x.right :=
    continuous_snd.comp hecont
  have hc : Continuous fun x : H2CocycleExtension z =>
      normalizedCocycle z x.right⁻¹ x.right :=
    (normalizedCocycle_continuous z).comp (hright.inv.prodMk hright)
  exact (hleft.neg.sub hc).prodMk hright.inv⟩

instance instIsTopologicalGroup [LocallyCompactSpace Q] :
    IsTopologicalGroup (H2CocycleExtension z) :=
  IsTopologicalGroup.mk

/-- The canonical continuous projection from the cocycle extension to `Q`. -/
def projection : H2CocycleExtension z →ₜ* Q where
  toFun x := x.right
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    continuous_snd.comp
      (show Continuous (toProdEquiv z) from continuous_induced_dom)

@[simp]
theorem projection_apply (x : H2CocycleExtension z) : projection z x = x.right := rfl

theorem projection_surjective : Function.Surjective (projection z) := by
  intro q
  exact ⟨⟨0, q⟩, rfl⟩

/-- The kernel is the multiplicative wrapper of the lifted additive coefficient group. -/
def kernelMulEquiv : (projection z).ker ≃* Multiplicative (A p) where
  toFun x := x.1.left
  invFun a := ⟨⟨a, 1⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply ext
    · rfl
    · have hx : x.1.right = 1 := x.property
      exact hx.symm
  right_inv _ := rfl
  map_mul' x y := by
    change x.1.left + y.1.left + normalizedCocycle z x.1.right y.1.right =
      x.1.left + y.1.left
    have hx : x.1.right = 1 := x.property
    have hy : y.1.right = 1 := y.property
    rw [hx, hy, normalizedCocycle_one_left]
    simp

/-- Additively, the kernel is exactly the lifted copy of `ZMod p`. -/
def kernelAddEquiv : Additive ((projection z).ker) ≃+ A p :=
  (kernelMulEquiv z).toAdditive.trans (AddEquiv.additiveMultiplicative (A p))

instance instFiniteKernel [Fact p.Prime] : Finite (projection z).ker :=
  Finite.of_equiv (Multiplicative (A p)) (kernelMulEquiv z).symm.toEquiv

theorem kernel_isPGroup [Fact p.Prime] : IsPGroup p (projection z).ker := by
  have hA : IsPGroup p (Multiplicative (A p)) := by
    apply IsPGroup.of_card (n := 1)
    simp [A]
  exact hA.of_equiv (kernelMulEquiv z).symm

/-- The coefficient kernel is central in the cocycle extension. -/
theorem kernel_le_center : (projection z).ker ≤ Subgroup.center (H2CocycleExtension z) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  change x.right = 1 at hx
  apply ext
  · change
      y.left + x.left + normalizedCocycle z y.right x.right =
        x.left + y.left + normalizedCocycle z x.right y.right
    rw [hx, normalizedCocycle_one_left, normalizedCocycle_one_right]
    simp [add_comm]
  · change y.right * x.right = x.right * y.right
    rw [hx]
    simp

instance instFinite [Fact p.Prime] [Finite Q] : Finite (H2CocycleExtension z) :=
  Finite.of_equiv (A p × Q) (toProdEquiv z).symm

/-- A cocycle extension of a finite `p`-group by `ZMod p` is again a finite `p`-group. -/
theorem isPGroup [Fact p.Prime] [Finite Q] (hQ : IsPGroup p Q) :
    IsPGroup p (H2CocycleExtension z) := by
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hQ
  apply IsPGroup.of_card (n := n + 1)
  rw [Nat.card_congr (toProdEquiv z)]
  simp [A, hn, pow_succ, Nat.mul_comm]

end H2CocycleExtension

end

end ClassFieldTower.ProP
