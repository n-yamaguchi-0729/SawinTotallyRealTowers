/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Nyll.ProCGroups.InverseSystems.CompatibilityAndSurjectivity

/-!
# Exact sequences of group-valued inverse systems

This module bundles morphisms whose stage maps are group homomorphisms and constructs the
induced homomorphisms on inverse limits.  For compact Hausdorff directed systems with surjective
transitions, it lifts stagewise kernel-image exactness to exactness of the inverse-limit maps.
-/

universe u v

namespace ProCGroups

namespace InverseSystems.InverseSystem

variable {I : Type u} [Preorder I]
variable {S T U : InverseSystems.InverseSystem (I := I)}
attribute [local instance] InverseSystems.InverseSystem.topologicalSpace
/-- Use the topology stored by the source inverse system at stage `i`. -/
instance instTopologicalSpaceS (i : I) : TopologicalSpace (S.X i) := S.topologicalSpace i
/-- Use the topology stored by the middle inverse system at stage `i`. -/
instance instTopologicalSpaceT (i : I) : TopologicalSpace (T.X i) := T.topologicalSpace i
/-- Use the topology stored by the target inverse system at stage `i`. -/
instance instTopologicalSpaceU (i : I) : TopologicalSpace (U.X i) := U.topologicalSpace i
variable [∀ i, Group (S.X i)] [∀ i, Group (T.X i)] [∀ i, Group (U.X i)]

/-- A morphism of group-valued inverse systems with homomorphism laws bundled componentwise. -/
structure GroupMorphism (S T : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [∀ i, Group (T.X i)] extends S.Morphism T where
  /-- Each stage map sends the source identity to the target identity. -/
  map_one' : ∀ i, map i 1 = 1
  /-- Each stage map preserves multiplication and therefore defines a group homomorphism. -/
  map_mul' : ∀ i (x y : S.X i), map i (x * y) = map i x * map i y

namespace GroupMorphism

/-- A bundled group morphism built from componentwise continuous monoid homomorphisms. -/
def ofContinuousMonoidHom
    (φ : ∀ i, S.X i →ₜ* T.X i)
    (hcomm : ∀ {i j : I} (hij : i ≤ j),
      T.map hij ∘ φ j = φ i ∘ S.map hij) :
    GroupMorphism S T where
  map := fun i => φ i
  continuous_map := fun i => (φ i).continuous_toFun
  comm := hcomm
  map_one' := fun i => (φ i).map_one
  map_mul' := fun i => (φ i).map_mul

/--
The group-system morphism built from continuous monoid homomorphisms has the prescribed stage
maps.
-/
@[simp] theorem ofContinuousMonoidHom_map
    (φ : ∀ i, S.X i →ₜ* T.X i)
    (hcomm : ∀ {i j : I} (hij : i ≤ j),
      T.map hij ∘ φ j = φ i ∘ S.map hij)
    (i : I) (x : S.X i) :
    (ofContinuousMonoidHom (S := S) (T := T) φ hcomm).map i x = φ i x :=
  rfl

/-- The identity morphism of an inverse system. -/
def id (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] :
    GroupMorphism S S where
  toMorphism := InverseSystems.InverseSystem.Morphism.id S
  map_one' := fun _ => rfl
  map_mul' := fun _ _ _ => rfl

/-- The identity group-system morphism acts as the identity on each stage. -/
@[simp] theorem id_apply
    (i : I) (x : S.X i) :
    (id S).map i x = x :=
  rfl

/-- Group-valued inverse-system morphisms compose stagewise, preserving their homomorphism laws. -/
def comp (Ψ : GroupMorphism T U) (Θ : GroupMorphism S T) :
    GroupMorphism S U where
  toMorphism := InverseSystems.InverseSystem.Morphism.comp Ψ.toMorphism Θ.toMorphism
  map_one' := by
    intro i
    simp only [Morphism.comp_apply, Θ.map_one', Ψ.map_one']
  map_mul' := by
    intro i x y
    simp only [Morphism.comp_apply, Θ.map_mul', Ψ.map_mul']

/-- At each stage, the composite group morphism applies `Θ` first and then `Ψ`. -/
@[simp] theorem comp_apply (Ψ : GroupMorphism T U) (Θ : GroupMorphism S T)
    (i : I) (x : S.X i) :
    (comp Ψ Θ).map i x = Ψ.map i (Θ.map i x) :=
  rfl

end GroupMorphism

/-- A morphism of group-valued inverse systems induces a homomorphism on inverse limits. -/
def limMapMonoidHom (Θ : S.Morphism T)
    (hΘ_one : ∀ i, Θ.map i 1 = 1)
    (hΘ_mul : ∀ i (x y : S.X i), Θ.map i (x * y) = Θ.map i x * Θ.map i y)
    [InverseSystems.IsGroupSystem S] [InverseSystems.IsGroupSystem T] :
    S.inverseLimit →* T.inverseLimit where
  toFun := S.limMap Θ
  map_one' := by
    apply T.ext
    intro i
    have hpi := congrFun (S.π_comp_limMap (Θ := Θ) i) (1 : S.inverseLimit)
    calc
      T.projection i (S.limMap Θ 1) = Θ.map i (S.projection i 1) := by
        simpa [Function.comp] using hpi
      _ = Θ.map i 1 := by rfl
      _ = 1 := hΘ_one i
  map_mul' := by
    intro x y
    apply T.ext
    intro i
    have hxy := congrFun (S.π_comp_limMap (Θ := Θ) i) (x * y)
    have hx := congrFun (S.π_comp_limMap (Θ := Θ) i) x
    have hy := congrFun (S.π_comp_limMap (Θ := Θ) i) y
    have hx' : T.projection i (S.limMap Θ x) = Θ.map i (S.projection i x) := by
      simpa [Function.comp] using hx
    have hy' : T.projection i (S.limMap Θ y) = Θ.map i (S.projection i y) := by
      simpa [Function.comp] using hy
    calc
      T.projection i (S.limMap Θ (x * y)) = Θ.map i (S.projection i (x * y)) := by
        simpa [Function.comp] using hxy
      _ = Θ.map i (S.projection i x * S.projection i y) := by rfl
      _ = Θ.map i (S.projection i x) * Θ.map i (S.projection i y) :=
        hΘ_mul i (S.projection i x) (S.projection i y)
      _ = T.projection i (S.limMap Θ x) * T.projection i (S.limMap Θ y) := by
        rw [← hx', ← hy']

/--
Bundled group morphisms induce homomorphisms on inverse limits without repeating the
componentwise homomorphism laws.
-/
def GroupMorphism.limMapMonoidHom (Θ : GroupMorphism S T)
    [InverseSystems.IsGroupSystem S] [InverseSystems.IsGroupSystem T] :
    S.inverseLimit →* T.inverseLimit :=
  ProCGroups.InverseSystems.InverseSystem.limMapMonoidHom
    (S := S) (T := T) Θ.toMorphism Θ.map_one' Θ.map_mul'

/--
The inverse-limit homomorphism evaluates at each stage by applying the corresponding stage
homomorphism after projection.
-/
@[simp] theorem GroupMorphism.limMapMonoidHom_apply_π
    (Θ : GroupMorphism S T)
    [InverseSystems.IsGroupSystem S] [InverseSystems.IsGroupSystem T]
    (i : I) (x : S.inverseLimit) :
    T.projection i (Θ.limMapMonoidHom x) = Θ.map i (S.projection i x) := by
  simpa [GroupMorphism.limMapMonoidHom,
    ProCGroups.InverseSystems.InverseSystem.limMapMonoidHom] using
    congrFun (S.π_comp_limMap (Θ := Θ.toMorphism) i) x

/--
If the componentwise composite \(\Psi_i \circ \Theta_i\) is trivial, then the induced morphisms
on inverse limits also compose to the trivial homomorphism. This isolates the only
non-mathematical part of the range \(\subseteq\) kernel direction.
-/
theorem limMapMonoidHom_comp_eq_one
    {Θ : S.Morphism T} {Ψ : T.Morphism U}
    [InverseSystems.IsGroupSystem S] [InverseSystems.IsGroupSystem T]
        [InverseSystems.IsGroupSystem U]
    (hΘ_one : ∀ i, Θ.map i 1 = 1)
    (hΘ_mul : ∀ i (x y : S.X i), Θ.map i (x * y) = Θ.map i x * Θ.map i y)
    (hΨ_one : ∀ i, Ψ.map i 1 = 1)
    (hΨ_mul : ∀ i (x y : T.X i), Ψ.map i (x * y) = Ψ.map i x * Ψ.map i y)
    (hcomp : ∀ i, Ψ.map i ∘ Θ.map i = fun _ => 1) :
    limMapMonoidHom (S := T) (T := U) Ψ hΨ_one hΨ_mul ∘
        limMapMonoidHom (S := S) (T := T) Θ hΘ_one hΘ_mul =
      fun _ => 1 := by
  funext x
  apply U.ext
  intro i
  have hπΘ := congrFun (S.π_comp_limMap (Θ := Θ) i) x
  have hπΨ := congrFun (T.π_comp_limMap (Θ := Ψ) i) (S.limMap Θ x)
  have hπΘ' : T.projection i (S.limMap Θ x) = Θ.map i (S.projection i x) := by
    simpa [Function.comp] using hπΘ
  have hπΨ' :
      U.projection i (T.limMap Ψ (S.limMap Θ x)) = Ψ.map i (T.projection i (S.limMap Θ x)) := by
    simpa [Function.comp] using hπΨ
  have hcomp' : Ψ.map i (Θ.map i (S.projection i x)) = 1 := by
    simpa [Function.comp] using congrFun (hcomp i) (S.projection i x)
  calc
    U.projection i
        ((limMapMonoidHom (S := T) (T := U) Ψ hΨ_one hΨ_mul)
          ((limMapMonoidHom (S := S) (T := T) Θ hΘ_one hΘ_mul) x))
        = Ψ.map i (T.projection i (S.limMap Θ x)) := by
            simpa [limMapMonoidHom] using hπΨ'
    _ = Ψ.map i (Θ.map i (S.projection i x)) := by rw [hπΘ']
    _ = 1 := hcomp'
    _ = U.projection i (1 : U.inverseLimit) := rfl

/--
Inverse limits preserve short exact sequences of profinite groups when taken over a common
directed index category.
-/
theorem limMap_exact
    [∀ i, CompactSpace (T.X i)] [∀ i, T2Space (T.X i)] [∀ i, T2Space (U.X i)]
    [InverseSystems.IsGroupSystem S] [InverseSystems.IsGroupSystem T]
        [InverseSystems.IsGroupSystem U]
    {Θ : S.Morphism T} {Ψ : T.Morphism U}
    (hΘ_one : ∀ i, Θ.map i 1 = 1)
    (hΘ_mul : ∀ i (x y : S.X i), Θ.map i (x * y) = Θ.map i x * Θ.map i y)
    (hΨ_one : ∀ i, Ψ.map i 1 = 1)
    (hΨ_mul : ∀ i (x y : T.X i), Ψ.map i (x * y) = Ψ.map i x * Ψ.map i y)
    (hdir : Directed (· ≤ ·) (id : I → I))
    (hΘinj : ∀ i, Function.Injective (Θ.map i))
    (hΨsurj : ∀ i, Function.Surjective (Ψ.map i))
    (hcomp : ∀ i, Ψ.map i ∘ Θ.map i = fun _ => 1)
    (hexact : ∀ i, ∀ y : T.X i, Ψ.map i y = 1 ↔ ∃ x : S.X i, Θ.map i x = y) :
    Function.Injective (S.limMap Θ) ∧
      Function.Surjective (T.limMap Ψ) ∧
      Set.range (limMapMonoidHom (S := S) (T := T) Θ hΘ_one hΘ_mul) =
        (MonoidHom.ker
          (limMapMonoidHom (S := T) (T := U) Ψ hΨ_one hΨ_mul) : Set T.inverseLimit) := by
  have hinj : Function.Injective (S.limMap Θ) :=
    InverseSystems.InverseSystem.injective_limMap (S := S) (T := T) Θ hΘinj
  have hsurj : Function.Surjective (T.limMap Ψ) :=
    InverseSystems.InverseSystem.surjective_limMap (S := T) (T := U) hdir Ψ hΨsurj
  have hcomp_lim :=
    limMapMonoidHom_comp_eq_one (S := S) (T := T) (U := U)
      hΘ_one hΘ_mul hΨ_one hΨ_mul hcomp
  refine ⟨hinj, hsurj, ?_⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change limMapMonoidHom (S := T) (T := U) Ψ hΨ_one hΨ_mul (S.limMap Θ x) = 1
    simpa [Function.comp, limMapMonoidHom] using congrFun hcomp_lim x
  · intro hy
    have hy' :
        limMapMonoidHom (S := T) (T := U) Ψ hΨ_one hΨ_mul y = 1 := by
      simpa [MonoidHom.mem_ker] using hy
    have hycoord :
        ∀ i, Ψ.map i (T.projection i y) = 1 := by
      intro i
      calc
        Ψ.map i (T.projection i y) =
            U.projection i
              (limMapMonoidHom (S := T) (T := U) Ψ hΨ_one hΨ_mul y) := by
                symm
                exact GroupMorphism.limMapMonoidHom_apply_π
                  (Θ :=
                    { toMorphism := Ψ
                      map_one' := hΨ_one
                      map_mul' := hΨ_mul }) i y
        _ = U.projection i 1 := congrArg (fun z : U.inverseLimit => U.projection i z) hy'
        _ = 1 := rfl
    choose x hx using fun i => (hexact i (T.projection i y)).1 (hycoord i)
    let xlim : S.inverseLimit := ⟨x, by
      intro i j hij
      apply hΘinj i
      calc
        Θ.map i (S.map hij (x j))
            = T.map hij (Θ.map j (x j)) := by
                exact (congrFun (Θ.comm hij) (x j)).symm
        _ = T.map hij (T.projection j y) := by rw [hx j]
        _ = T.projection i y := T.projection_compatible y i j hij
        _ = Θ.map i (x i) := (hx i).symm⟩
    refine ⟨xlim, ?_⟩
    apply T.ext
    intro i
    exact hx i

end InverseSystems.InverseSystem

end ProCGroups
