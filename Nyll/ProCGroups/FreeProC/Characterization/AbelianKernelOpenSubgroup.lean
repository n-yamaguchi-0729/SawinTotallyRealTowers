/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FreeProC.Characterization.AbelianKernelEmbeddingProblems
import Nyll.ProCGroups.FreeProC.Characterization.OpenSubgroupFiniteQuotient
import Nyll.ProCGroups.InducedFunctions
import Nyll.ProCGroups.InducedSemidirect
import Nyll.ProCGroups.GroupTheory.SplitSemidirect
import Nyll.ProCGroups.GroupTheory.SemidirectSubgroups
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Split abelian-kernel solvability passes to open subgroups

A finite quotient of the open subgroup is placed inside an actual finite
ambient quotient. Inducing its kernel action gives a split problem for the
ambient group. Its proper solution restricts surjectively to the required
semidirect subgroup, and evaluation recovers the original problem.
-/

namespace ProCGroups.FreeProC.Characterization

open ProCGroups.InducedFunctions

universe u

variable {C : FiniteGroupClass.{u}}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Apply the solver to the actual right projection, using the isomorphism
of its kernel with the specified commutative coefficient group. -/
private theorem exists_semidirect_lift
    (hsolve : HasFiniteSplitAbelianKernelEmbeddingSolutions C G)
    {Q I : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [Finite Q] [DiscreteTopology Q] [CommGroup I]
    (φ : Q →* MulAut I) [TopologicalSpace (I ⋊[φ] Q)]
    [DiscreteTopology (I ⋊[φ] Q)]
    (hI : C I) (q : G →ₜ* Q) (hq : Function.Surjective q) :
    ∃ σ : G →ₜ* I ⋊[φ] Q, Function.Surjective σ ∧
      ∀ g : G, (σ g).right = q g := by
  have : Finite I := C.finite_of_mem hI
  have : Finite (I ⋊[φ] Q) :=
    Finite.of_equiv (I × Q) SemidirectProduct.equivProd.symm
  let α : (I ⋊[φ] Q) →ₜ* Q :=
    { toMonoidHom := SemidirectProduct.rightHom
      continuous_toFun := continuous_of_discreteTopology }
  let s : Q →ₜ* I ⋊[φ] Q :=
    { toMonoidHom := SemidirectProduct.inr
      continuous_toFun := continuous_of_discreteTopology }
  let P : TopologicalEmbeddingProblem G :=
    ⟨TopGrp.of (I ⋊[φ] Q), TopGrp.of Q, α,
      SemidirectProduct.rightHom_surjective, q, hq⟩
  have hsplit : P.IsSplit := by
    refine ⟨s, ?_⟩
    apply ContinuousMonoidHom.ext
    intro x
    change (SemidirectProduct.rightHom : (I ⋊[φ] Q) →* Q)
      ((SemidirectProduct.inr : Q →* I ⋊[φ] Q) x) = x
    exact SemidirectProduct.rightHom_inr x
  have hker : C α.toMonoidHom.ker :=
    C.mem_of_mulEquiv (semidirectRightKernelEquiv φ).symm hI
  have hcomm : ∀ a b : α.toMonoidHom.ker, Commute (a : I ⋊[φ] Q) (b : I ⋊[φ] Q) := by
    intro a b
    have hab : a * b = b * a := by
      apply (semidirectRightKernelEquiv φ).injective
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val hab
  obtain ⟨σ⟩ := hsolve P inferInstance inferInstance inferInstance inferInstance
    hsplit hker hcomm
  refine ⟨σ.val, σ.property.1, ?_⟩
  intro g
  exact DFunLike.congr_fun σ.property.2 g

/-- Solvability of all finite split embedding problems whose abelian kernel
belongs to `C` passes to open subgroups. Only subgroup and finite-product
closure of `C` are used; the whole covering and quotient groups are unrestricted. -/
theorem HasFiniteSplitAbelianKernelEmbeddingSolutions.openSubgroup
    (hsolve : HasFiniteSplitAbelianKernelEmbeddingSolutions C G)
    (hSub : C.SubgroupClosed) (hProd : C.FiniteProductClosed)
    [CompactSpace G] (H : OpenSubgroup G) :
    HasFiniteSplitAbelianKernelEmbeddingSolutions C (H : Subgroup G) := by
  classical
  intro P _hEfin _hEdisc _hBfin hBdisc hsplit hA hcomm
  have : DiscreteTopology P.B := hBdisc
  obtain ⟨s, hs⟩ := hsplit
  have hs' : P.α.toMonoidHom.comp s.toMonoidHom = MonoidHom.id P.B :=
    congrArg ContinuousMonoidHom.toMonoidHom hs
  obtain ⟨V, _hVH, η, ρ, _hη, hρ, hηval, hρη, hpreimage⟩ :=
    exists_finiteQuotient_factor_of_openSubgroup H P.φ P.surjective_φ
  let Q := G ⧸ (V : Subgroup G)
  let q : G →ₜ* Q := ProC.OpenNormalSubgroup.quotientProj V
  let J : Subgroup Q :=
    ((QuotientGroup.mk' (V : Subgroup G)).comp (H : Subgroup G).subtype).range
  let A := P.α.toMonoidHom.ker
  let : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun a b => Subtype.ext (hcomm a b).eq }
  let β : P.B →* MulAut A :=
    (MulAut.conjNormal : P.A →* MulAut A).comp s.toMonoidHom
  let : MulDistribMulAction J A :=
    MulDistribMulAction.compHom A (β.comp ρ.toMonoidHom)
  let I := InducedModule (B := A) J
  have hI : C I := by
    let : Fintype Q := Fintype.ofFinite Q
    exact hSub (inducedSubgroup (B := A) J)
      (hProd (G := fun _ : Q => A) (fun _ => hA))
  let φ : Q →* MulAut I := MulDistribMulAction.toMulAut Q I
  let W := I ⋊[φ] Q
  let : TopologicalSpace W := ⊥
  have : DiscreteTopology W := ⟨rfl⟩
  obtain ⟨σ, hσ, hσq⟩ := exists_semidirect_lift hsolve φ hI q
    (ProC.OpenNormalSubgroup.quotientProj_surjective V)
  let N : Subgroup W := J.comap (SemidirectProduct.rightHom : W →* Q)
  have hσH (h : H) : σ (h : G) ∈ N := by
    change (σ (h : G)).right ∈ J
    rw [hσq]
    exact (hpreimage (h : G)).mpr h.property
  let σH : H →ₜ* N :=
    { toMonoidHom :=
        (σ.toMonoidHom.comp (H : Subgroup G).subtype).codRestrict N hσH
      continuous_toFun :=
        (σ.continuous_toFun.comp continuous_subtype_val).subtype_mk hσH }
  have hσHsurj : Function.Surjective σH := by
    intro w
    obtain ⟨x, hx⟩ := hσ (w : W)
    have hxH : x ∈ H := (hpreimage x).mp (by
      change q x ∈ J
      rw [← hσq x, hx]
      exact w.property)
    exact ⟨⟨x, hxH⟩, Subtype.ext hx⟩
  let eN : N ≃* I ⋊[φ.comp J.subtype] J := semidirectRightPreimageEquiv φ J
  let ev : I ⋊[φ.comp J.subtype] J →*
      A ⋊[MulDistribMulAction.toMulAut J A] J :=
    inducedEvaluationSemidirectHom (A := A) J
  let push : A ⋊[MulDistribMulAction.toMulAut J A] J →* A ⋊[β] P.B :=
    SemidirectProduct.map (MonoidHom.id A) ρ.toMonoidHom (by
      intro j
      apply MonoidHom.ext
      intro a
      rfl)
  have hpush : Function.Surjective push := by
    intro x
    obtain ⟨j, hj⟩ := hρ x.right
    refine ⟨⟨x.left, j⟩, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact hj
  let eP : A ⋊[β] P.B ≃* P.A :=
    splitKernelSemidirectMulEquiv P.α.toMonoidHom s.toMonoidHom hs'
  let ψ : N →ₜ* P.A :=
    { toMonoidHom := eP.toMonoidHom.comp (push.comp (ev.comp eN.toMonoidHom))
      continuous_toFun := continuous_of_discreteTopology }
  have hψsurj : Function.Surjective ψ :=
    eP.surjective.comp (hpush.comp
      ((inducedEvaluationSemidirectHom_surjective (A := A) J).comp eN.surjective))
  have hψ (w : N) : P.α (ψ w) = ρ ⟨(w : W).right, w.property⟩ := by
    change P.α.toMonoidHom (splitKernelSemidirectMulEquiv P.α.toMonoidHom s.toMonoidHom hs'
      (push (ev (eN w)))) = ρ ⟨(w : W).right, w.property⟩
    rw [splitKernelSemidirectMulEquiv_commutes]
    rfl
  refine ⟨⟨ψ.comp σH, hψsurj.comp hσHsurj, ?_⟩⟩
  apply ContinuousMonoidHom.ext
  intro h
  change P.α (ψ (σH h)) = P.φ h
  rw [hψ]
  have hj : (⟨(σ (h : G)).right, hσH h⟩ : J) = η h :=
    Subtype.ext ((hσq (h : G)).trans (hηval h).symm)
  change ρ (⟨(σ (h : G)).right, hσH h⟩ : J) = P.φ h
  rw [hj]
  exact DFunLike.congr_fun hρη h

end ProCGroups.FreeProC.Characterization
