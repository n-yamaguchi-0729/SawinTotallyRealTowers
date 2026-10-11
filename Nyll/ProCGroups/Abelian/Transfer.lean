/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Nyll.ProCGroups.ProC.Quotients.OpenSubgroupSections

/-! # Continuous transfer for open normal subgroups -/

namespace ProCGroups.FiniteStepSolvableQuotients
open ProCGroups.Abelian ProCGroups.ProC
universe u v

/-- The individual transfer term landing in an open normal subgroup. -/
noncomputable def openNormalTransferTerm
    {G : Type u} [TopologicalSpace G] [Group G]
    (N : OpenNormalSubgroup G)
    (q : G ⧸ (N : Subgroup G)) (g : G) :
    ↥(N : Subgroup G) := by
  let ρ : G ⧸ (N : Subgroup G) → G :=
    quotientOpenSubgroupSection (N : Subgroup G)
  let π : G →* G ⧸ (N : Subgroup G) :=
    QuotientGroup.mk' (N : Subgroup G)
  refine ⟨(ρ ((QuotientGroup.mk' (N : Subgroup G) g) * q))⁻¹ * g * ρ q, ?_⟩
  have hρ :
      Function.RightInverse ρ (QuotientGroup.mk (s := (N : Subgroup G))) :=
    quotientOpenSubgroupSection_rightInverse (N : Subgroup G)
  have hρ₁ :
      π (ρ ((QuotientGroup.mk' (N : Subgroup G) g) * q)) =
        (QuotientGroup.mk' (N : Subgroup G) g) * q := by
    simpa [π] using hρ ((QuotientGroup.mk' (N : Subgroup G) g) * q)
  have hρ₂ : π (ρ q) = q := by
    simpa [π] using hρ q
  have hmem :
      π ((ρ ((QuotientGroup.mk' (N : Subgroup G) g) * q))⁻¹ * g * ρ q) = 1 := by
    calc
      π ((ρ ((QuotientGroup.mk' (N : Subgroup G) g) * q))⁻¹ * g * ρ q) =
          (π (ρ ((QuotientGroup.mk' (N : Subgroup G) g) * q)))⁻¹ * π g * π (ρ q) := by
            simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv, π]
      _ =
          (((QuotientGroup.mk' (N : Subgroup G) g) * q))⁻¹ *
            QuotientGroup.mk' (N : Subgroup G) g * q := by
              rw [hρ₁, hρ₂]
      _ = 1 := by
        simp only [QuotientGroup.mk'_apply, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  exact
    (QuotientGroup.eq_one_iff
      (N := (N : Subgroup G))
      ((ρ ((QuotientGroup.mk' (N : Subgroup G) g) * q))⁻¹ * g * ρ q)).1 hmem

/-- Transfer on topological abelianization, before passing to the quotient universal property. -/
noncomputable def openNormalTransferTopologicalAbelianizationPre
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : OpenNormalSubgroup G) [Finite (G ⧸ (N : Subgroup G))] :
    G →ₜ* TopologicalAbelianization ↥(N : Subgroup G) := by
  classical
  letI : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
  refine
    { toMonoidHom :=
        { toFun := fun g =>
            ∏ q : G ⧸ (N : Subgroup G),
              TopologicalAbelianization.mk ↥(N : Subgroup G)
                (openNormalTransferTerm (G := G) N q g)
          map_one' := by
            let f : G ⧸ (N : Subgroup G) → TopologicalAbelianization ↥(N : Subgroup G) :=
              fun q =>
                TopologicalAbelianization.mk ↥(N : Subgroup G)
                  (openNormalTransferTerm (G := G) N q 1)
            have hf : ∀ q : G ⧸ (N : Subgroup G), f q = 1 := by
              intro q
              change
                TopologicalAbelianization.mk ↥(N : Subgroup G)
                  (openNormalTransferTerm (G := G) N q 1) = 1
              have hterm : openNormalTransferTerm (G := G) N q 1 = 1 := by
                apply Subtype.ext
                simp only [openNormalTransferTerm, QuotientGroup.mk'_apply,
                    QuotientGroup.mk_one, one_mul, mul_one,
  inv_mul_cancel, OneMemClass.coe_one]
              simp only [ContinuousMonoidHom.coe_toMonoidHom, hterm, map_one]
            simpa [f] using Fintype.prod_eq_one f hf
          map_mul' := by
            intro g h
            let f : G ⧸ (N : Subgroup G) → TopologicalAbelianization ↥(N : Subgroup G) :=
              fun q =>
                TopologicalAbelianization.mk ↥(N : Subgroup G)
                  (openNormalTransferTerm (G := G) N q g)
            let k : G ⧸ (N : Subgroup G) → TopologicalAbelianization ↥(N : Subgroup G) :=
              fun q =>
                TopologicalAbelianization.mk ↥(N : Subgroup G)
                  (openNormalTransferTerm (G := G) N q h)
            calc
              (∏ q : G ⧸ (N : Subgroup G),
                  TopologicalAbelianization.mk ↥(N : Subgroup G)
                    (openNormalTransferTerm (G := G) N q (g * h))) =
                ∏ q : G ⧸ (N : Subgroup G),
                  f ((QuotientGroup.mk' (N : Subgroup G) h) * q) * k q := by
                    apply Fintype.prod_congr
                    intro q
                    have hterm :
                        openNormalTransferTerm (G := G) N q (g * h) =
                          openNormalTransferTerm (G := G) N
                            ((QuotientGroup.mk' (N : Subgroup G) h) * q) g *
                          openNormalTransferTerm (G := G) N q h := by
                      apply Subtype.ext
                      dsimp [openNormalTransferTerm]
                      simp only [mul_assoc, mul_inv_cancel_left]
                    have hterm :=
                      congrArg (TopologicalAbelianization.mk ↥(N : Subgroup G)) hterm
                    simpa [f, k, map_mul] using hterm
              _ =
                (∏ q : G ⧸ (N : Subgroup G), f ((QuotientGroup.mk' (N : Subgroup G) h) * q)) *
                  ∏ q : G ⧸ (N : Subgroup G), k q := by
                    rw [Finset.prod_mul_distrib]
              _ = (∏ q : G ⧸ (N : Subgroup G), f q) * ∏ q : G ⧸ (N : Subgroup G), k q := by
                    exact congrArg
                      (fun z => z * ∏ q : G ⧸ (N : Subgroup G), k q)
                      (Equiv.prod_comp
                        (Equiv.mulLeft (QuotientGroup.mk' (N : Subgroup G) h)) f)
              _ = _ := rfl }
      continuous_toFun := by
        exact continuous_finsetProd Finset.univ fun q _ => by
          let ρ : G ⧸ (N : Subgroup G) → G :=
            quotientOpenSubgroupSection (N : Subgroup G)
          let π : G →ₜ* (G ⧸ (N : Subgroup G)) :=
            { toMonoidHom := QuotientGroup.mk' (N : Subgroup G)
              continuous_toFun := continuous_quotient_mk' }
          have hρcont : Continuous ρ := by
            let : DiscreteTopology (G ⧸ (N : Subgroup G)) :=
              QuotientGroup.discreteTopology N.isOpen'
            simpa [ρ] using
              (continuous_of_discreteTopology :
                Continuous (quotientOpenSubgroupSection (N : Subgroup G)))
          have hqcont : Continuous (fun g : G => π g * q) := by
            change Continuous
              (fun g : G => ((↑g : G ⧸ (N : Subgroup G))) * q)
            exact
              (QuotientGroup.continuous_mk :
                Continuous ((↑) : G → G ⧸ (N : Subgroup G))).mul continuous_const
          have hbase :
              Continuous (fun g : G =>
                (ρ ((QuotientGroup.mk' (N : Subgroup G) g) * q))⁻¹ * g * ρ q) := by
            exact ((hρcont.comp hqcont).inv.mul continuous_id).mul continuous_const
          exact
            (continuous_quotient_mk' :
              Continuous (TopologicalAbelianization.mk ↥(N : Subgroup G))).comp
              (Continuous.subtype_mk hbase (fun g => (openNormalTransferTerm (G := G) N q g).2)) }

/--
Open normal subgroups transfer through the topological abelianization by taking the appropriate
preimage or image under the quotient map.
-/
noncomputable def openNormalTransferTopologicalAbelianization
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : OpenNormalSubgroup G) [Finite (G ⧸ (N : Subgroup G))] :
    TopologicalAbelianization G →ₜ* TopologicalAbelianization ↥(N : Subgroup G) :=
  TopologicalAbelianization.lift
    (openNormalTransferTopologicalAbelianizationPre (G := G) N)

/-- Transfer sends a fixed point to the \(|G/N|\)-th power of that point. -/
theorem openNormalTransferTopologicalAbelianization_eq_pow_of_fixed
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : OpenNormalSubgroup G) [Finite (G ⧸ (N : Subgroup G))]
    {a : TopologicalAbelianization ↥(N : Subgroup G)}
    (hfix :
      ∀ q : G ⧸ (N : Subgroup G),
        quotientConjugationTopologicalAbelianizationMap (G := G) (N := (N : Subgroup G)) q a = a) :
    openNormalTransferTopologicalAbelianization (G := G) N
      (TopologicalAbelianization.map
        { toMonoidHom := (N : Subgroup G).subtype
          continuous_toFun := continuous_subtype_val } a) =
      a ^ Nat.card (G ⧸ (N : Subgroup G)) := by
  classical
  let : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
  let ιN : ↥(N : Subgroup G) →ₜ* G :=
    { toMonoidHom := (N : Subgroup G).subtype
      continuous_toFun := continuous_subtype_val }
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.closedCommutator (N : Subgroup G)) a
  have hmap :
      TopologicalAbelianization.map ιN
          (TopologicalAbelianization.mk ↥(N : Subgroup G) x) =
        TopologicalAbelianization.mk G (ιN x) := by
    rfl
  have hlift :
      TopologicalAbelianization.lift
          (openNormalTransferTopologicalAbelianizationPre (G := G) N)
          (TopologicalAbelianization.mk G (ιN x)) =
        openNormalTransferTopologicalAbelianizationPre (G := G) N (ιN x) := by
    rfl
  change
      openNormalTransferTopologicalAbelianization (G := G) N
        (TopologicalAbelianization.map ιN
          (TopologicalAbelianization.mk ↥(N : Subgroup G) x)) =
        (TopologicalAbelianization.mk ↥(N : Subgroup G) x) ^ Nat.card (G ⧸ (N : Subgroup G))
  rw [openNormalTransferTopologicalAbelianization, hmap, hlift]
  let ρ : G ⧸ (N : Subgroup G) → G :=
    quotientOpenSubgroupSection (N : Subgroup G)
  have hρ :
      Function.RightInverse ρ (QuotientGroup.mk (s := (N : Subgroup G))) :=
    quotientOpenSubgroupSection_rightInverse (N : Subgroup G)
  have hterm :
      ∀ q : G ⧸ (N : Subgroup G),
        TopologicalAbelianization.mk ↥(N : Subgroup G)
          (openNormalTransferTerm (G := G) N q x) =
            TopologicalAbelianization.mk ↥(N : Subgroup G) x := by
    intro q
    have hxq : (QuotientGroup.mk' (N : Subgroup G) (x : G)) * q = q := by
      simp only [QuotientGroup.mk'_apply, mul_eq_right, QuotientGroup.eq_one_iff, SetLike.coe_mem]
    have htransfer :
        openNormalTransferTerm (G := G) N q x =
          (MulAut.conjNormal ((ρ q)⁻¹)) x := by
      apply Subtype.ext
      have hρxq' :
          quotientOpenSubgroupSection (N : Subgroup G)
            (((x : G) : G ⧸ (N : Subgroup G)) * q) =
            quotientOpenSubgroupSection (N : Subgroup G) q := by
        simpa using congrArg (quotientOpenSubgroupSection (N : Subgroup G)) hxq
      dsimp [openNormalTransferTerm]
      rw [hρxq']
      simp only [mul_assoc, inv_inv, ρ]
    have hqinv : QuotientGroup.mk' (N : Subgroup G) ((ρ q)⁻¹ : G) = q⁻¹ := by
      simpa [map_inv] using
        congrArg Inv.inv
          (show QuotientGroup.mk' (N : Subgroup G) (ρ q) = q from by
            simpa using hρ q)
    have hfix' := hfix q⁻¹
    have haction :
        quotientConjugationTopologicalAbelianizationMap (G := G) (N := (N : Subgroup G))
          (QuotientGroup.mk' (N : Subgroup G) ((ρ q)⁻¹ : G))
          (TopologicalAbelianization.mk ↥(N : Subgroup G) x) =
        TopologicalAbelianization.mk ↥(N : Subgroup G)
          (openNormalTransferTerm (G := G) N q x) := by
      calc
        quotientConjugationTopologicalAbelianizationMap (G := G) (N := (N : Subgroup G))
            (QuotientGroup.mk' (N : Subgroup G) ((ρ q)⁻¹ : G))
            (TopologicalAbelianization.mk ↥(N : Subgroup G) x) =
          TopologicalAbelianization.mk ↥(N : Subgroup G)
            ((MulAut.conjNormal ((ρ q)⁻¹)) x) := by
              simpa using
                (quotientConjugationTopologicalAbelianizationMap_mk_apply_mk
                  (N := (N : Subgroup G)) (g := ((ρ q)⁻¹ : G)) (n := x))
        _ =
          TopologicalAbelianization.mk ↥(N : Subgroup G)
            (openNormalTransferTerm (G := G) N q x) := by
              rw [htransfer]
    calc
      TopologicalAbelianization.mk ↥(N : Subgroup G)
          (openNormalTransferTerm (G := G) N q x) =
        quotientConjugationTopologicalAbelianizationMap (G := G) (N := (N : Subgroup G))
          (QuotientGroup.mk' (N : Subgroup G) ((ρ q)⁻¹ : G))
          (TopologicalAbelianization.mk ↥(N : Subgroup G) x) := by
            symm
            exact haction
      _ =
        quotientConjugationTopologicalAbelianizationMap (G := G) (N := (N : Subgroup G))
          (q⁻¹) (TopologicalAbelianization.mk ↥(N : Subgroup G) x) := by
            rw [hqinv]
      _ = TopologicalAbelianization.mk ↥(N : Subgroup G) x := hfix'
  calc
    (∏ q : G ⧸ (N : Subgroup G),
        TopologicalAbelianization.mk ↥(N : Subgroup G)
          (openNormalTransferTerm (G := G) N q x)) =
      ∏ _q : G ⧸ (N : Subgroup G), TopologicalAbelianization.mk ↥(N : Subgroup G) x := by
        apply Fintype.prod_congr
        intro q
        exact hterm q
    _ =
      (TopologicalAbelianization.mk ↥(N : Subgroup G) x) ^
        Fintype.card (G ⧸ (N : Subgroup G)) := by
          simp only [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass, Finset.prod_const,
              Finset.card_univ]
    _ =
      (TopologicalAbelianization.mk ↥(N : Subgroup G) x) ^
        Nat.card (G ⧸ (N : Subgroup G)) := by
          rw [Nat.card_eq_fintype_card]


/-- Transfer of an arbitrary continuous character with commutative values. -/
noncomputable def openNormalCharacterTransfer
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {A : Type v} [TopologicalSpace A] [CommGroup A] [T1Space A]
    (N : OpenNormalSubgroup G) [Finite (G ⧸ (N : Subgroup G))]
    (χ : (N : Subgroup G) →ₜ* A) : G →ₜ* A :=
  (TopologicalAbelianization.lift χ).comp
    (openNormalTransferTopologicalAbelianizationPre N)

/-- On the open normal subgroup, transfer is the product over conjugates. -/
theorem openNormalCharacterTransfer_apply_of_mem
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {A : Type v} [TopologicalSpace A] [CommGroup A] [T1Space A]
    (N : OpenNormalSubgroup G) [Finite (G ⧸ (N : Subgroup G))]
    (χ : (N : Subgroup G) →ₜ* A) (n : (N : Subgroup G)) :
    letI : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
    openNormalCharacterTransfer N χ n =
      ∏ q : G ⧸ (N : Subgroup G),
        χ (MulAut.conjNormal ((quotientOpenSubgroupSection (N : Subgroup G) q)⁻¹) n) := by
  classical
  let : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
  change TopologicalAbelianization.lift χ
    (∏ q : G ⧸ (N : Subgroup G),
      TopologicalAbelianization.mk (N : Subgroup G) (openNormalTransferTerm N q n)) = _
  rw [map_prod]
  apply Fintype.prod_congr
  intro q
  rw [TopologicalAbelianization.lift_apply_mk]
  congr 1
  apply Subtype.ext
  have hn : QuotientGroup.mk' (N : Subgroup G) (n : G) = 1 :=
    (QuotientGroup.eq_one_iff (N := (N : Subgroup G)) _).mpr n.property
  change (quotientOpenSubgroupSection (N : Subgroup G)
    (QuotientGroup.mk' (N : Subgroup G) (n : G) * q))⁻¹ * (n : G) *
      quotientOpenSubgroupSection (N : Subgroup G) q = _
  rw [hn, one_mul]
  simp only [MulAut.conjNormal_apply, inv_inv]

end ProCGroups.FiniteStepSolvableQuotients
