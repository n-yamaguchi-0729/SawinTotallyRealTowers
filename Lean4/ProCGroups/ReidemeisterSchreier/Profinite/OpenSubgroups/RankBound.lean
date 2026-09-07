import ProCGroups.ReidemeisterSchreier.Discrete.OpenSubgroups.FreeBasis
import ProCGroups.GroupTheory.Subgroups
import ProCGroups.FiniteGeneration.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

/-!
# Cardinal and finite-rank Schreier bounds

This module defines the cardinal Schreier transform, proves its finite and
infinite simplifications, and bounds the topological rank of an open subgroup
of a compact Hausdorff totally disconnected group by the classical finite
rank transform.
-/

open Set
open scoped Topology Pointwise

namespace ReidemeisterSchreier
namespace Profinite

open ProCGroups
open ProCGroups.FiniteGeneration
open ReidemeisterSchreier.Discrete.OpenSubgroups

universe u

/--
Cardinal form of the Schreier rank transform for an open subgroup of finite index \(n\). For
finite rank this is the usual Schreier transform \(1+n(d-1)\). For infinite cardinals the
finite-index transform stabilizes at the original cardinal.
-/
noncomputable def schreierRankTransformCardinal (κ : Cardinal) (n : ℕ) : Cardinal :=
  if _ : κ < Cardinal.aleph0 then
    (_root_.ReidemeisterSchreier.Schreier.rankTransform κ.toNat n : Cardinal)
  else κ

/-- On a finite cardinal, the cardinal Schreier transform agrees with the usual natural-number formula. -/
@[simp] theorem schreierRankTransformCardinal_natCast (d n : ℕ) :
    schreierRankTransformCardinal (d : Cardinal) n =
      (_root_.ReidemeisterSchreier.Schreier.rankTransform d n : Cardinal) := by
  simp only [schreierRankTransformCardinal, Cardinal.natCast_lt_aleph0, ↓reduceDIte,
      Cardinal.toNat_natCast]

/-- A finite-index Schreier transform fixes every infinite cardinal. -/
theorem schreierRankTransformCardinal_eq_self_of_aleph0_le
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (n : ℕ) :
    schreierRankTransformCardinal κ n = κ := by
  simp only [schreierRankTransformCardinal, not_lt.mpr hκ, ↓reduceDIte]

/--
For a finite input cardinal, the Schreier rank-transform cardinal is the corresponding finite
Schreier value.
-/
@[simp 900] theorem schreierRankTransformCardinal_mk_finite (X : Type u) [Finite X] (n : ℕ) :
    schreierRankTransformCardinal (Cardinal.mk X) n =
      (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) n : Cardinal) := by
  rw [← Nat.cast_card (α := X)]
  exact schreierRankTransformCardinal_natCast (Nat.card X) n

/--
For an infinite input cardinal, the finite-index Schreier rank transform is the same infinite
cardinal.
-/
@[simp 900] theorem schreierRankTransformCardinal_mk_infinite (X : Type u) [Infinite X] (n : ℕ) :
    schreierRankTransformCardinal (Cardinal.mk X) n = Cardinal.mk X :=
  schreierRankTransformCardinal_eq_self_of_aleph0_le (Cardinal.aleph0_le_mk X) n


/--
An open subgroup of a finitely generated profinite group satisfies the usual Schreier bound on
the minimal number of topological generators.
-/
theorem topologicalRank_openSubgroup_le_rankTransform_of_topologicalRank_eq_nat
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {d : ℕ} (hd : Generation.topologicalRank G = d)
    (U : OpenSubgroup G) :
    Generation.topologicalRank ↥(U : Subgroup G) ≤
      (_root_.ReidemeisterSchreier.Schreier.rankTransform d (Nat.card (G ⧸ (U : Subgroup G))) :
          Cardinal) := by
  classical
  cases d with
  | zero =>
      rcases
          topologicallyGeneratedByAtMost_of_topologicalRank_eq_nat
            (G := G) hd with ⟨s, hs, hsgen⟩
      have hs0 : s.card = 0 := Nat.eq_zero_of_le_zero hs
      have hsempty : s = ∅ := Finset.card_eq_zero.mp hs0
      have hgenEmpty : Generation.TopologicallyGenerates (G := G) (∅ : Set G) := by
        simpa [hsempty] using hsgen
      have hdenseOne : Dense ({1} : Set G) := by
        have hdenseBot :
            Dense (((Subgroup.closure (∅ : Set G)) : Subgroup G) : Set G) :=
          (Generation.topologicallyGenerates_iff_dense (G := G) (X := (∅ : Set G))).1
            hgenEmpty
        simpa using hdenseBot
      have hsingleton :
          ({1} : Set G) = (Set.univ : Set G) := by
        exact (closure_eq_iff_isClosed.mpr isClosed_singleton).symm.trans hdenseOne.closure_eq
      have : Subsingleton G := ⟨fun x y => by
        have hx : x = 1 := by
          have hxmem : x ∈ ({1} : Set G) := by
            simp only [hsingleton, mem_univ]
          simpa using hxmem
        have hy : y = 1 := by
          have hymem : y ∈ ({1} : Set G) := by
            simp only [hsingleton, mem_univ]
          simpa using hymem
        rw [hx, hy]⟩
      have hbot_top : (⊥ : Subgroup ↥(U : Subgroup G)) = ⊤ := by
        ext x
        constructor
        · intro _
          trivial
        · intro _
          exact Subsingleton.elim _ _
      have hgenEmptyU :
          Generation.TopologicallyGenerates (G := ↥(U : Subgroup G))
            (∅ : Set ↥(U : Subgroup G)) := by
        rw [Generation.TopologicallyGenerates]
        have htopClosure : (⊤ : Subgroup ↥(U : Subgroup G)).topologicalClosure = ⊤ :=
          top_unique (Subgroup.le_topologicalClosure _)
        simpa [hbot_top] using htopClosure
      have hbound : Generation.topologicalRank ↥(U : Subgroup G) ≤ (0 : Cardinal) := by
        simpa only [Cardinal.mk_eq_zero] using
          (Generation.topologicalRank_le_mk_of_topologicallyGenerates
            (G := ↥(U : Subgroup G)) hgenEmptyU)
      simpa using hbound
  | succ n =>
      have hgenAtMost :
          TopologicallyGeneratedByAtMost (G := G) (n + 1) :=
        topologicallyGeneratedByAtMost_of_topologicalRank_eq_nat
          (G := G) hd
      have hfg_iff :
          TopologicallyFinitelyGenerated G ↔
            ∃ m, TopologicallyGeneratedByAtMost (G := G) m :=
          by
            simpa using
              (topologicallyFinitelyGenerated_iff_exists_topologicallyGeneratedByAtMost
                (G := G))
      have hfg : TopologicallyFinitelyGenerated G := by
        exact hfg_iff.2 ⟨n + 1, hgenAtMost⟩
      have hdle : Generation.topologicalRank G ≤ ((n + 1 : ℕ) : Cardinal) := by
        rw [hd]
      obtain ⟨g, hg⟩ :=
        exists_generatingTuple_of_topologicalRank_le_of_finite
          (G := G) (n := n + 1) hfg hdle
      let φ : FreeGroup (Fin (n + 1)) →* G := FreeGroup.lift g
      let D : Subgroup G := φ.range
      have hg_subset : Set.range g ⊆ (D : Set G) := by
        rintro _ ⟨i, rfl⟩
        exact ⟨FreeGroup.of i, by simp only [FreeGroup.lift_apply_of, φ]⟩
      have hDgen : Generation.TopologicallyGenerates (G := G) (D : Set G) :=
        ProCGroups.Generation.topologicallyGenerates_mono (G := G) hg hg_subset
      have hDdenseClosure :
          Dense (((Subgroup.closure (D : Set G)) : Subgroup G) : Set G) :=
        (Generation.topologicallyGenerates_iff_dense (G := G) (X := (D : Set G))).1 hDgen
      have hD_dense : Dense ((D : Set G)) := by
        simpa [Subgroup.closure_eq D] using hDdenseClosure
      let I : Subgroup G := (U : Subgroup G) ⊓ D
      have hIU_dense : Dense ((I.subgroupOf (U : Subgroup G)) : Set ↥(U : Subgroup G)) := by
        rw [Subtype.dense_iff]
        have himage :
            ((↑) : ↥(U : Subgroup G) → G) '' ((I.subgroupOf (U : Subgroup G)) :
              Set ↥(U : Subgroup G)) =
              ((U : Set G) ∩ (D : Set G)) := by
          have hmap :
              (((I.subgroupOf (U : Subgroup G)).map (U : Subgroup G).subtype : Subgroup G) :
                Set G) =
                ((U : Set G) ∩ (D : Set G)) := by
            rw [Subgroup.map_subgroupOf_eq_of_le]
            · rfl
            · exact inf_le_left
          exact
            (Subgroup.coe_map (U : Subgroup G).subtype (I.subgroupOf (U : Subgroup G))).symm.trans
              hmap
        change (U : Set G) ⊆
          closure (((↑) : ↥(U : Subgroup G) → G) '' ((I.subgroupOf (U : Subgroup G)) :
            Set ↥(U : Subgroup G)))
        rw [himage]
        change ((U : Subgroup G) : Set G) ⊆
          closure (((U : Subgroup G) : Set G) ∩ (D : Set G))
        exact hD_dense.open_subset_closure_inter U.isOpen'
      let L : Subgroup (FreeGroup (Fin (n + 1))) := Subgroup.comap φ (U : Subgroup G)
      have hDindex :
          (U : Subgroup G).relIndex D = (U : Subgroup G).index := by
        change ((U : Subgroup G).subgroupOf D).index = (U : Subgroup G).index
        have key :
            ∀ x y : D,
              QuotientGroup.leftRel ((U : Subgroup G).subgroupOf D) x y ↔
                QuotientGroup.leftRel (U : Subgroup G) x y := by
          intro x y
          simp only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
              InvMemClass.coe_inv,
  OpenSubgroup.mem_toSubgroup]
        refine Nat.card_congr <|
          Equiv.ofBijective
            (Quotient.map' ((↑) : D → G) fun x y => (key x y).mp) ⟨?_, ?_⟩
        · intro a b hab
          revert hab
          refine Quotient.inductionOn₂' a b ?_
          intro x y hab
          have hxy : QuotientGroup.leftRel (U : Subgroup G) x y := by
            rw [Quotient.map'_mk'', Quotient.map'_mk''] at hab
            exact Quotient.exact' hab
          exact Quotient.sound' ((key x y).mpr hxy)
        · refine Quotient.ind' fun x => ?_
          let V : Set G := x • ((U : Subgroup G) : Set G)
          have hVopen : IsOpen V := by
            change IsOpen (x • ((U : Subgroup G) : Set G))
            exact U.isOpen'.smul x
          have hVnonempty : V.Nonempty := by
            refine ⟨x, ?_⟩
            simpa [V] using mem_leftCoset x (show (1 : G) ∈ (U : Subgroup G) from U.one_mem)
          rcases hD_dense.exists_mem_open hVopen hVnonempty with ⟨y, hyD, hyV⟩
          refine ⟨(⟨y, hyD⟩ : D), ?_⟩
          change QuotientGroup.mk y = QuotientGroup.mk x
          apply QuotientGroup.eq.2
          simpa [mul_inv_rev, inv_inv] using
            (U : Subgroup G).inv_mem ((mem_leftCoset_iff x).1 (by simpa [V] using hyV))
      have hLindex : L.index = (U : Subgroup G).index := by
        calc
          L.index = (U : Subgroup G).relIndex D := by
            simpa [L, D] using (Subgroup.index_comap (H := (U : Subgroup G)) (f := φ))
          _ = (U : Subgroup G).index := hDindex
      have hLindex_ne_zero : L.index ≠ 0 := by
        rw [hLindex]
        exact Subgroup.index_ne_zero_of_finite (H := (U : Subgroup G))
      have : Finite (FreeGroup (Fin (n + 1)) ⧸ L) :=
        (Subgroup.index_ne_zero_iff_finite (H := L)).1 hLindex_ne_zero
      obtain ⟨Y, ⟨eL⟩, hYcard⟩ :=
        exists_freeBasis_subgroupOfFreeGroup_of_rankTransform
          (X := Fin (n + 1)) (L := L)
      have hquotCard :
          Nat.card (FreeGroup (Fin (n + 1)) ⧸ L) = Nat.card (G ⧸ (U : Subgroup G)) := by
        rw [← Subgroup.index_eq_card (H := L), hLindex, Subgroup.index_eq_card]
      have hYcard' :
          Nat.card Y = _root_.ReidemeisterSchreier.Schreier.rankTransform (n + 1) (Nat.card (G ⧸
              (U : Subgroup G))) := by
        simpa [hquotCard] using hYcard
      have hYnonzero : Nat.card Y ≠ 0 := by
        rw [hYcard', _root_.ReidemeisterSchreier.Schreier.rankTransform_succ]
        simp only [Nat.add_comm, ne_eq, Nat.add_eq_zero_iff, mul_eq_zero, one_ne_zero,
            and_false, not_false_eq_true]
      have : Finite Y := Nat.finite_of_card_ne_zero hYnonzero
      let : Fintype Y := Fintype.ofFinite Y
      let φU : L →* ↥(U : Subgroup G) := {
        toFun := fun x => ⟨φ x.1, x.2⟩
        map_one' := by simp only [OneMemClass.coe_one, map_one, Subgroup.mk_eq_one, φ]
        map_mul' := by
          intro a b
          ext
          simp only [Subgroup.coe_mul, map_mul, φ]}
      let κ : Y → ↥(U : Subgroup G) := fun y => φU (eL y)
      have hLtop :
          Subgroup.closure (Set.range fun y : Y => eL y) = ⊤ := by
        have hset :
            Set.range (fun y : Y => eL y) =
              eL.repr.symm.toMonoidHom '' Set.range (FreeGroup.of : Y → FreeGroup Y) := by
          ext z
          constructor
          · rintro ⟨y, rfl⟩
            exact ⟨FreeGroup.of y, ⟨y, rfl⟩, by rfl⟩
          · rintro ⟨x, hx, rfl⟩
            rcases hx with ⟨y, rfl⟩
            exact ⟨y, rfl⟩
        calc
          Subgroup.closure (Set.range fun y : Y => eL y)
              =
                Subgroup.closure
                  (eL.repr.symm.toMonoidHom '' Set.range (FreeGroup.of : Y → FreeGroup Y)) := by
                    rw [hset]
          _ = ⊤ := by
                rw [← MonoidHom.map_closure, FreeGroup.closure_range_of]
                exact Subgroup.map_top_of_surjective
                  eL.repr.symm.toMonoidHom eL.repr.symm.surjective
      have hφU_range : φU.range = I.subgroupOf (U : Subgroup G) := by
        ext u
        constructor
        · rintro ⟨x, rfl⟩
          change φ x.1 ∈ I
          exact ⟨x.2, ⟨x.1, rfl⟩⟩
        · intro hu
          change (u : G) ∈ I at hu
          rcases hu with ⟨huU, huD⟩
          rcases huD with ⟨x, hx⟩
          refine ⟨⟨x, ?_⟩, ?_⟩
          · change φ x ∈ (U : Subgroup G)
            exact hx.symm ▸ huU
          · apply Subtype.ext
            simp only [MonoidHom.coe_mk, OneHom.coe_mk, hx, Subtype.coe_eta, φU]
      have hφU_dense :
          Dense ((φU.range : Subgroup ↥(U : Subgroup G)) : Set ↥(U : Subgroup G)) := by
        rw [hφU_range]
        exact hIU_dense
      have hκclosure :
          Subgroup.closure (Set.range κ) = φU.range := by
        have hmap :
            (Subgroup.closure (Set.range fun y : Y => eL y)).map φU =
              Subgroup.closure (φU '' Set.range (fun y : Y => eL y)) := by
          simpa using
            (MonoidHom.map_closure φU (Set.range fun y : Y => eL y))
        have himage :
            φU '' Set.range (fun y : Y => eL y) = Set.range κ := by
          ext u
          constructor
          · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
            exact ⟨y, rfl⟩
          · rintro ⟨y, rfl⟩
            exact ⟨eL y, ⟨y, rfl⟩, rfl⟩
        calc
          Subgroup.closure (Set.range κ)
              = Subgroup.closure (φU '' Set.range (fun y : Y => eL y)) := by
                  rw [← himage]
          _ = (Subgroup.closure (Set.range fun y : Y => eL y)).map φU := by
                symm
                exact hmap
          _ = (⊤ : Subgroup L).map φU := by rw [hLtop]
          _ = φU.range := by rw [← MonoidHom.range_eq_map]
      have hκgen :
          Generation.TopologicallyGenerates (G := ↥(U : Subgroup G)) (Set.range κ) := by
        exact (Generation.topologicallyGenerates_iff_dense
          (G := ↥(U : Subgroup G)) (X := Set.range κ)).2 <|
          by simpa [hκclosure] using hφU_dense
      let s : Finset ↥(U : Subgroup G) := Finset.univ.image κ
      have hs_card : s.card ≤ Nat.card Y := by
        simpa [s, Nat.card_eq_fintype_card] using
          (Finset.card_image_le (s := (Finset.univ : Finset Y)) (f := κ))
      have hs_gen :
          Generation.TopologicallyGenerates (G := ↥(U : Subgroup G))
            (↑s : Set ↥(U : Subgroup G)) := by
        simpa [s, Finset.coe_image] using hκgen
      have hdU_nat : Generation.topologicalRank ↥(U : Subgroup G) ≤ Nat.card Y := by
        exact topologicalRank_le_of_topologicallyGeneratedByAtMost
          (G := ↥(U : Subgroup G)) ⟨s, hs_card, hs_gen⟩
      calc
        Generation.topologicalRank ↥(U : Subgroup G) ≤ (Nat.card Y : Cardinal) := by
          exact hdU_nat
        _ = (_root_.ReidemeisterSchreier.Schreier.rankTransform (n + 1) (Nat.card (G ⧸ (U :
            Subgroup G))) : Cardinal) := by
            exact_mod_cast hYcard'

end Profinite
end ReidemeisterSchreier
