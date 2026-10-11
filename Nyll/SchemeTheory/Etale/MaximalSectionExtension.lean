/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.UnramifiedHomExt
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!+# The largest open extension of an etale section

A section over a dense open into a separated etale target has a largest
open domain of extension. We glue all local sections that agree with the
given section on their overlaps. Their pairwise agreement follows from
the dense open and the separated-unramified equalizer. The base need not
be reduced, and no local existence assertion is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Etale

private theorem section_eq_of_dense_open
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [IsSeparated f]
    (U W : X.Opens) (hU : Dense (U : Set X))
    (a b : W.toScheme ⟶ Y) (ha : a ≫ f = W.ι) (hb : b ≫ f = W.ι)
    (hab : X.homOfLE (show U ⊓ W ≤ W from inf_le_right) ≫ a =
      X.homOfLE (show U ⊓ W ≤ W from inf_le_right) ≫ b) : a = b := by
  let j : (U ⊓ W).toScheme ⟶ W.toScheme := X.homOfLE inf_le_right
  have hrange : Set.range j = W.ι ⁻¹' (U : Set X) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz⟩, rfl⟩
      change X.homOfLE (show U ⊓ W ≤ W from inf_le_right) ⟨z, hz⟩ ∈ _
      rw [Scheme.homOfLE_apply']
      exact hz.1
    · intro hy
      exact ⟨⟨y.1, hy, y.2⟩, X.homOfLE_apply' inf_le_right y.1 ⟨hy, y.2⟩⟩
  have hj : IsDominant j := by
    constructor
    change Dense (Set.range j)
    rw [hrange]
    exact hU.preimage W.ι.isOpenEmbedding.isOpenMap
  let a₀ : Over.mk W.ι ⟶ Over.mk f := Over.homMk a ha
  let b₀ : Over.mk W.ι ⟶ Over.mk f := Over.homMk b hb
  let i : Over.mk (U ⊓ W).ι ⟶ Over.mk W.ι :=
    Over.homMk j (X.homOfLE_ι inf_le_right)
  have : FormallyUnramified (Over.mk f).hom := inferInstanceAs (FormallyUnramified f)
  have : LocallyOfFiniteType (Over.mk f).hom := inferInstanceAs (LocallyOfFiniteType f)
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  have : IsDominant i.left := hj
  have h : a₀ = b₀ := Over.hom_ext_of_isDominant_of_unramified a₀ b₀ i
    (Over.OverMorphism.ext hab)
  exact congrArg (fun z : Over.mk W.ι ⟶ Over.mk f => z.left) h

/-- The constructed maximum contains every open carrying a section which
agrees with the initial section on the overlap, even if that open does not
contain the initial domain. -/
theorem exists_maximal_open_section_extension
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [IsSeparated f]
    (U : X.Opens) (hU : Dense (U : Set X))
    (s : U.toScheme ⟶ Y) (hs : s ≫ f = U.ι) :
    ∃ (V : X.Opens) (hUV : U ≤ V) (b : V.toScheme ⟶ Y),
      b ≫ f = V.ι ∧ X.homOfLE hUV ≫ b = s ∧
      ∀ (W : X.Opens) (c : W.toScheme ⟶ Y), c ≫ f = W.ι →
        X.homOfLE (show U ⊓ W ≤ U from inf_le_left) ≫ s =
          X.homOfLE (show U ⊓ W ≤ W from inf_le_right) ≫ c → W ≤ V := by
  let I : Type u := Σ W : X.Opens, { c : W.toScheme ⟶ Y // c ≫ f = W.ι ∧
    X.homOfLE (show U ⊓ W ≤ U from inf_le_left) ≫ s =
      X.homOfLE (show U ⊓ W ≤ W from inf_le_right) ≫ c }
  let v : I → X.Opens := fun i => i.1
  let a : (i : I) → (v i).toScheme ⟶ Y := fun i => i.2.1
  have haf : ∀ i : I, a i ≫ f = (v i).ι := fun i => i.2.2.1
  have hau : ∀ i : I,
      X.homOfLE (show U ⊓ v i ≤ U from inf_le_left) ≫ s =
        X.homOfLE (show U ⊓ v i ≤ v i from inf_le_right) ≫ a i := fun i => i.2.2.2
  let i₀ : I := ⟨U, s, hs, rfl⟩
  let V : X.Opens := ⨆ i : I, v i
  have hUV : U ≤ V := le_iSup v i₀
  let 𝒰 : V.toScheme.OpenCover := Scheme.Opens.iSupOpenCover v
  have hcompat : ∀ i j : I,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ a i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ a j := by
    intro i j
    have hij : X.homOfLE (show v i ⊓ v j ≤ v i from inf_le_left) ≫ a i =
        X.homOfLE (show v i ⊓ v j ≤ v j from inf_le_right) ≫ a j := by
      apply section_eq_of_dense_open f U (v i ⊓ v j) hU
      · rw [Category.assoc, haf, Scheme.homOfLE_ι]
      · rw [Category.assoc, haf, Scheme.homOfLE_ι]
      · have hi :
            X.homOfLE (show U ⊓ (v i ⊓ v j) ≤ v i from inf_le_right.trans inf_le_left) ≫ a i =
              X.homOfLE (show U ⊓ (v i ⊓ v j) ≤ U from inf_le_left) ≫ s := by
          have hDi : U ⊓ (v i ⊓ v j) ≤ U ⊓ v i :=
            le_inf inf_le_left (inf_le_right.trans inf_le_left)
          have h := congrArg
            (fun z : (U ⊓ v i).toScheme ⟶ Y => X.homOfLE hDi ≫ z) (hau i).symm
          simpa only [← Category.assoc, Scheme.homOfLE_homOfLE] using h
        have hj :
            X.homOfLE (show U ⊓ (v i ⊓ v j) ≤ v j from inf_le_right.trans inf_le_right) ≫ a j =
              X.homOfLE (show U ⊓ (v i ⊓ v j) ≤ U from inf_le_left) ≫ s := by
          have hDj : U ⊓ (v i ⊓ v j) ≤ U ⊓ v j :=
            le_inf inf_le_left (inf_le_right.trans inf_le_right)
          have h := congrArg
            (fun z : (U ⊓ v j).toScheme ⟶ Y => X.homOfLE hDj ≫ z) (hau j).symm
          simpa only [← Category.assoc, Scheme.homOfLE_homOfLE] using h
        rw [← Category.assoc, Scheme.homOfLE_homOfLE, hi,
          ← Category.assoc, Scheme.homOfLE_homOfLE, hj]
    let e := (isPullback_opens_inf_le (le_iSup v i) (le_iSup v j)).isoPullback
    have he₁ : e.hom ≫ pullback.fst (𝒰.f i) (𝒰.f j) =
        X.homOfLE (show v i ⊓ v j ≤ v i from inf_le_left) :=
      (isPullback_opens_inf_le (le_iSup v i) (le_iSup v j)).isoPullback_hom_fst
    have he₂ : e.hom ≫ pullback.snd (𝒰.f i) (𝒰.f j) =
        X.homOfLE (show v i ⊓ v j ≤ v j from inf_le_right) :=
      (isPullback_opens_inf_le (le_iSup v i) (le_iSup v j)).isoPullback_hom_snd
    apply (cancel_epi e.hom).mp
    calc
      e.hom ≫ (pullback.fst (𝒰.f i) (𝒰.f j) ≫ a i) =
          (e.hom ≫ pullback.fst (𝒰.f i) (𝒰.f j)) ≫ a i :=
        (Category.assoc _ _ _).symm
      _ = X.homOfLE inf_le_left ≫ a i := congrArg (fun z => z ≫ a i) he₁
      _ = X.homOfLE inf_le_right ≫ a j := hij
      _ = (e.hom ≫ pullback.snd (𝒰.f i) (𝒰.f j)) ≫ a j :=
        congrArg (fun z => z ≫ a j) he₂.symm
      _ = e.hom ≫ (pullback.snd (𝒰.f i) (𝒰.f j) ≫ a j) := Category.assoc _ _ _
  let b : V.toScheme ⟶ Y := 𝒰.glueMorphisms a hcompat
  have hbf : b ≫ f = V.ι := by
    apply 𝒰.hom_ext
    change ∀ i : I, X.homOfLE (le_iSup v i) ≫ (b ≫ f) =
      X.homOfLE (le_iSup v i) ≫ V.ι
    intro i
    have hbi : X.homOfLE (le_iSup v i) ≫ b = a i := 𝒰.ι_glueMorphisms a hcompat i
    rw [← Category.assoc, hbi, haf i, Scheme.homOfLE_ι]
  have hbu : X.homOfLE hUV ≫ b = s :=
    𝒰.ι_glueMorphisms a hcompat i₀
  refine ⟨V, hUV, b, hbf, hbu, ?_⟩
  intro W c hcf hcu
  exact le_iSup v (⟨W, c, hcf, hcu⟩ : I)

end AlgebraicGeometry.Etale
