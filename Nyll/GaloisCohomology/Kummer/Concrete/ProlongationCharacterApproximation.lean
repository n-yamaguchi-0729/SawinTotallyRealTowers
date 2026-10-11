/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.GaloisCohomology.Kummer.Concrete.PowerClassCharacterApproximation
import Nyll.ValuedFieldTheory.Valuation.Completion.PowerClasses
import Nyll.ValuedFieldTheory.Valuation.Completion.EquivariantMap
import Mathlib.Data.Fintype.EquivFin

/-!
# Simultaneous completion characters on prolongations

Prescribed local characters over inequivalent base valuations lift to a
global character over a finite family of prolongations. Equivalent
prolongations are grouped together before weak approximation of power
classes, and completion equivalences transport the resulting character.
-/

namespace KummerTheory

open ValuationTheory.DiscreteValuationField
open Field.absoluteGaloisGroup

universe u v w z

/-- Local characters prescribed on inequivalent base valuations can be lifted
simultaneously over any finite family of prolongations once roots of unity are present. -/
theorem exists_completion_character_on_prolongations
    {ι κ : Type*} [Finite κ] {K : Type u} {E : Type w}
    [Field K] [Field E] [Algebra K E]
    (D : ι → DVF.{u, v} K)
    (hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation))
    (V : κ → DVF.{w, z} E) (π : κ → ι)
    [hV : ∀ j, (D (π j)).valuation.HasExtension (V j).valuation]
    (n : ℕ+) [NeZero ((n : ℕ) : E)]
    (hmu : (primitiveRoots (n : ℕ) E).Nonempty)
    (χ : ∀ i, Gal(AlgebraicClosure (D i).valuation.Completion/(D i).valuation.Completion) →ₜ*
      Multiplicative (ZMod (n : ℕ))) :
    ∃ ψ : Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod (n : ℕ)),
      ∀ j, (ψ.comp (map (algebraMap E (V j).valuation.Completion)) :
        Gal(AlgebraicClosure (V j).valuation.Completion/(V j).valuation.Completion) →ₜ*
          Multiplicative (ZMod (n : ℕ))) =
        (χ (π j)).comp (map (DVF.completionMap (D (π j)) (V j))) := by
  classical
  let s : Setoid κ :=
    { r := fun i j => (V i).valuation.IsEquiv (V j).valuation
      iseqv := ⟨fun _ => _root_.Valuation.IsEquiv.refl,
        fun h => h.symm, fun h h' => h.trans h'⟩ }
  let J := Quotient s
  let : Fintype J := Fintype.ofFinite J
  let W (j : J) : DVF.{w,z} E := V j.out
  have hW : Pairwise (fun i j => ¬ (W i).valuation.IsEquiv (W j).valuation) := by
    intro i j hij heq
    exact hij ((Quotient.out_eq i).symm.trans
      ((Quotient.sound heq).trans (Quotient.out_eq j)))
  let C (j : J) := (W j).valuation.Completion
  let : ∀ j, Field (C j) := fun j => inferInstanceAs (Field ((W j).valuation.Completion))
  let f (j : J) : E →+* C j := algebraMap E (W j).valuation.Completion
  have hclasses : Function.Surjective (fun (u : Eˣ) (j : J) =>
      (Units.map (f j).toMonoidHom u : (C j)ˣ ⧸
        (powMonoidHom (n : ℕ) : (C j)ˣ →* (C j)ˣ).range)) :=
    DVF.surjective_pi_completion_powerClasses W hW (n : ℕ) (NeZero.ne _)
  let η (j : J) : Gal(AlgebraicClosure (C j)/C j) →ₜ* Multiplicative (ZMod (n : ℕ)) :=
    (χ (π j.out)).comp (map (DVF.completionMap (D (π j.out)) (V j.out)))
  obtain ⟨ψ, hψ⟩ := ClassFieldTower.Martinet.Shafarevich.surjective_characters_of_powerClasses
    C f n hmu hclasses η
  refine ⟨ψ, ?_⟩
  intro j
  let q : J := Quotient.mk s j
  let i : κ := q.out
  have hij : (V i).valuation.IsEquiv (V j).valuation := Quotient.exact (Quotient.out_eq q)
  have hπ : π i = π j := by
    by_contra hne
    apply hD hne
    exact (_root_.Valuation.HasExtension.val_isEquiv_comap
      (vR := (D (π i)).valuation) (vA := (V i).valuation)).trans
        ((_root_.Valuation.IsEquiv.comap (algebraMap K E) hij).trans
          (_root_.Valuation.HasExtension.val_isEquiv_comap
            (vR := (D (π j)).valuation) (vA := (V j).valuation)).symm)
  have hExt : (D (π i)).valuation.HasExtension (V j).valuation := hπ.symm ▸ hV j
  let g := DVF.completionRingEquiv (V i) (V j) (RingEquiv.refl E) hij
  have hg : g.toRingHom.comp (algebraMap E (V i).valuation.Completion) =
      algebraMap E (V j).valuation.Completion := by
    ext x
    exact DVF.completionRingEquiv_algebraMap (V i) (V j) (RingEquiv.refl E) hij x
  have hgbase : g.toRingHom.comp (DVF.completionMap (D (π i)) (V i)) =
      DVF.completionMap (D (π i)) (V j) :=
    DVF.completionRingEquiv_comp_completionMap (D (π i)) (V i) (V j) 1 hij
  have hrep : (ψ.comp (map (algebraMap E (V i).valuation.Completion)) :
      Gal(AlgebraicClosure (V i).valuation.Completion/(V i).valuation.Completion) →ₜ*
        Multiplicative (ZMod (n : ℕ))) =
      (χ (π i)).comp (map (DVF.completionMap (D (π i)) (V i))) := congrFun hψ q
  have hlast : ((χ (π i)).comp (map (DVF.completionMap (D (π i)) (V j))) :
      Gal(AlgebraicClosure (V j).valuation.Completion/(V j).valuation.Completion) →ₜ*
        Multiplicative (ZMod (n : ℕ))) =
      (χ (π j)).comp (map (DVF.completionMap (D (π j)) (V j))) := by
    have transport (a b : ι) (hab : a = b)
        (ha : (D a).valuation.HasExtension (V j).valuation)
        (hb : (D b).valuation.HasExtension (V j).valuation) :
        (let _ := ha; (χ a).comp (map (DVF.completionMap (D a) (V j)))) =
          (let _ := hb; (χ b).comp (map (DVF.completionMap (D b) (V j)))) := by
      subst b
      rfl
    exact transport (π i) (π j) hπ hExt (hV j)
  apply ContinuousMonoidHom.ext
  intro σ
  exact (DFunLike.congr_fun
    ((congrArg (fun f => ψ.comp (map f)) hg.symm).trans
      (character_map_comp (algebraMap E (V i).valuation.Completion) g.toRingHom ψ)) σ).trans
    ((DFunLike.congr_fun hrep (map g.toRingHom σ)).trans
      ((DFunLike.congr_fun
        ((character_map_comp (DVF.completionMap (D (π i)) (V i)) g.toRingHom (χ (π i))).symm.trans
          (congrArg (fun f => (χ (π i)).comp (map f)) hgbase)) σ).trans
        (DFunLike.congr_fun hlast σ)))

end KummerTheory
