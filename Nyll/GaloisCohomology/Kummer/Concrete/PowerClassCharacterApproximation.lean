/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.FieldMapNaturality

/-!
# Prescribing characters from power classes

When the base field contains the relevant roots of unity, simultaneous
prescription of multiplicative power classes gives simultaneous prescription
of continuous cyclic characters along arbitrary field embeddings. The proof
uses the naturality of the actual absolute Galois restriction maps.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory ValuationTheory.Completion

variable {ι K : Type*} [Field K] (L : ι → Type*) [∀ i, Field (L i)]

/-- Under the roots-of-unity hypothesis, simultaneous lifting of power classes
gives simultaneous extension of actual absolute Galois characters. -/
theorem surjective_characters_of_powerClasses
    (f : ∀ i, K →+* L i) (n : ℕ+) [NeZero ((n : ℕ) : K)]
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hclasses : Function.Surjective (fun (u : Kˣ) (i : ι) =>
      (Units.map (f i).toMonoidHom u :
        (L i)ˣ ⧸ (powMonoidHom (n : ℕ) : (L i)ˣ →* (L i)ˣ).range))) :
    Function.Surjective (fun χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod (n : ℕ)) =>
      fun i => (χ.comp (Field.absoluteGaloisGroup.map (f i)) :
        Gal(AlgebraicClosure (L i)/L i) →ₜ* Multiplicative (ZMod (n : ℕ)))) := by
  classical
  have (i : ι) : NeZero ((n : ℕ) : L i) :=
    NeZero.nat_of_injective (f := f i) (f i).injective
  have hmuL (i : ι) : (primitiveRoots (n : ℕ) (L i)).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmu
    exact ⟨f i ζ, (mem_primitiveRoots n.pos).mpr
      (((mem_primitiveRoots n.pos).mp hζ).map_of_injective (f i).injective)⟩
  intro χlocal
  let d := separableDiscreteNthRootsContinuousMulEquivMultiplicativeZMod K n hmu
  let e (i : ι) := separableNthRootsFieldMapEquiv (f i) n hmu
  let η (i : ι) : Gal(SeparableClosure (L i)/L i) →ₜ*
      DiscreteNthRootsSubgroup (SeparableClosure (L i)) (n : ℕ) :=
    (ContinuousMonoidHom.toContinuousMonoidHom (e i)).comp
      ((ContinuousMonoidHom.toContinuousMonoidHom d.symm).comp
        ((χlocal i).comp (ContinuousMonoidHom.toContinuousMonoidHom
          (separableClosureAutContinuousEquiv (L i)).symm)))
  let c (i : ι) := (separableKummerContinuousNthRootsCharacterEquiv (L i) n (hmuL i)).symm (η i)
  obtain ⟨u, hu⟩ := hclasses c
  let χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod (n : ℕ)) :=
    (ContinuousMonoidHom.toContinuousMonoidHom d).comp
      ((separableKummerContinuousNthRootsCharacterEquiv K n hmu
        (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)).comp
          (ContinuousMonoidHom.toContinuousMonoidHom (separableClosureAutContinuousEquiv K)))
  refine ⟨χ, funext (fun i => ?_)⟩
  apply ContinuousMonoidHom.ext
  intro σ
  change d (separableKummerContinuousNthRootsCharacterEquiv K n hmu
    (u : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
    (separableClosureAutEquiv K (Field.absoluteGaloisGroup.map (f i) σ))) = χlocal i σ
  have hlocal :
      separableKummerContinuousNthRootsCharacterEquiv (L i) n (hmuL i)
        ((Units.map (f i).toMonoidHom u) :
          (L i)ˣ ⧸ (powMonoidHom (n : ℕ) : (L i)ˣ →* (L i)ˣ).range)
        (separableClosureAutEquiv (L i) σ) =
      η i (separableClosureAutEquiv (L i) σ) := by
    exact (congrArg (fun a =>
      separableKummerContinuousNthRootsCharacterEquiv (L i) n (hmuL i) a
        (separableClosureAutEquiv (L i) σ)) (congrFun hu i)).trans
      (DFunLike.congr_fun
        ((separableKummerContinuousNthRootsCharacterEquiv (L i) n (hmuL i)).apply_symm_apply (η i))
        (separableClosureAutEquiv (L i) σ))
  have hinner : η i (separableClosureAutEquiv (L i) σ) =
      e i (d.symm (χlocal i σ)) := by
    exact congrArg (fun τ => e i (d.symm (χlocal i τ)))
      ((separableClosureAutContinuousEquiv (L i)).symm_apply_apply σ)
  have hroots := (separableKummerCharacter_fieldMap_equiv (f i) n hmu (hmuL i) u σ).trans
    (hlocal.trans hinner)
  exact (congrArg d ((e i).injective hroots)).trans (d.apply_symm_apply (χlocal i σ))

end ClassFieldTower.Martinet.Shafarevich
