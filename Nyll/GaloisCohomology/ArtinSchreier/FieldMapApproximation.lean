/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ArtinSchreier.CharacterClasses
import Mathlib.Tactic.Choose
import Nyll.GaloisCohomology.Topology.SeparableGaloisMap

/-!
# Prescribing Artin–Schreier characters along field embeddings

Root differences commute with the actual absolute Galois restriction maps.
Simultaneous approximation of additive classes therefore prescribes characters.
-/

namespace ArtinSchreierTheory
open Field.absoluteGaloisGroup ValuationTheory.Completion
variable (p : ℕ) [Fact p.Prime] {K L : Type*} [Field K] [Field L]
  [CharP K p] [CharP L p]

/-- A field embedding carries root differences to the restricted character. -/
theorem rootCharacter_fieldMap (f : K →+* L) (a : K) (β : SeparableClosure K)
    (hβ : β ^ p - β = algebraMap K (SeparableClosure K) a)
    (hβL : (separableClosureLift f β) ^ p - separableClosureLift f β =
      algebraMap L (SeparableClosure L) (f a))
    (σ : Gal(AlgebraicClosure L/L)) :
    rootCharacter p (SeparableClosure K) a β hβ
        (separableClosureAutEquiv K (map f σ)) =
      rootCharacter p (SeparableClosure L) (f a) (separableClosureLift f β) hβL
        (separableClosureAutEquiv L σ) := by
  change (rootCharacter p (SeparableClosure K) a β hβ
        (separableClosureAutEquiv K (map f σ))).toAdd =
      (rootCharacter p (SeparableClosure L) (f a) (separableClosureLift f β) hβL
        (separableClosureAutEquiv L σ)).toAdd
  apply (ZMod.castHom (dvd_refl p) (SeparableClosure L)).injective
  rw [rootCharacter_cast]
  have h := congrArg (separableClosureLift f)
    (rootCharacter_cast p (SeparableClosure K) a β hβ
      (separableClosureAutEquiv K (map f σ)))
  rw [map_sub, map_separableClosureLift] at h
  simpa only [ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast] using h
end ArtinSchreierTheory

namespace ClassFieldTower.Martinet.Shafarevich
open ArtinSchreierTheory Field.absoluteGaloisGroup ValuationTheory.Completion
variable {ι K : Type*} [Field K] (L : ι → Type*) [∀ i, Field (L i)]

/-- Simultaneously lift continuous cyclic characters from additive class approximation. -/
theorem surjective_characters_of_artinSchreierClasses
    (p : ℕ) [Fact p.Prime] [CharP K p] [∀ i, CharP (L i) p]
    (f : ∀ i, K →+* L i)
    (hclasses : Function.Surjective (fun (a : K) (i : ι) =>
      (f i a : (L i) ⧸
        ((frobenius (L i) p).toAddMonoidHom - AddMonoidHom.id (L i)).range))) :
    Function.Surjective (fun χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod p) =>
      fun i => (χ.comp (map (f i)) :
        Gal(AlgebraicClosure (L i)/L i) →ₜ* Multiplicative (ZMod p))) := by
  classical
  intro χlocal
  let η (i : ι) : Gal(SeparableClosure (L i)/L i) →ₜ* Multiplicative (ZMod p) :=
    (χlocal i).comp (ContinuousMonoidHom.toContinuousMonoidHom
      (separableClosureAutContinuousEquiv (L i)).symm)
  choose a b hb hχ using fun i => exists_rootCharacter_eq p (η i)
  obtain ⟨a0, ha0⟩ := hclasses (fun i => (a i : (L i) ⧸
    ((frobenius (L i) p).toAddMonoidHom - AddMonoidHom.id (L i)).range))
  obtain ⟨β, hβ⟩ := exists_root p (SeparableClosure K) (algebraMap K (SeparableClosure K) a0)
  let χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod p) :=
    (rootCharacter p (SeparableClosure K) a0 β hβ).comp
      (ContinuousMonoidHom.toContinuousMonoidHom (separableClosureAutContinuousEquiv K))
  refine ⟨χ, funext (fun i => ?_)⟩
  apply ContinuousMonoidHom.ext
  intro σ
  have hβi : (separableClosureLift (f i) β) ^ p - separableClosureLift (f i) β =
      algebraMap (L i) (SeparableClosure (L i)) (f i a0) := by
    rw [← map_pow, ← map_sub, hβ, separableClosureLift_algebraMap]
  change rootCharacter p (SeparableClosure K) a0 β hβ
    (separableClosureAutEquiv K (map (f i) σ)) = χlocal i σ
  calc
    _ = rootCharacter p (SeparableClosure (L i)) (f i a0)
        (separableClosureLift (f i) β) hβi (separableClosureAutEquiv (L i) σ) :=
      rootCharacter_fieldMap p (f i) a0 β hβ hβi σ
    _ = rootCharacter p (SeparableClosure (L i)) (a i) (b i) (hb i)
        (separableClosureAutEquiv (L i) σ) :=
      DFunLike.congr_fun (rootCharacter_eq_of_class_eq p (f i a0) (a i)
        (separableClosureLift (f i) β) (b i) hβi (hb i) (congrFun ha0 i)) _
    _ = η i (separableClosureAutEquiv (L i) σ) := DFunLike.congr_fun (hχ i) _
    _ = χlocal i σ := congrArg (χlocal i)
      ((separableClosureAutContinuousEquiv (L i)).symm_apply_apply σ)
end ClassFieldTower.Martinet.Shafarevich
