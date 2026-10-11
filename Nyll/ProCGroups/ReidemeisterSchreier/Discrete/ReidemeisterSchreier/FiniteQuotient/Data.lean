/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.Rewriting

/-!
# Reidemeister Schreier / Discrete / Reidemeister Schreier / Finite Quotient / Data

This module packages a finite quotient map with chosen section words.  It
defines the kernel, representatives, finite Schreier symbols, their
evaluation, and the basic identities used by tau rewriting.
-/


namespace ReidemeisterSchreier.Discrete

open ReidemeisterSchreier.Discrete.Presentations

variable {X Q : Type*} [Group Q] [Fintype Q]

/-- A finite quotient together with a normalized section. -/
structure FiniteQuotientSchreierData (X Q : Type*) [Group Q] [Fintype Q] where
  /-- The homomorphism from the free group to the finite quotient. -/
  quotientMap : FreeGroup X →* Q
  /-- A chosen free-group representative of each finite quotient element. -/
  quotientSection : Q → FreeGroup X
  /-- Each chosen representative maps back to the quotient element it represents. -/
  quotientMap_quotientSection : ∀ q, quotientMap (quotientSection q) = q
  /-- The identity quotient element is represented by the identity word. -/
  quotientSection_one : quotientSection 1 = 1

namespace FiniteQuotientSchreierData

/--
Finite quotient Schreier data can be built from quotient-section words whose evaluations are the
prescribed quotient sections.
-/
def ofQuotientSectionWords
    (quotientMap : FreeGroup X →* Q)
    (quotientSectionWord : Q → List (X × Bool))
    (quotientMap_mk_quotientSectionWord :
      ∀ q : Q, quotientMap (FreeGroup.mk (quotientSectionWord q)) = q)
    (quotientSectionWord_one : quotientSectionWord 1 = []) :
    FiniteQuotientSchreierData X Q where
  quotientMap := quotientMap
  quotientSection q := FreeGroup.mk (quotientSectionWord q)
  quotientMap_quotientSection := quotientMap_mk_quotientSectionWord
  quotientSection_one := by
    simp only [quotientSectionWord_one, ← FreeGroup.one_eq_mk]

/--
The finite quotient Schreier data built from quotient-section words has the prescribed
quotient-section map.
-/
@[simp]
theorem ofQuotientSectionWords_quotientSection
    (quotientMap : FreeGroup X →* Q)
    (quotientSectionWord : Q → List (X × Bool))
    (quotientMap_mk_quotientSectionWord :
      ∀ q : Q, quotientMap (FreeGroup.mk (quotientSectionWord q)) = q)
    (quotientSectionWord_one : quotientSectionWord 1 = [])
    (q : Q) :
    (ofQuotientSectionWords quotientMap quotientSectionWord
      quotientMap_mk_quotientSectionWord quotientSectionWord_one).quotientSection q =
      FreeGroup.mk (quotientSectionWord q) :=
  rfl

variable (D : FiniteQuotientSchreierData X Q)

/-- Applying the quotient map to a chosen quotient section returns the original quotient element. -/
@[simp]
theorem quotientMap_quotientSection_apply (q : Q) :
    D.quotientMap (D.quotientSection q) = q :=
  D.quotientMap_quotientSection q

/-- The kernel of the finite quotient map is the subgroup used in the finite Schreier data. -/
def kernel : Subgroup (FreeGroup X) :=
  D.quotientMap.ker

/--
The representative map chooses the quotient section of the quotient class of a free-group word.
-/
def representative (w : FreeGroup X) : FreeGroup X :=
  D.quotientSection (D.quotientMap w)

/-- The representative of a chosen quotient section is that quotient section. -/
@[simp]
theorem representative_quotientSection (q : Q) :
    D.representative (D.quotientSection q) = D.quotientSection q := by
  simp only [representative, quotientMap_quotientSection_apply]

/-- The representative of a word is the quotient section of its quotient-map image. -/
theorem representative_eq_quotientSection_quotientMap (w : FreeGroup X) :
    D.representative w = D.quotientSection (D.quotientMap w) :=
  rfl

/-- The representative of the identity is the identity quotient section. -/
theorem representative_one : D.representative 1 = 1 := by
  simp only [representative, map_one, D.quotientSection_one]

/-- A finite quotient section defines a right Schreier representative for the kernel subgroup. -/
def rightSchreierRepresentative :
    RightSchreierRepresentative D.kernel where
  representative := D.representative
  sameRightCoset := by
    intro g
    change D.quotientMap (g * (D.representative g)⁻¹) = 1
    simp only [representative, map_mul, map_inv, quotientMap_quotientSection_apply, mul_inv_cancel]
  representative_eq_of_sameRightCoset := by
    intro g h hgh
    have hgh' : D.quotientMap (g * h⁻¹) = 1 := by
      simpa [kernel] using hgh
    have hquot : D.quotientMap g = D.quotientMap h := by
      have hmap : D.quotientMap g * (D.quotientMap h)⁻¹ = 1 := by
        simpa using hgh'
      calc
        D.quotientMap g =
            D.quotientMap g * (D.quotientMap h)⁻¹ * D.quotientMap h := by
              group
        _ = D.quotientMap h := by
              rw [hmap]
              simp only [one_mul]
    simp only [representative, hquot]
  representative_one := D.representative_one

/-- Finite-indexed Schreier generator labels. -/
abbrev FiniteSchreierSymbol (X Q : Type*) := Q × X

/--
The finite-quotient Schreier transition sends \(q\) and generator \(x\) to \(q\) multiplied by
the quotient image of \(x\).
-/
def transition (q : Q) (x : X) : Q :=
  D.quotientMap (D.quotientSection q * FreeGroup.of x)

/--
The inverse finite-quotient Schreier transition sends \(q\) and generator \(x\) to \(q\)
multiplied by the inverse of the quotient image of \(x\).
-/
def inverseTransition (q : Q) (x : X) : Q :=
  D.quotientMap (D.quotientSection q * (FreeGroup.of x)⁻¹)

/-- The transition map is the one specified by the finite-quotient Schreier data. -/
@[simp]
theorem transition_eq (q : Q) (x : X) :
    D.transition q x = q * D.quotientMap (FreeGroup.of x) := by
  simp only [transition, map_mul, quotientMap_quotientSection_apply]

/--
The inverse transition multiplies the current quotient state by the inverse of the generator's
quotient image.
-/
@[simp]
theorem inverseTransition_eq (q : Q) (x : X) :
    D.inverseTransition q x = q * (D.quotientMap (FreeGroup.of x))⁻¹ := by
  simp only [inverseTransition, map_mul, quotientMap_quotientSection_apply, map_inv]

/--
The Schreier generator is the correction term \(t x \overline{t x}^{-1}\) attached to a
representative and a generator.
-/
def schreierGenerator (q : Q) (x : X) : FreeGroup X :=
  D.quotientSection q * FreeGroup.of x * (D.quotientSection (D.transition q x))⁻¹

/-- Evaluation of one finite Schreier symbol as its Schreier generator in the free group. -/
def symbolEval (z : FiniteSchreierSymbol X Q) : FreeGroup X :=
  D.schreierGenerator z.1 z.2

/--
The homomorphism extending finite Schreier-symbol evaluation to the free group on Schreier
symbols.
-/
def symbolEvalHom : FreeGroup (FiniteSchreierSymbol X Q) →* FreeGroup X :=
  FreeGroup.lift (D.symbolEval)

/-- The evaluation homomorphism sends a Schreier-symbol generator to its symbol evaluation. -/
@[simp]
theorem symbolEvalHom_of (z : FiniteSchreierSymbol X Q) :
    D.symbolEvalHom (FreeGroup.of z) = D.symbolEval z := by
  simp only [symbolEvalHom, FreeGroup.lift_apply_of]

/-- The quotient map kills every finite Schreier generator. -/
theorem quotientMap_schreierGenerator_eq_one (q : Q) (x : X) :
    D.quotientMap (D.schreierGenerator q x) = 1 := by
  simp only [schreierGenerator, transition, map_mul, quotientMap_quotientSection_apply,
      mul_assoc, map_inv,
  mul_inv_rev, mul_inv_cancel_left, mul_inv_cancel]

/-- Each evaluated finite Schreier symbol lies in the kernel of the quotient map. -/
theorem symbolEval_mem (z : FiniteSchreierSymbol X Q) :
    D.symbolEval z ∈ D.kernel := by
  rcases z with ⟨q, x⟩
  change D.quotientMap (D.symbolEval (q, x)) = 1
  exact quotientMap_schreierGenerator_eq_one (D := D) q x

/--
The image of the Schreier-symbol evaluation homomorphism lies in the kernel of the quotient map.
-/
theorem symbolEvalHom_mem
    (q : FreeGroup (FiniteSchreierSymbol X Q)) :
    D.symbolEvalHom q ∈ D.kernel := by
  have hle : D.symbolEvalHom.range ≤ D.kernel := by
    rw [symbolEvalHom, FreeGroup.range_lift_eq_closure]
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact symbolEval_mem (D := D) z
  exact hle ⟨q, rfl⟩

/-- Evaluation of Schreier symbols as a homomorphism into the kernel being rewritten. -/
def symbolEvalSubgroupHom :
    FreeGroup (FiniteSchreierSymbol X Q) →* D.kernel where
  toFun q := ⟨D.symbolEvalHom q, D.symbolEvalHom_mem q⟩
  map_one' := Subtype.ext D.symbolEvalHom.map_one
  map_mul' q r := Subtype.ext (D.symbolEvalHom.map_mul q r)

/--
Forgetting the subgroup target of \(\mathrm{symbolEvalSubgroupHom}\) gives the ordinary
evaluation homomorphism.
-/
@[simp]
theorem symbolEvalSubgroupHom_apply
    (q : FreeGroup (FiniteSchreierSymbol X Q)) :
    (D.symbolEvalSubgroupHom q : FreeGroup X) = D.symbolEvalHom q :=
  rfl

/-- The subgroup of the kernel induced by the ambient normal closure of the original relators. -/
def relatorSubgroup
    (R : Set (FreeGroup X)) :
    Subgroup D.kernel where
  carrier := {g | (g : FreeGroup X) ∈ Subgroup.normalClosure R}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, OneMemClass.coe_one, one_mem]
  mul_mem' := by
    intro a b ha hb
    exact Subgroup.mul_mem (Subgroup.normalClosure R) ha hb
  inv_mem' := by
    intro a ha
    exact Subgroup.inv_mem (Subgroup.normalClosure R) ha

/-- The subgroup generated by the relators of the presented group is normal. -/
instance relatorSubgroup_normal
    (R : Set (FreeGroup X)) :
    (D.relatorSubgroup R).Normal where
  conj_mem n hn g := by
    change ((g : FreeGroup X) * (n : FreeGroup X) * (g : FreeGroup X)⁻¹) ∈
      Subgroup.normalClosure R
    simpa [mul_assoc] using
      (Subgroup.normalClosure_normal.conj_mem
        (n : FreeGroup X) hn (g : FreeGroup X))

/-- Evaluation of a finite Schreier symbol is the corresponding Schreier generator formula. -/
@[simp]
theorem symbolEval_apply (q : Q) (x : X) :
    D.symbolEval (q, x) =
      D.quotientSection q * FreeGroup.of x *
        (D.quotientSection (D.transition q x))⁻¹ :=
  rfl

/--
Applying the transition after the inverse transition for the same generator returns the original
quotient element.
-/
theorem transition_after_inverseTransition (q : Q) (x : X) :
    D.transition (D.inverseTransition q x) x = q := by
  simp only [transition, inverseTransition, map_mul, quotientMap_quotientSection_apply, map_inv,
      mul_assoc,
  inv_mul_cancel, mul_one]

/--
Applying the inverse transition after the transition for the same generator returns the original
quotient element.
-/
theorem inverseTransition_after_transition (q : Q) (x : X) :
    D.inverseTransition (D.transition q x) x = q := by
  simp only [inverseTransition, transition, map_mul, quotientMap_quotientSection_apply, map_inv,
      mul_assoc,
  mul_inv_cancel, mul_one]

/--
Evaluation after an inverse transition has the expected representative formula ending at the
original quotient class.
-/
@[simp]
theorem symbolEval_inverseTransition (q : Q) (x : X) :
    D.symbolEval (D.inverseTransition q x, x) =
      D.quotientSection (D.inverseTransition q x) *
        FreeGroup.of x * (D.quotientSection q)⁻¹ := by
  simp only [symbolEval, schreierGenerator, inverseTransition_eq, transition_eq,
      inv_mul_cancel_right]


end FiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete
