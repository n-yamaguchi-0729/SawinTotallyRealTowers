/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.CleanedSymbols
import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Relators.FreeGroupLift

/-!
# Reidemeister Schreier / Discrete / Reidemeister Schreier / Finite Quotient / Cleaned Tau

This module rewrites tau words on the nondegenerate Schreier-symbol alphabet
and proves that the cleaned rewriting respects reduction, multiplication, and
the original tau evaluation.
-/


namespace ReidemeisterSchreier.Discrete

open ReidemeisterSchreier.Discrete.Presentations

variable {X Q : Type*} [Group Q] [Fintype Q]

namespace FiniteQuotientSchreierData

variable (D : FiniteQuotientSchreierData X Q)
variable [DecidableEq X]

/--
List-word form of Schreier rewriting after deleting degenerate finite Schreier generators. This
is the computational API for concrete finite examples.
-/
def cleanedTauList
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    FreeGroup D.NondegenerateSchreierSymbol :=
  D.deleteDegenerateSchreierGeneratorHom (D.tauList q xs)

omit [DecidableEq X] in
/-- The cleaned \(\tau\)-list of the empty word is the identity. -/
@[simp]
theorem cleanedTauList_nil
    [DecidablePred D.IsDegenerateSchreierSymbol] (q : Q) :
    D.cleanedTauList q [] = 1 := by
  simp only [cleanedTauList, tauList, map_one]

omit [DecidableEq X] in
/--
The cleaned \(\tau\)-list for a positive letter prefixes the corresponding cleaned
Schreier-symbol word.
-/
@[simp]
theorem cleanedTauList_cons_true
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (x : X) (xs : List (X × Bool)) :
    D.cleanedTauList q ((x, true) :: xs) =
      D.cleanedSchreierSymbolWord (q, x) *
        D.cleanedTauList (D.transition q x) xs := by
  simp only [cleanedTauList, tauList, transition_eq, map_mul,
      deleteDegenerateSchreierGeneratorHom_of]

omit [DecidableEq X] in
/--
The cleaned \(\tau\)-list for a negative letter prefixes the inverse of the corresponding
cleaned Schreier-symbol word.
-/
@[simp]
theorem cleanedTauList_cons_false
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (x : X) (xs : List (X × Bool)) :
    D.cleanedTauList q ((x, false) :: xs) =
      (D.cleanedSchreierSymbolWord (D.inverseTransition q x, x))⁻¹ *
        D.cleanedTauList (D.inverseTransition q x) xs := by
  simp only [cleanedTauList, tauList, inverseTransition_eq, map_mul, map_inv,
  deleteDegenerateSchreierGeneratorHom_of]

omit [DecidableEq X] in
/--
The cleaned \(\tau\)-list rewrite of a concatenated word splits as the product of the first
rewrite and the rewrite of the second word from the updated quotient element.
-/
theorem cleanedTauList_append
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (xs ys : List (X × Bool)) :
    D.cleanedTauList q (xs ++ ys) =
      D.cleanedTauList q xs *
        D.cleanedTauList
          (D.quotientMap (D.quotientSection q * FreeGroup.mk xs)) ys := by
  simp only [cleanedTauList, D.tauList_append, map_mul, quotientMap_quotientSection_apply]

omit [DecidableEq X] in
/-- Free-group reduction does not change the cleaned \(\tau\)-list rewrite. -/
theorem cleanedTauList_red
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) {xs ys : List (X × Bool)}
    (h : FreeGroup.Red xs ys) :
    D.cleanedTauList q xs = D.cleanedTauList q ys := by
  simp only [cleanedTauList, D.tauList_red q h]

omit [DecidableEq X] in
/-- The cleaned \(\tau\)-lists agree when the corresponding quotient generators agree. -/
theorem cleanedTauList_eq_of_mk_eq
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) {xs ys : List (X × Bool)}
    (h : FreeGroup.mk xs = FreeGroup.mk ys) :
    D.cleanedTauList q xs = D.cleanedTauList q ys := by
  simp only [cleanedTauList, D.tauList_eq_of_mk_eq q h]

/-- Schreier rewriting after deleting degenerate finite Schreier generators. -/
def cleanedTau
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    FreeGroup D.NondegenerateSchreierSymbol :=
  D.deleteDegenerateSchreierGeneratorHom (D.tau q w)

/--
Cleaned \(\tau\) of a free-group word is the cleaned \(\tau\)-list rewrite of its word
representation.
-/
theorem cleanedTau_eq_cleanedTauList_toWord
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    D.cleanedTau q w = D.cleanedTauList q w.toWord :=
  rfl

/--
The cleaned \(\tau\)-rewrite of \(\mathrm{FreeGroup.mk}(xs)\) agrees with rewriting the list
\(xs\).
-/
theorem cleanedTau_mk
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    D.cleanedTau q (FreeGroup.mk xs) = D.cleanedTauList q xs := by
  simp only [cleanedTau, D.tau_mk, cleanedTauList]

/--
Reduced list-word normal form of \(\mathrm{cleanedTau}(q,w)\). This is the computation-facing
output of the cleaned finite Reidemeister--Schreier rewriting map.
-/
noncomputable def cleanedTauNormalWord
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    List (D.NondegenerateSchreierSymbol × Bool) :=
  (D.cleanedTau q w).toWord

/-- Reduced list-word normal form of \(\mathrm{cleanedTauList}(q,xs)\). -/
noncomputable def cleanedTauListNormalWord
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    List (D.NondegenerateSchreierSymbol × Bool) :=
  (D.cleanedTauList q xs).toWord

/-- The reduced normal word reconstructs the cleaned \(\tau\)-rewrite. -/
theorem mk_cleanedTauNormalWord
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    FreeGroup.mk (D.cleanedTauNormalWord q w) = D.cleanedTau q w := by
  simpa [cleanedTauNormalWord] using
    (FreeGroup.mk_toWord (x := D.cleanedTau q w))

omit [DecidableEq X] in
/-- The reduced normal word reconstructs the cleaned \(\tau\)-list rewrite. -/
theorem mk_cleanedTauListNormalWord
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    FreeGroup.mk (D.cleanedTauListNormalWord q xs) =
      D.cleanedTauList q xs := by
  simpa [cleanedTauListNormalWord] using
    (FreeGroup.mk_toWord (x := D.cleanedTauList q xs))

/--
The normal word of the cleaned \(\tau\)-rewrite of `FreeGroup.mk xs` is the normal word obtained
by cleaning the list `xs` directly.
-/
theorem cleanedTauNormalWord_mk
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    D.cleanedTauNormalWord q (FreeGroup.mk xs) =
      D.cleanedTauListNormalWord q xs := by
  simp only [cleanedTauNormalWord, D.cleanedTau_mk, cleanedTauListNormalWord]

/--
A cleaned \(\tau\)-rewrite equals `FreeGroup.mk ys` exactly when its normal word is
`FreeGroup.reduce ys`.
-/
theorem cleanedTau_eq_mk_iff_cleanedTauNormalWord_eq_reduce
    {D : FiniteQuotientSchreierData X Q}
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    {q : Q} {w : FreeGroup X}
    {ys : List (D.NondegenerateSchreierSymbol × Bool)} :
    D.cleanedTau q w = FreeGroup.mk ys ↔
      D.cleanedTauNormalWord q w = FreeGroup.reduce ys := by
  unfold cleanedTauNormalWord
  rw [← FreeGroup.toWord_inj]
  constructor
  · intro h
    exact h
  · intro h
    exact h

omit [DecidableEq X] in
/--
The cleaned \(\tau\)-list normal word records the reduced list form of the cleaned \(\tau\)-list
rewrite.
-/
theorem cleanedTauList_eq_mk_iff_cleanedTauListNormalWord_eq_reduce
    {D : FiniteQuotientSchreierData X Q}
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    {q : Q} {xs : List (X × Bool)}
    {ys : List (D.NondegenerateSchreierSymbol × Bool)} :
    D.cleanedTauList q xs = FreeGroup.mk ys ↔
      D.cleanedTauListNormalWord q xs = FreeGroup.reduce ys := by
  unfold cleanedTauListNormalWord
  rw [← FreeGroup.toWord_inj]
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
If the substituted cleaned \(\tau\)-normal word reduces to \(ys\), then the target lift of the
cleaned \(\tau\)-word is \(\mathrm{FreeGroup.mk}(ys)\).
-/
theorem targetLift_cleanedTau_eq_mk_of_substitutionWord_reduce_eq
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {toTargetGenerator : D.NondegenerateSchreierSymbol → FreeGroup Y}
    (q : Q) (w : FreeGroup X) {ys : List (Y × Bool)}
    (h :
      FreeGroup.reduce
          (freeGroupSubstitutionWord toTargetGenerator
            (D.cleanedTauNormalWord q w)) =
        FreeGroup.reduce ys) :
    FreeGroup.lift toTargetGenerator (D.cleanedTau q w) =
      FreeGroup.mk ys := by
  rw [← D.mk_cleanedTauNormalWord q w]
  exact freeGroup_lift_mk_eq_mk_of_substitutionWord_reduce_eq h

/--
If the substituted cleaned \(\tau\)-normal word reduces to a word relator-equivalent to \(1\),
then the target lift of the cleaned \(\tau\)-word is relator-equivalent to \(1\).
-/
theorem targetLift_cleanedTau_relatorEquivalent_one_of_substitutionWord_reduce_eq
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {S : Set (FreeGroup Y)}
    {toTargetGenerator : D.NondegenerateSchreierSymbol → FreeGroup Y}
    (q : Q) (w : FreeGroup X) {ys : List (Y × Bool)}
    (h :
      FreeGroup.reduce
          (freeGroupSubstitutionWord toTargetGenerator
            (D.cleanedTauNormalWord q w)) =
        FreeGroup.reduce ys)
    (hy : RelatorEquivalent S (FreeGroup.mk ys) 1) :
    RelatorEquivalent S
      (FreeGroup.lift toTargetGenerator (D.cleanedTau q w)) 1 :=
  (RelatorEquivalent.of_eq
    (D.targetLift_cleanedTau_eq_mk_of_substitutionWord_reduce_eq
      (toTargetGenerator := toTargetGenerator) q w h)).trans hy

/--
If the substituted cleaned \(\tau\)-normal word reduces to a target relator, then the target
lift of the cleaned \(\tau\)-word is relator-equivalent to \(1\).
-/
theorem targetLift_cleanedTau_relatorEquivalent_one_of_substitutionWord_reduce_mem
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {S : Set (FreeGroup Y)}
    {toTargetGenerator : D.NondegenerateSchreierSymbol → FreeGroup Y}
    (q : Q) (w : FreeGroup X) {ys : List (Y × Bool)}
    (h :
      FreeGroup.reduce
          (freeGroupSubstitutionWord toTargetGenerator
            (D.cleanedTauNormalWord q w)) =
        FreeGroup.reduce ys)
    (hy : FreeGroup.mk ys ∈ S) :
    RelatorEquivalent S
      (FreeGroup.lift toTargetGenerator (D.cleanedTau q w)) 1 :=
  D.targetLift_cleanedTau_relatorEquivalent_one_of_substitutionWord_reduce_eq
    (toTargetGenerator := toTargetGenerator) q w h
    (RelatorEquivalent.of_mem hy)

/--
If substitution reduces every cleaned source relator to a target word relator-equivalent to
\(1\), then the induced generator map sends every cleaned relator to a word relator-equivalent
to \(1\).
-/
theorem mapsCleanedRelators_of_cleanedTauNormalWord_reduce
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    {toTargetGenerator : D.NondegenerateSchreierSymbol → FreeGroup Y}
    (targetWord : Q → FreeGroup X → List (Y × Bool))
    (hword :
      ∀ q : Q, ∀ r ∈ R,
        FreeGroup.reduce
            (freeGroupSubstitutionWord toTargetGenerator
              (D.cleanedTauNormalWord q r)) =
          FreeGroup.reduce (targetWord q r))
    (hrel :
      ∀ q : Q, ∀ r ∈ R,
        RelatorEquivalent S (FreeGroup.mk (targetWord q r)) 1) :
    ∀ q : Q, ∀ r ∈ R,
      RelatorEquivalent S
        (FreeGroup.lift toTargetGenerator (D.cleanedTau q r)) 1 := by
  intro q r hr
  exact
    D.targetLift_cleanedTau_relatorEquivalent_one_of_substitutionWord_reduce_eq
      (toTargetGenerator := toTargetGenerator) q r (hword q r hr)
      (hrel q r hr)

/--
If substitution reduces every cleaned source relator to a word in the target relator set, then
the induced generator map sends every cleaned relator to a word relator-equivalent to \(1\).
-/
theorem mapsCleanedRelators_of_cleanedTauNormalWord_reduce_mem
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    {toTargetGenerator : D.NondegenerateSchreierSymbol → FreeGroup Y}
    (targetWord : Q → FreeGroup X → List (Y × Bool))
    (hword :
      ∀ q : Q, ∀ r ∈ R,
        FreeGroup.reduce
            (freeGroupSubstitutionWord toTargetGenerator
              (D.cleanedTauNormalWord q r)) =
          FreeGroup.reduce (targetWord q r))
    (hmem :
      ∀ q : Q, ∀ r ∈ R, FreeGroup.mk (targetWord q r) ∈ S) :
    ∀ q : Q, ∀ r ∈ R,
      RelatorEquivalent S
        (FreeGroup.lift toTargetGenerator (D.cleanedTau q r)) 1 :=
  D.mapsCleanedRelators_of_cleanedTauNormalWord_reduce targetWord hword
    (fun q r hr => RelatorEquivalent.of_mem (hmem q r hr))

/-- The \(\tau\)-word for the identity case evaluates to the identity. -/
@[simp]
theorem cleanedTau_one
    [DecidablePred D.IsDegenerateSchreierSymbol] (q : Q) :
    D.cleanedTau q 1 = 1 := by
  simp only [cleanedTau, tau_one, map_one]

/--
The cleaned \(\tau\)-rewrite of a product factors into the rewrite of the first word and the
rewrite of the second word from the updated quotient element.
-/
theorem cleanedTau_mul
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (u v : FreeGroup X) :
    D.cleanedTau q (u * v) =
      D.cleanedTau q u *
        D.cleanedTau (D.quotientMap (D.quotientSection q * u)) v := by
  simp only [cleanedTau, D.tau_mul, map_mul, quotientMap_quotientSection_apply]

/--
For a kernel word, the cleaned \(\tau\)-rewriting preserves products from the identity quotient
element.
-/
theorem cleanedTau_mul_of_mem_kernel
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {u : FreeGroup X} (hu : u ∈ D.kernel) (v : FreeGroup X) :
    D.cleanedTau 1 (u * v) = D.cleanedTau 1 u * D.cleanedTau 1 v := by
  have h := D.tau_mul_of_mem_kernel (u := u) (v := v) hu
  simp only [cleanedTau, h, map_mul]

/--
The cleaned \(\tau\)-rewrite of an inverse is the inverse of the \(\tau\)-rewrite from the
updated quotient element.
-/
theorem cleanedTau_inv
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (u : FreeGroup X) :
    D.cleanedTau (D.quotientMap (D.quotientSection q * u)) u⁻¹ =
      (D.cleanedTau q u)⁻¹ := by
  unfold cleanedTau
  rw [D.tau_inv]
  simp only [map_inv]

/--
For a kernel word, the cleaned \(\tau\)-rewriting commutes with inversion from the identity
quotient element.
-/
theorem cleanedTau_inv_of_mem_kernel
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {u : FreeGroup X} (hu : u ∈ D.kernel) :
    D.cleanedTau 1 u⁻¹ = (D.cleanedTau 1 u)⁻¹ := by
  have h := D.tau_inv_of_mem_kernel (u := u) hu
  simp only [cleanedTau, h, map_inv]

/--
Evaluating a cleaned \(\tau\)-word through nondegenerate symbols gives the same quotient-section
conjugate as the uncleaned \(\tau\)-word.
-/
theorem nondegenerateSymbolEvalHom_cleanedTau
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    D.nondegenerateSymbolEvalHom (D.cleanedTau q w) =
      D.quotientSection q * w *
        (D.quotientSection
          (D.quotientMap (D.quotientSection q * w)))⁻¹ := by
  rw [cleanedTau, D.nondegenerateSymbolEvalHom_deleteDegenerateSchreierGeneratorHom]
  exact D.symbolEvalHom_tau q w

/--
For a kernel word, cleaned \(\tau\) sends natural powers to powers of the cleaned \(\tau\)-word.
-/
theorem cleanedTau_pow_of_mem_kernel
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {u : FreeGroup X} (hu : u ∈ D.kernel) (n : ℕ) :
    D.cleanedTau 1 (u ^ n) = (D.cleanedTau 1 u) ^ n := by
  induction n with
  | zero =>
      simp only [pow_zero, cleanedTau_one]
  | succ n ih =>
      rw [pow_succ, pow_succ]
      rw [D.cleanedTau_mul_of_mem_kernel (D.kernel.pow_mem hu n)]
      rw [ih]

/--
For a kernel word, cleaned \(\tau\) sends integer powers to powers of the cleaned \(\tau\)-word.
-/
theorem cleanedTau_zpow_of_mem_kernel
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {u : FreeGroup X} (hu : u ∈ D.kernel) (n : ℤ) :
    D.cleanedTau 1 (u ^ n) = (D.cleanedTau 1 u) ^ n := by
  cases n with
  | ofNat n =>
      simpa using D.cleanedTau_pow_of_mem_kernel hu n
  | negSucc n =>
      have hpow := D.cleanedTau_pow_of_mem_kernel hu (n + 1)
      have hinv := D.cleanedTau_inv_of_mem_kernel (D.kernel.pow_mem hu (n + 1))
      calc
        D.cleanedTau 1 (u ^ Int.negSucc n) =
            D.cleanedTau 1 ((u ^ (n + 1))⁻¹) := by
              simp only [zpow_negSucc]
        _ = (D.cleanedTau 1 (u ^ (n + 1)))⁻¹ := hinv
        _ = ((D.cleanedTau 1 u) ^ (n + 1))⁻¹ := by rw [hpow]
        _ = (D.cleanedTau 1 u) ^ Int.negSucc n := by
              simp only [zpow_negSucc]

/--
For kernel words, cleaned \(\tau\) sends a conjugate to the conjugate of the cleaned
\(\tau\)-words.
-/
theorem cleanedTau_conj_of_mem_kernel
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {a u : FreeGroup X} (ha : a ∈ D.kernel) (hu : u ∈ D.kernel) :
    D.cleanedTau 1 (a * u * a⁻¹) =
      D.cleanedTau 1 a * D.cleanedTau 1 u * (D.cleanedTau 1 a)⁻¹ := by
  rw [mul_assoc]
  rw [D.cleanedTau_mul_of_mem_kernel ha (u * a⁻¹)]
  rw [D.cleanedTau_mul_of_mem_kernel hu a⁻¹]
  rw [D.cleanedTau_inv_of_mem_kernel ha]
  rw [mul_assoc]


end FiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete
