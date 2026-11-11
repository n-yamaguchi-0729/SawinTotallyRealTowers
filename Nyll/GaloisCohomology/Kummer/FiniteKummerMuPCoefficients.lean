/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.FiniteKummerCoefficientH2
public import Nyll.GaloisCohomology.Kummer.AbsoluteMuPTrivialization

/-!
# Coherence of finite Kummer and absolute roots-of-unity coefficients

The finite chosen-root homomorphism and the existing absolute `mu_p`
trivialization use the same supplied primitive root.  Their values therefore
agree in the algebraic closure.  The finite coefficient homomorphism is
also natural under field embeddings; its `p`-th-power property is supplied
by the shared finite coefficient module.
These identities supply the coefficient comparison for absolute lifts;
none is assumed as an extra input.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

universe u

variable (K : Type u) [Field K]
variable (p : ℕ+) [Fact (p : ℕ).Prime]

private theorem absoluteMuPLinearEquivZMod_symm_coe_intCast
    (hmu : (primitiveRoots p K).Nonempty) (i : ℤ) :
    ((absoluteMuPLinearEquivZMod K p hmu).symm (i : ZMod p)).toMul.1 =
      (finiteKummerCoefficientAddHom K (AlgebraicClosure K)
        p hmu (ULift.up.{u} (i : ZMod p))).toMul := by
  let hzeta : IsPrimitiveRoot hmu.choose p :=
    (mem_primitiveRoots p.pos).mp hmu.choose_spec
  let hzetaUnit := hzeta.isUnit_unit' p.ne_zero
  rw [finiteKummerCoefficientAddHom_intCast K (AlgebraicClosure K)
    p hmu i]
  change Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom
      ((hzetaUnit.zmodEquivZPowers (i : ZMod p)).toMul : Kˣ) =
    finiteKummerCoefficientRootUnit K (AlgebraicClosure K)
      p hmu ^ i
  rw [hzetaUnit.zmodEquivZPowers_apply_coe_int]
  change Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom
      ((hzeta.isUnit p.ne_zero).unit' ^ i) = _
  rw [map_zpow]
  congr 1
  apply Units.ext
  rfl

/-- The inverse absolute trivialization has exactly the finite Kummer
coefficient value in the algebraic closure. -/
theorem absoluteMuPLinearEquivZMod_symm_coe
    (hmu : (primitiveRoots p K).Nonempty) (z : ZMod p) :
    ((absoluteMuPLinearEquivZMod K p hmu).symm z).toMul.1 =
      (finiteKummerCoefficientAddHom K (AlgebraicClosure K)
        p hmu (ULift.up.{u} z)).toMul := by
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective z
  exact absoluteMuPLinearEquivZMod_symm_coe_intCast K p hmu i


end ClassFieldTower.Martinet.Shafarevich
