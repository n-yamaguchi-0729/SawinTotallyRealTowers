/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.FiniteKummerCoefficientH2
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTrivialization

set_option autoImplicit false
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

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type) [Field K]
variable (p : ℕ+) [Fact (p : ℕ).Prime]

private theorem absoluteMuPLinearEquivZMod_symm_coe_intCast
    (hmu : (primitiveRoots p K).Nonempty) (i : ℤ) :
    ((absoluteMuPLinearEquivZMod K p hmu).symm (i : ZMod p)).toMul.1 =
      (finiteKummerCoefficientAddHom K (AlgebraicClosure K)
        p hmu (ULift.up.{0} (i : ZMod p))).toMul := by
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
        p hmu (ULift.up.{0} z)).toMul := by
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective z
  exact absoluteMuPLinearEquivZMod_symm_coe_intCast K p hmu i

omit [Fact (p : ℕ).Prime] in
/-- The chosen-root coefficient homomorphism commutes with field embeddings. -/
theorem finiteKummerCoefficientAddHom_map
    {L M : Type} [Field L] [Field M] [Algebra K L] [Algebra K M]
    (f : L →ₐ[K] M) (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (z : ULift.{0} (ZMod (p : ℕ))) :
    Units.map f (finiteKummerCoefficientAddHom K L p hmu z).toMul =
      (finiteKummerCoefficientAddHom K M p hmu z).toMul := by
  rcases z with ⟨z⟩
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective z
  rw [finiteKummerCoefficientAddHom_intCast K L p hmu i,
    finiteKummerCoefficientAddHom_intCast K M p hmu i]
  change Units.map f (finiteKummerCoefficientRootUnit K L p hmu ^ i) =
    finiteKummerCoefficientRootUnit K M p hmu ^ i
  rw [map_zpow]
  congr 1
  apply Units.ext
  change f (algebraMap K L hmu.choose) = algebraMap K M hmu.choose
  exact f.commutes hmu.choose

end ClassFieldTower.Martinet.Shafarevich
