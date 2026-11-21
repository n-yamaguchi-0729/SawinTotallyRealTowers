/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

/-!
# Ideles in the ordinary idele-class norm quotient

This file supplies the useful composite from ideles to the quotient
of `C_K` by the range of the ordinary norm `C_L → C_K`, used by the
global norm-residue-symbol constructions.
-/



@[expose] public section

open scoped NumberField
open IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The norm class of an idèle in the standard principal quotient. -/
def globalNormClassFromIdele :
    IdeleGroup K →*
      NumberField.IdeleClassGroup (𝓞 K) K ⧸ (NumberField.IdeleClassGroup.norm K L).range :=
  (QuotientGroup.mk' (NumberField.IdeleClassGroup.norm K L).range).comp
    (IdeleGroup.toStandardClass K)

/-- The norm class of a one-place idèle uses the original standard insertion. -/
theorem globalNormClassFromIdele_finitePlaceIdele (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) :
    globalNormClassFromIdele K L (IdeleGroup.finitePlaceIdele v a) =
      QuotientGroup.mk' (NumberField.IdeleClassGroup.norm K L).range
        (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v a) := by
  rw [globalNormClassFromIdele, MonoidHom.comp_apply,
    IdeleGroup.toStandardClass_finitePlaceIdele]

/-- The canonical norm quotient kills principal idèles. -/
@[simp]
theorem globalNormClassFromIdele_principalIdele (x : Kˣ) :
    globalNormClassFromIdele K L (IdeleGroup.principalIdele K x) = 1 := by
  rw [globalNormClassFromIdele, MonoidHom.comp_apply, IdeleGroup.toStandardClass_principalIdele,
    map_one]

end Reciprocity
end GlobalClassFieldTheory
