/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.Morphisms.EtaleReduced
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Faithfulness of finite-etale pullback along a dense morphism

Over a locally Noetherian reduced base, morphisms between finite-etale covers
are determined after pullback along a quasi-compact scheme-theoretically
dominant morphism.  The proof uses reducedness of the source cover, separatedness
of the target cover, and stability of scheme-theoretic dominance under flat
base change.
-/

noncomputable section

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Pullback of finite-etale covers along a quasi-compact
scheme-theoretically dominant morphism is faithful over a locally Noetherian
reduced base. -/
instance pullback_faithful_of_schemeTheoreticallyDominant
    {U X : Scheme.{u}} (j : U ⟶ X)
    [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    [IsReduced X] [IsLocallyNoetherian X] :
    (pullback j).Faithful where
  map_injective {A B} f g hfg := by
    let hA : IsFiniteEtale A.hom := A.prop
    let hB : IsFiniteEtale B.hom := B.prop
    let hAred : IsReduced A.left :=
      @Etale.isReduced_of_isLocallyNoetherian _ _ A.hom hA.toEtale
        (inferInstance : IsReduced X) (inferInstance : IsLocallyNoetherian X)
    let hAflat : Flat A.hom := Etale.iff_flat_and_formallyUnramified.mp hA.toEtale |>.1
    let hpSTD : IsSchemeTheoreticallyDominant (Limits.pullback.fst A.hom j) :=
      @IsSchemeTheoreticallyDominant.pullbackFst _ _ _ A.hom j
        (inferInstance : IsSchemeTheoreticallyDominant j)
        (inferInstance : QuasiCompact j) hAflat
    let hpQC : QuasiCompact (Limits.pullback.fst A.hom j) := inferInstance
    let hpDom : IsDominant (Limits.pullback.fst A.hom j) :=
      (@isSchemeTheoreticallyDominant_iff_isDominant _ _
        (Limits.pullback.fst A.hom j) hpQC hAred).mp hpSTD
    let hBsep : IsSeparated B.hom :=
      @IsSeparated.of_isAffineHom _ _ B.hom hB.toIsFinite.toIsAffineHom
    apply MorphismProperty.Over.Hom.ext
    exact @ext_of_isDominant_of_isSeparated _ _ _ _ hAred f.left g.left B.hom hBsep
      ((Over.w f).trans (Over.w g).symm) (Limits.pullback.fst A.hom j) hpDom (by
        let wf : (Limits.pullback.fst A.hom j ≫ f.left) ≫ B.hom =
            Limits.pullback.snd A.hom j ≫ j := by
          exact (Category.assoc _ _ _).trans <|
            (congrArg (Limits.pullback.fst A.hom j ≫ ·) (Over.w f)).trans
              (show Limits.pullback.fst A.hom j ≫ A.hom =
                Limits.pullback.snd A.hom j ≫ j from Limits.pullback.condition)
        let wg : (Limits.pullback.fst A.hom j ≫ g.left) ≫ B.hom =
            Limits.pullback.snd A.hom j ≫ j := by
          exact (Category.assoc _ _ _).trans <|
            (congrArg (Limits.pullback.fst A.hom j ≫ ·) (Over.w g)).trans
              (show Limits.pullback.fst A.hom j ≫ A.hom =
                Limits.pullback.snd A.hom j ≫ j from Limits.pullback.condition)
        let mf := ((pullback j).map f).left
        let mg := ((pullback j).map g).left
        have hmf : mf ≫ Limits.pullback.fst B.hom j =
            Limits.pullback.fst A.hom j ≫ f.left := by
          exact Limits.pullback.lift_fst _ _ _
        have hmg : mg ≫ Limits.pullback.fst B.hom j =
            Limits.pullback.fst A.hom j ≫ g.left := by
          exact Limits.pullback.lift_fst _ _ _
        have hm : mf = mg := congrArg (fun q ↦ q.left) hfg
        exact hmf.symm.trans <| (congrArg (· ≫ Limits.pullback.fst B.hom j) hm).trans hmg)

end AlgebraicGeometry.FiniteEtale

end
