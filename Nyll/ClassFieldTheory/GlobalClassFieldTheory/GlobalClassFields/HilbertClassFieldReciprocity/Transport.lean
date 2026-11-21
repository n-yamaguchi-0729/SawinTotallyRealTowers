/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldRealization

/-!
# Generic transport core for Hilbert class-field reciprocity

The quotient transport and its norm-residue evaluation are compiled once in
this leaf.  Big/small and actual/original Hilbert reciprocity specializations
reuse the named data provider without rebuilding the generic reciprocity
composite.
-/



@[expose] public section

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity



/-- Inverse norm-residue evaluation transported through a subgroup equality
and then through an arbitrary multiplicative equivalence. -/
theorem hilbertClassFieldQuotientTransport_inverse_apply_with
    {G : Type*} {A : Type*} {I : Type*} [Group G] [Group A] [Group I]
    (N H : Subgroup G) [N.Normal] [H.Normal]
    (e : Additive (G ⧸ N) ≃+ Additive A)
    (h : N = H) (f : G ⧸ H ≃* I) (c : G) :
    f (QuotientGroup.quotientMulEquivOfEq h
        (Additive.toMul
          (e.symm (e
            (Additive.ofMul (QuotientGroup.mk' N c)))))) =
      f (QuotientGroup.mk' H c) := by
  apply congrArg f
  calc
    _ = QuotientGroup.quotientMulEquivOfEq h
          (Additive.toMul
            (Additive.ofMul (QuotientGroup.mk' N c))) :=
      congrArg
        (fun z => QuotientGroup.quotientMulEquivOfEq h
          (Additive.toMul z))
        (e.symm_apply_apply _)
    _ = QuotientGroup.mk' H c :=
      QuotientGroup.quotientMulEquivOfEq_mk h c

/-- Global reciprocity followed by subgroup-equality transport and a chosen
quotient equivalence. -/
noncomputable def hilbertClassFieldGlobalReciprocityTransportEquiv
    {F : Type*} {E : Type*} {I : Type*}
    [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    [Group I]
    (H : Subgroup (IdeleClassGroup F))
    (h : (_root_.ideleClassNorm F E).range = H)
    (f : IdeleClassGroup F ⧸ H ≃* I) :
    Gal(E / F) ≃* I :=
  (AddEquiv.toMultiplicative
      (globalReciprocityEquiv F E)).trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans f)

/-- Evaluation of the shared transported reciprocity equivalence on the
global norm-residue symbol. -/
theorem hilbertClassFieldGlobalReciprocityTransport_globalNormResidue
    {F : Type*} {E : Type*} {I : Type*}
    [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    [Group I]
    (H : Subgroup (IdeleClassGroup F))
    (h : (_root_.ideleClassNorm F E).range = H)
    (f : IdeleClassGroup F ⧸ H ≃* I)
    (c : IdeleClassGroup F) :
    hilbertClassFieldGlobalReciprocityTransportEquiv H h f
        (globalNormResidueMonoidHom F E c) =
      f (QuotientGroup.mk' H c) := by
  let N := (_root_.ideleClassNorm F E).range
  let q := QuotientGroup.mk' N c
  let e := globalNormResidueEquiv F E
  let t := QuotientGroup.quotientMulEquivOfEq h
  let g (a : Additive (IdeleClassGroup F ⧸ N)) := f (t a.toMul)
  let a := Additive.ofMul (globalNormResidueMonoidHom F E c)
  let b := Additive.ofMul q
  have hArtin : a = e b := congrArg Additive.ofMul (globalNormResidueMonoidHom_apply F E c)
  have hTransport := QuotientGroup.quotientMulEquivOfEq_mk h c
  calc
    _ = g (e.symm a) := rfl
    _ = g (e.symm (e b)) := congrArg (g ∘ e.symm) hArtin
    _ = g b := congrArg g (e.symm_apply_apply b)
    _ = f (QuotientGroup.mk' H c) := congrArg f hTransport

/-- The transported equivalence and its evaluation theorem, packaged once for
all four Hilbert class-field specializations. -/
noncomputable def hilbertClassFieldGlobalReciprocityTransportData
    {F : Type*} {E : Type*} {I : Type*}
    [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    [Group I]
    (H : Subgroup (IdeleClassGroup F))
    (h : (_root_.ideleClassNorm F E).range = H)
    (f : IdeleClassGroup F ⧸ H ≃* I) :
    {e : Gal(E / F) ≃* I //
      ∀ c : IdeleClassGroup F,
        e (globalNormResidueMonoidHom F E c) =
          f (QuotientGroup.mk' H c)} :=
  ⟨hilbertClassFieldGlobalReciprocityTransportEquiv H h f,
    hilbertClassFieldGlobalReciprocityTransport_globalNormResidue H h f⟩

end GlobalClassFields
end GlobalClassFieldTheory
