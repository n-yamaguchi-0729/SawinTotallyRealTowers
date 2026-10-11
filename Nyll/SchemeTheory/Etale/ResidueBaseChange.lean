/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Purely inseparable residue extensions under base change

For an actual prime of a tensor product, pure inseparability at its image
in the original algebra implies pure inseparability over the new base.
The proof uses the uniqueness of field embeddings and the two generators
of the tensor product. No universal injectivity away from the selected
point is required.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace Algebra

/-- Pure inseparability at a selected prime is preserved by arbitrary base
change, expressed through the canonical maps of the actual residue fields. -/
theorem isPurelyInseparable_residueFieldMap_tensorProduct
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (P : Ideal T) [P.IsPrime] [P.LiesOver p]
    (Q : Ideal (T ⊗[R] S)) [Q.IsPrime] [Q.LiesOver P]
    (hq : q = Q.comap (TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S).toRingHom)
    (hpure : (Ideal.ResidueField.map p q (algebraMap R S) (q.over_def p)).IsPurelyInseparable) :
    (Ideal.ResidueField.map P Q (algebraMap T (T ⊗[R] S))
      (Q.over_def P)).IsPurelyInseparable := by
  let a := Ideal.ResidueField.map p q (algebraMap R S) (q.over_def p)
  let b := Ideal.ResidueField.map p P (algebraMap R T) (P.over_def p)
  let c := Ideal.ResidueField.map q Q
    (TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S).toRingHom hq
  let d := Ideal.ResidueField.map P Q (algebraMap T (T ⊗[R] S)) (Q.over_def P)
  have hbase : (algebraMap T (T ⊗[R] S)).comp (algebraMap R T) =
      (TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S).toRingHom.comp (algebraMap R S) :=
    TensorProduct.includeLeftRingHom_comp_algebraMap
  have hcomm : c.comp a = d.comp b := by
    apply Ideal.ResidueField.ringHom_ext
    apply RingHom.ext
    intro r
    simp only [a, b, c, d, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
    exact congrArg (algebraMap (T ⊗[R] S) Q.ResidueField)
      (RingHom.congr_fun hbase r).symm
  let : Algebra p.ResidueField q.ResidueField := a.toAlgebra
  let : IsPurelyInseparable p.ResidueField q.ResidueField := hpure
  let : Algebra P.ResidueField Q.ResidueField := d.toAlgebra
  change IsPurelyInseparable P.ResidueField Q.ResidueField
  let : Nonempty (Q.ResidueField →+* AlgebraicClosure Q.ResidueField) :=
    ⟨algebraMap _ _⟩
  apply IsPurelyInseparable.of_injective_comp_algebraMap
    P.ResidueField Q.ResidueField (AlgebraicClosure Q.ResidueField)
  intro α β h
  change α.comp d = β.comp d at h
  have hc : α.comp c = β.comp c := by
    apply IsPurelyInseparable.injective_comp_algebraMap
      p.ResidueField q.ResidueField (AlgebraicClosure Q.ResidueField)
    change (α.comp c).comp a = (β.comp c).comp a
    calc
      (α.comp c).comp a = α.comp (c.comp a) := RingHom.comp_assoc _ _ _
      _ = α.comp (d.comp b) := congrArg α.comp hcomm
      _ = (α.comp d).comp b := (RingHom.comp_assoc _ _ _).symm
      _ = (β.comp d).comp b := congrArg (fun k ↦ k.comp b) h
      _ = β.comp (d.comp b) := RingHom.comp_assoc _ _ _
      _ = β.comp (c.comp a) := congrArg β.comp hcomm.symm
      _ = (β.comp c).comp a := (RingHom.comp_assoc _ _ _).symm
  apply Ideal.ResidueField.ringHom_ext
  apply TensorProduct.ringHom_ext
  · apply RingHom.ext
    intro t
    change α (algebraMap (T ⊗[R] S) Q.ResidueField
        (algebraMap T (T ⊗[R] S) t)) =
      β (algebraMap (T ⊗[R] S) Q.ResidueField (algebraMap T (T ⊗[R] S) t))
    simpa only [d, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap] using
      RingHom.congr_fun h (algebraMap T P.ResidueField t)
  · apply RingHom.ext
    intro s
    simpa only [c, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap] using
      RingHom.congr_fun hc (algebraMap S q.ResidueField s)

end Algebra
