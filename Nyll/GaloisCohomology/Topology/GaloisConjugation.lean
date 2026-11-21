/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Continuity of semilinear conjugation for Krull topologies

Finite intermediate fields pull back along the specified semilinear field
equivalence. Their fixing subgroups prove continuity on the original Galois
groups, with independent universes for both bases and both ambient fields.
-/

@[expose] public section

noncomputable section

universe u v w z

open scoped Topology Pointwise

namespace RamificationTheory.Field.absoluteGaloisGroup

private theorem finiteDimensional_comap_algEquiv
    {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) (E : IntermediateField F B)
    [FiniteDimensional F E] :
    FiniteDimensional F (E.comap e.toAlgHom) := by
  let Ecomap : IntermediateField F A := E.comap e.toAlgHom
  let eLin : Ecomap ≃ₗ[F] E :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun x => ⟨e.symm x.1, by
        change e (e.symm x.1) ∈ E
        rw [e.apply_symm_apply]
        exact x.2⟩
      left_inv := by
        intro x
        ext
        exact e.symm_apply_apply x.1
      right_inv := by
        intro x
        ext
        exact e.apply_symm_apply x.1
      map_add' x y := Subtype.ext (map_add e x.1 y.1)
      map_smul' a x := Subtype.ext (e.toLinearEquiv.map_smul a x.1) }
  exact Module.Finite.equiv eLin.symm

theorem finiteDimensional_map_algEquiv
    {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) (E : IntermediateField F A)
    [FiniteDimensional F E] :
    FiniteDimensional F (E.map e.toAlgHom) := by
  let Emap : IntermediateField F B := E.map e.toAlgHom
  let eLin : E ≃ₗ[F] Emap :=
    { toFun := fun x => ⟨e x.1, ⟨x.1, x.2, rfl⟩⟩
      invFun := fun x => ⟨e.symm x.1, by
        rcases x.2 with ⟨y, hy, hxy⟩
        rw [← hxy]
        simpa using hy⟩
      left_inv := by
        intro x
        ext
        exact e.symm_apply_apply x.1
      right_inv := by
        intro x
        ext
        exact e.apply_symm_apply x.1
      map_add' x y := Subtype.ext (map_add e x.1 y.1)
      map_smul' := by
        intro a x
        ext
        exact e.toLinearEquiv.map_smul a x.1 }
  exact Module.Finite.equiv eLin

/-- Pull back an intermediate field along a ring equivalence which is
semilinear over a base-field equivalence.  This is the finite-level source
needed for Krull-continuity of conjugation by such a semilinear equivalence. -/
def semilinearRingEquivPreimageIntermediateField
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') : IntermediateField F Ω where
  carrier := {x : Ω | e x ∈ E}
  zero_mem' := by rw [Set.mem_ofPred_eq, map_zero]; exact E.zero_mem
  one_mem' := by rw [Set.mem_ofPred_eq, map_one]; exact E.one_mem
  add_mem' := by
    intro x y hx hy
    simpa using E.add_mem hx hy
  mul_mem' := by
    intro x y hx hy
    simpa using E.mul_mem hx hy
  inv_mem' := by
    intro x hx
    simpa using E.inv_mem hx
  algebraMap_mem' := by
    intro x
    change e (algebraMap F Ω x) ∈ E
    rw [he x]
    exact E.algebraMap_mem (τ x)

/-- States the theorem `mem_semilinearRingEquivPreimageIntermediateField_iff`. -/
@[simp]
theorem mem_semilinearRingEquivPreimageIntermediateField_iff
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') (x : Ω) :
    x ∈ semilinearRingEquivPreimageIntermediateField τ e he E ↔ e x ∈ E :=
  Iff.rfl

/-- States the theorem `semilinearRingEquivPreimageIntermediateField_symm_mem`. -/
theorem semilinearRingEquivPreimageIntermediateField_symm_mem
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') {x : Ω'} (hx : x ∈ E) :
    e.symm x ∈ semilinearRingEquivPreimageIntermediateField τ e he E := by
  change e (e.symm x) ∈ E
  simpa using hx

/-- The semilinear pullback of a finite intermediate field is finite. -/
theorem finiteDimensional_semilinearRingEquivPreimageIntermediateField
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') [FiniteDimensional F' E] :
    FiniteDimensional F
      (semilinearRingEquivPreimageIntermediateField τ e he E) := by
  let T := semilinearRingEquivPreimageIntermediateField τ e he E
  let f : E →ₛₗ[(τ.symm : F' →+* F)] T :=
    { toFun := fun x =>
        ⟨e.symm x.1,
          semilinearRingEquivPreimageIntermediateField_symm_mem
            τ e he E x.2⟩
      map_add' x y := Subtype.ext (map_add e.symm x.1 y.1)
      map_smul' := by
        intro a x
        ext
        simp only [Algebra.smul_def]
        change e.symm (algebraMap F' Ω' a * x.1) =
          algebraMap F Ω (τ.symm a) * e.symm x.1
        have hbase :
            e (algebraMap F Ω (τ.symm a)) =
              algebraMap F' Ω' a := by
          simpa using he (τ.symm a)
        apply e.injective
        calc
          e (e.symm (algebraMap F' Ω' a * x.1)) =
              algebraMap F' Ω' a * x.1 := by
                rw [e.apply_symm_apply]
          _ = e (algebraMap F Ω (τ.symm a)) * x.1 := by
                rw [hbase]
          _ = e (algebraMap F Ω (τ.symm a)) * e (e.symm x.1) := by
                rw [e.apply_symm_apply]
          _ = e (algebraMap F Ω (τ.symm a) * e.symm x.1) := by
                rw [map_mul] }
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨⟨e y.1, y.2⟩, ?_⟩
    ext
    exact e.symm_apply_apply y.1
  have hfgImage : Submodule.FG ((⊤ : Submodule F' E).map f) :=
    (Module.Finite.fg_top (R := F') (M := E)).map f
  have hmaptop : (⊤ : Submodule F' E).map f =
      (⊤ : Submodule F T) := by
    rw [Submodule.map_top, LinearMap.range_eq_top_of_surjective f hsurj]
  change Module.Finite F T
  exact Module.Finite.of_fg_top (by simpa [hmaptop] using hfgImage)

/-- Conjugation by a semilinear equivalence of an algebraic closure is
continuous for the Krull topology.  The semilinear base action is recorded
explicitly by `he`, and the group homomorphism is required only to have the
corresponding conjugation formula on underlying ring equivalences. -/
theorem semilinear_conjugation_continuous
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (φ : Gal(Ω / F) →* Gal(Ω' / F'))
    (hφ : ∀ g : Gal(Ω / F),
      (φ g).toRingEquiv =
        e.symm.trans (g.toRingEquiv.trans e)) :
    Continuous φ := by
  refine continuous_of_continuousAt_one φ ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff F' Ω' s).1 hs with
    ⟨E, hE, hEs⟩
  let Epre : IntermediateField F Ω :=
    semilinearRingEquivPreimageIntermediateField τ e he E
  have : FiniteDimensional F' E := hE
  have : FiniteDimensional F Epre :=
    finiteDimensional_semilinearRingEquivPreimageIntermediateField
      τ e he E
  refine (krullTopology_mem_nhds_one_iff F Ω (φ ⁻¹' s)).2 ?_
  refine ⟨Epre, inferInstance, ?_⟩
  intro σ hσ
  apply hEs
  change φ σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hxpre : e.symm x ∈ Epre :=
    semilinearRingEquivPreimageIntermediateField_symm_mem
      τ e he E hx
  have hfix :=
    (IntermediateField.mem_fixingSubgroup_iff Epre σ).1 hσ
      (e.symm x) hxpre
  change (φ σ).toRingEquiv x = x
  rw [hφ σ]
  change e (σ (e.symm x)) = x
  rw [hfix, e.apply_symm_apply]

/-- Algebra-equivalence conjugation is continuous for Krull topologies. -/
theorem algEquiv_autCongr_continuous
    {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) :
    Continuous (AlgEquiv.autCongr e : Gal(A / F) → Gal(B / F)) := by
  refine continuous_of_continuousAt_one (AlgEquiv.autCongr e).toMonoidHom ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff F B s).1 hs with
    ⟨E, hE, hEs⟩
  let Ecomap : IntermediateField F A := E.comap e.toAlgHom
  have : FiniteDimensional F E := hE
  have : FiniteDimensional F Ecomap :=
    finiteDimensional_comap_algEquiv e E
  refine (krullTopology_mem_nhds_one_iff F A
    ((AlgEquiv.autCongr e) ⁻¹' s)).2 ?_
  refine ⟨Ecomap, inferInstance, ?_⟩
  intro σ hσ
  apply hEs
  change AlgEquiv.autCongr e σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change e (σ (e.symm x)) = x
  have hxEcomap : e.symm x ∈ Ecomap := by
    change e (e.symm x) ∈ E
    rw [e.apply_symm_apply]
    exact hx
  have hfix := (IntermediateField.mem_fixingSubgroup_iff Ecomap σ).1 hσ
    (e.symm x) hxEcomap
  rw [hfix]
  exact e.apply_symm_apply x

/-- The inverse of algebra-equivalence conjugation is continuous for Krull
topologies. -/
theorem algEquiv_autCongr_symm_continuous
    {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) :
    Continuous ((AlgEquiv.autCongr e).symm : Gal(B / F) → Gal(A / F)) := by
  rw [AlgEquiv.autCongr_symm]
  exact algEquiv_autCongr_continuous e.symm

end RamificationTheory.Field.absoluteGaloisGroup
