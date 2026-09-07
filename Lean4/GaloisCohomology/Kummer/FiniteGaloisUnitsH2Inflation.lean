import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Tactic.Abel

set_option autoImplicit false

/-!
# Injectivity of field-unit H² inflation

The map is induced by actual restriction to a normal intermediate field
and inclusion of its units. For a finite Galois upper field, Hilbert 90
corrects an upper primitive by an actual principal one-coboundary. The
corrected primitive is constant on restriction fibres and its values are
fixed by all relative automorphisms, so it descends to the lower field.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable (E : IntermediateField K L) [Normal K E]

private def unitsInclusion :
    Rep.ofAlgebraAutOnUnits K E →+ Rep.ofAlgebraAutOnUnits K L :=
  (Units.map E.val.toMonoidHom).toAdditive

omit [Normal K E] in
private theorem unitsInclusion_injective : Function.Injective (unitsInclusion K L E) :=
  Units.map_injective E.val.injective

private theorem unitsInclusion_equivariant (σ : Gal(L/K)) (a : Rep.ofAlgebraAutOnUnits K E) :
    unitsInclusion K L E ((Rep.ofAlgebraAutOnUnits K E).ρ
      (AlgEquiv.restrictNormalHom E σ) a) =
      (Rep.ofAlgebraAutOnUnits K L).ρ σ (unitsInclusion K L E a) := by
  apply Units.ext
  exact (σ.restrictNormal_commutes E ((show Additive Eˣ from a).toMul : E))

/-- The actual inclusion of lower-field units, equivariant for restriction
of the upper Galois group to the normal intermediate field. -/
def finiteGaloisUnitsInflationRepHom :
    Rep.res (AlgEquiv.restrictNormalHom E)
      (Rep.ofAlgebraAutOnUnits K E) ⟶ Rep.ofAlgebraAutOnUnits K L := by
  apply Rep.ofHom
  refine ⟨(unitsInclusion K L E).toIntLinearMap, ?_⟩
  intro σ
  apply LinearMap.ext
  intro a
  exact unitsInclusion_equivariant K L E σ a

/-- Inflation with the actual field-unit coefficient inclusion in a finite
Galois tower. -/
def finiteGaloisUnitsH2Inflation :
    groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 :=
  groupCohomology.map (AlgEquiv.restrictNormalHom E)
    (finiteGaloisUnitsInflationRepHom K L E) 2

private theorem restrictNormal_restrictScalars (τ : Gal(L/E)) :
    AlgEquiv.restrictNormalHom E (τ.restrictScalars K) = 1 := by
  ext a
  change (((τ.restrictScalars K).restrictNormal E a) : L) = (a : L)
  exact ((τ.restrictScalars K).restrictNormal_commutes E a).trans (τ.commutes a)

omit [Normal K E] in
private theorem unitsInclusion_relative_fixed (τ : Gal(L/E)) (a : Rep.ofAlgebraAutOnUnits K E) :
    (Rep.ofAlgebraAutOnUnits K L).ρ (τ.restrictScalars K) (unitsInclusion K L E a) =
      unitsInclusion K L E a := by
  apply Units.ext
  exact τ.commutes ((show Additive Eˣ from a).toMul : E)

private theorem exists_relativeAut_of_restrictNormal_eq_one
    (σ : Gal(L/K)) (hσ : AlgEquiv.restrictNormalHom E σ = 1) :
    ∃ τ : Gal(L/E), τ.restrictScalars K = σ := by
  have hmem : σ ∈ E.fixingSubgroup := by
    rw [← E.restrictNormalHom_ker]
    exact hσ
  exact ⟨E.fixingSubgroupEquiv ⟨σ, hmem⟩, rfl⟩

variable [FiniteDimensional K L] [IsGalois K L]

omit [Normal K E] in
private theorem exists_unitsInclusion_eq_of_fixed (a : Rep.ofAlgebraAutOnUnits K L)
    (ha : ∀ τ : Gal(L/E), (Rep.ofAlgebraAutOnUnits K L).ρ (τ.restrictScalars K) a = a) :
    ∃ b : Rep.ofAlgebraAutOnUnits K E, unitsInclusion K L E b = a := by
  have hfix : ∀ τ : Gal(L/E), τ ((show Additive Lˣ from a).toMul : L) = ((show Additive Lˣ from a).toMul : L) := by
    intro τ
    exact congrArg Units.val (ha τ)
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := E) (E := L) ((show Additive Lˣ from a).toMul : L)).mpr hfix
  have hb0 : b ≠ 0 := by
    intro h
    apply Units.ne_zero (show Additive Lˣ from a).toMul
    rw [← hb, h, map_zero]
  refine ⟨Additive.ofMul (Units.mk0 b hb0), ?_⟩
  apply Units.ext
  exact hb

omit [IsGalois K L] in
private theorem exists_primitive_constant_on_relativeAut
    (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K E))
    (b : Gal(L/K) → Rep.ofAlgebraAutOnUnits K L)
    (hb : ∀ σ τ : Gal(L/K),
      (Rep.ofAlgebraAutOnUnits K L).ρ σ (b τ) - b (σ * τ) + b σ =
        unitsInclusion K L E
          (c (AlgEquiv.restrictNormalHom E σ, AlgEquiv.restrictNormalHom E τ))) :
    ∃ b' : Gal(L/K) → Rep.ofAlgebraAutOnUnits K L,
      (∀ σ τ : Gal(L/K),
        (Rep.ofAlgebraAutOnUnits K L).ρ σ (b' τ) - b' (σ * τ) + b' σ =
          unitsInclusion K L E
            (c (AlgEquiv.restrictNormalHom E σ, AlgEquiv.restrictNormalHom E τ))) ∧
      ∀ τ : Gal(L/E), b' (τ.restrictScalars K) = b' 1 := by
  have h0 : b 1 = unitsInclusion K L E (c (1, 1)) := by
    simpa only [map_one, Module.End.one_apply, one_mul, sub_self, zero_add] using hb 1 1
  have hfixed (τ : Gal(L/E)) : (Rep.ofAlgebraAutOnUnits K L).ρ (τ.restrictScalars K) (b 1) = b 1 := by
    rw [h0, unitsInclusion_relative_fixed]
  let f : Gal(L/E) → Lˣ := fun τ ↦ (show Additive Lˣ from b (τ.restrictScalars K) - b 1).toMul
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro σ τ
    change b ((σ * τ).restrictScalars K) - b 1 =
      (Rep.ofAlgebraAutOnUnits K L).ρ (σ.restrictScalars K) (b (τ.restrictScalars K) - b 1) +
        (b (σ.restrictScalars K) - b 1)
    have h := hb (σ.restrictScalars K) (τ.restrictScalars K)
    rw [restrictNormal_restrictScalars, restrictNormal_restrictScalars, ← h0] at h
    change (Rep.ofAlgebraAutOnUnits K L).ρ (σ.restrictScalars K) (b (τ.restrictScalars K)) -
      b ((σ * τ).restrictScalars K) + b (σ.restrictScalars K) = b 1 at h
    have heq : b ((σ * τ).restrictScalars K) =
        (Rep.ofAlgebraAutOnUnits K L).ρ (σ.restrictScalars K) (b (τ.restrictScalars K)) +
          b (σ.restrictScalars K) - b 1 := by
      rw [← h]
      abel
    rw [heq, map_sub, hfixed]
    abel
  obtain ⟨β, hβ⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  let βa : Rep.ofAlgebraAutOnUnits K L := Additive.ofMul β
  let b' : Gal(L/K) → Rep.ofAlgebraAutOnUnits K L :=
    b - groupCohomology.d₀₁ (Rep.ofAlgebraAutOnUnits K L) βa
  have hd : groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits K L) b' =
      groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits K L) b := by
    change groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits K L)
      (b - groupCohomology.d₀₁ (Rep.ofAlgebraAutOnUnits K L) βa) = _
    rw [map_sub, groupCohomology.d₀₁_comp_d₁₂_apply, sub_zero]
  refine ⟨b', ?_, ?_⟩
  · intro σ τ
    exact (congrFun hd (σ, τ)).trans (hb σ τ)
  · intro τ
    have hβ' : (Rep.ofAlgebraAutOnUnits K L).ρ (τ.restrictScalars K) βa - βa =
        b (τ.restrictScalars K) - b 1 := hβ τ
    change b (τ.restrictScalars K) -
        ((Rep.ofAlgebraAutOnUnits K L).ρ (τ.restrictScalars K) βa - βa) =
      b 1 - ((Rep.ofAlgebraAutOnUnits K L).ρ 1 βa - βa)
    rw [hβ', map_one, Module.End.one_apply]
    abel

private theorem exists_lower_primitive
    (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K E))
    (b : Gal(L/K) → Rep.ofAlgebraAutOnUnits K L)
    (hb : ∀ σ τ : Gal(L/K),
      (Rep.ofAlgebraAutOnUnits K L).ρ σ (b τ) - b (σ * τ) + b σ =
        unitsInclusion K L E
          (c (AlgEquiv.restrictNormalHom E σ, AlgEquiv.restrictNormalHom E τ)))
    (hn : ∀ τ : Gal(L/E), b (τ.restrictScalars K) = b 1) :
    ∃ a : Gal(E/K) → Rep.ofAlgebraAutOnUnits K E,
      groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits K E) a = c := by
  have h0 : b 1 = unitsInclusion K L E (c (1, 1)) := by
    simpa only [map_one, Module.End.one_apply, one_mul, sub_self, zero_add] using hb 1 1
  have hright (σ : Gal(L/K)) (τ : Gal(L/E)) : b (σ * τ.restrictScalars K) = b σ := by
    have h := hb σ (τ.restrictScalars K)
    rw [restrictNormal_restrictScalars, groupCohomology.cocycles₂_map_one_snd,
      unitsInclusion_equivariant, ← h0, hn] at h
    have h' : b σ = b (σ * τ.restrictScalars K) := by
      apply add_left_cancel (a := (Rep.ofAlgebraAutOnUnits K L).ρ σ (b 1))
      apply (sub_eq_iff_eq_add).mp
      simpa only [sub_add_eq_add_sub] using h
    exact h'.symm
  have hfiber (σ τ : Gal(L/K))
      (hστ : AlgEquiv.restrictNormalHom E σ = AlgEquiv.restrictNormalHom E τ) :
      b σ = b τ := by
    have hk : AlgEquiv.restrictNormalHom E (τ⁻¹ * σ) = 1 := by
      rw [map_mul, map_inv, hστ, inv_mul_cancel]
    obtain ⟨η, hη⟩ := exists_relativeAut_of_restrictNormal_eq_one K L E (τ⁻¹ * σ) hk
    calc
      b σ = b (τ * η.restrictScalars K) := by rw [hη, mul_inv_cancel_left]
      _ = b τ := hright τ η
  have hfixed (σ : Gal(L/K)) (τ : Gal(L/E)) :
      (Rep.ofAlgebraAutOnUnits K L).ρ (τ.restrictScalars K) (b σ) = b σ := by
    have h := hb (τ.restrictScalars K) σ
    rw [restrictNormal_restrictScalars, groupCohomology.cocycles₂_map_one_fst,
      ← h0, hn] at h
    have heq : b (τ.restrictScalars K * σ) = b σ := by
      apply hfiber
      rw [map_mul, restrictNormal_restrictScalars, one_mul]
    rw [heq] at h
    exact sub_eq_zero.mp (add_right_cancel (h.trans (zero_add (b 1)).symm))
  have ha : ∀ σ : Gal(L/K), ∃ a : Rep.ofAlgebraAutOnUnits K E,
      unitsInclusion K L E a = b σ := fun σ ↦
    exists_unitsInclusion_eq_of_fixed K L E (b σ) (hfixed σ)
  choose a ha using ha
  let surj : Function.Surjective (AlgEquiv.restrictNormalHom E : Gal(L/K) → Gal(E/K)) :=
    AlgEquiv.restrictNormalHom_surjective L (F := K) (K₁ := E)
  let s : Gal(E/K) → Gal(L/K) := Function.surjInv surj
  let aE : Gal(E/K) → Rep.ofAlgebraAutOnUnits K E := fun σ ↦ a (s σ)
  have hdesc (σ : Gal(L/K)) :
      unitsInclusion K L E (aE (AlgEquiv.restrictNormalHom E σ)) = b σ := by
    change unitsInclusion K L E (a (s (AlgEquiv.restrictNormalHom E σ))) = b σ
    rw [ha]
    exact hfiber _ σ (Function.surjInv_eq surj _)
  refine ⟨aE, ?_⟩
  funext στ
  obtain ⟨σ, hσ⟩ := surj στ.1
  obtain ⟨τ, hτ⟩ := surj στ.2
  apply unitsInclusion_injective K L E
  change unitsInclusion K L E
      ((Rep.ofAlgebraAutOnUnits K E).ρ στ.1 (aE στ.2) - aE (στ.1 * στ.2) + aE στ.1) =
    unitsInclusion K L E (c στ)
  rw [← hσ, ← hτ, map_add, map_sub, unitsInclusion_equivariant,
    hdesc, ← map_mul, hdesc, hdesc]
  simpa only [hσ, hτ, Prod.mk.eta] using hb σ τ

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Inflation sends an actual two-cocycle class to the class obtained by
restricting its arguments and including its field-unit values. -/
theorem finiteGaloisUnitsH2Inflation_H2π
    (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K E)) :
    (finiteGaloisUnitsH2Inflation K L E).hom
        (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K E) c) =
      groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
        (groupCohomology.mapCocycles₂ (AlgEquiv.restrictNormalHom E)
          (finiteGaloisUnitsInflationRepHom K L E) c) := by
  exact congrArg (fun f ↦ f c)
    (groupCohomology.H2π_comp_map (AlgEquiv.restrictNormalHom E)
      (finiteGaloisUnitsInflationRepHom K L E))

/-- Inflation on actual field-unit H² is injective in a finite Galois
tower. Noether–Hilbert90 corrects any upper primitive so that it descends
to a lower-field primitive. -/
theorem finiteGaloisUnitsH2Inflation_injective :
    Function.Injective (finiteGaloisUnitsH2Inflation K L E).hom := by
  have hzero : ∀ x : groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2,
      (finiteGaloisUnitsH2Inflation K L E).hom x = 0 → x = 0 := by
    intro x
    induction x using groupCohomology.H2_induction_on with
    | h c =>
      intro hx
      rw [finiteGaloisUnitsH2Inflation_H2π] at hx
      obtain ⟨b, hb⟩ := (groupCohomology.H2π_eq_zero_iff _).mp hx
      have hb' (σ τ : Gal(L/K)) :
          (Rep.ofAlgebraAutOnUnits K L).ρ σ (b τ) - b (σ * τ) + b σ =
            unitsInclusion K L E
              (c (AlgEquiv.restrictNormalHom E σ, AlgEquiv.restrictNormalHom E τ)) :=
        congrFun hb (σ, τ)
      obtain ⟨b', hb', hn⟩ := exists_primitive_constant_on_relativeAut K L E c b hb'
      obtain ⟨a, ha⟩ := exists_lower_primitive K L E c b' hb' hn
      exact (groupCohomology.H2π_eq_zero_iff c).mpr ⟨a, ha⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero (x - y)
  rw [map_sub, hxy, sub_self]

end
end ClassFieldTower.Cohomology
