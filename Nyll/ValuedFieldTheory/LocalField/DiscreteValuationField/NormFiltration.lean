/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Units

/-!
# Homomorphisms on subgroup filtrations

A group homomorphism carrying source levels into target levels induces maps
on subgroups, quotients, and subquotients. Valuations and norm scaling data
are not inputs to these group-theoretic constructions.
-/

@[expose] public section

open LocalFieldTheory.DiscreteValuationField

noncomputable section

universe u v

namespace MonoidHom

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (N : H →* G)
variable (UG : AntitoneSubgroupFiltration G) (UH : AntitoneSubgroupFiltration H)
variable (targetLevel : ℕ → ℕ)

/-- A compatibility hypothesis for a homomorphism and two filtrations. -/
abbrev MapsFiltrationLevels : Prop :=
  ∀ n {x : H}, x ∈ UH.level n →
    N x ∈ UG.level (targetLevel n)

/-- The norm map restricted to a filtration level. -/
def mapLevelOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ) :
    UH.level n →* UG.level (targetLevel n) where
  toFun x := ⟨N x.1, hN n x.2⟩
  map_one' := by
    apply Subtype.ext
    exact N.map_one
  map_mul' x y := by
    apply Subtype.ext
    exact N.map_mul x.1 y.1

/--
The defining evaluation formula for `mapLevelOfMapsFiltrationLevels` is
`(mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x : G) = N x.1`.
-/
@[simp] theorem mapLevelOfMapsFiltrationLevels_apply
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (x : UH.level n) :
    (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x : G) =
      N x.1 :=
  rfl

/-- The raw membership consequence of filtration compatibility. -/
theorem maps_level_of_mapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ) {x : H}
    (hx : x ∈ UH.level n) :
    N x ∈ UG.level (targetLevel n) :=
  hN n hx

/-- If the norm sends `U_H^n` into `U_G^(targetLevel n)`, then it also sends
it into any coarser target level. -/
theorem maps_level_of_mapsFiltrationLevels_of_le
    (hN : MapsFiltrationLevels N UG UH targetLevel) {n m : ℕ}
    (hm : m ≤ targetLevel n) {x : H}
    (hx : x ∈ UH.level n) :
    N x ∈ UG.level m :=
  UG.mem_of_mem_of_le hm (hN n hx)

/-- Filtration compatibility can be weakened by replacing the target level by
a coarser one. -/
theorem mapsFiltrationLevels_of_le {targetLevel' : ℕ → ℕ}
    (hN : MapsFiltrationLevels N UG UH targetLevel)
    (hle : ∀ n, targetLevel' n ≤ targetLevel n) :
    MapsFiltrationLevels N UG UH targetLevel' := by
  intro n x hx
  exact N.maps_level_of_mapsFiltrationLevels_of_le
    UG UH targetLevel hN (hle n) hx

/-- Surjectivity of the norm on a filtration level, stated without subtypes. -/
theorem mapLevelOfMapsFiltrationLevels_surjective_iff
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ) :
    Function.Surjective
      (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n) ↔
      ∀ y ∈ UG.level (targetLevel n),
        ∃ x ∈ UH.level n, N x = y := by
  constructor
  · intro hsurj y hy
    rcases hsurj ⟨y, hy⟩ with ⟨x, hx⟩
    exact ⟨x.1, x.2, by
      simpa [mapLevelOfMapsFiltrationLevels_apply] using congr_arg Subtype.val hx⟩
  · intro h y
    rcases h y.1 y.2 with ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/--
Characterizes `(mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n).range = ⊤` by the
equivalent condition `∀ y ∈ UG.level (targetLevel n), ∃ x ∈
UH.level n, N x = y`.
-/
theorem mapLevelOfMapsFiltrationLevels_range_eq_top_iff
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ) :
    (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n).range = ⊤ ↔
      ∀ y ∈ UG.level (targetLevel n),
        ∃ x ∈ UH.level n, N x = y := by
  rw [MonoidHom.range_eq_top,
    mapLevelOfMapsFiltrationLevels_surjective_iff N UG UH targetLevel hN n]

/-- A compatible norm descends to the quotient by a filtration level. -/
def quotientMapOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    H ⧸ UH.level n →*
      G ⧸ UG.level (targetLevel n) :=
  QuotientGroup.map (UH.level n)
    (UG.level (targetLevel n)) N (by
      intro x hx
      exact hN n hx)

/--
The defining evaluation formula for `quotientMapOfMapsFiltrationLevels` is
`quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n (QuotientGroup.mk x) =
QuotientGroup.mk (N x)`.
-/
@[simp] theorem quotientMapOfMapsFiltrationLevels_apply_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] (x : H) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk x) =
      QuotientGroup.mk (N x) :=
  rfl

/--
Establishes the identity `quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
(QuotientGroup.mk' (UH.level n) x) = QuotientGroup.mk' (UG.level
(targetLevel n)) (N x)`.
-/
@[simp] theorem quotientMapOfMapsFiltrationLevels_apply_mk'
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] (x : H) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk' (UH.level n) x) =
      QuotientGroup.mk' (UG.level (targetLevel n))
        (N x) :=
  rfl

/-- The preimage of the target filtration subgroup under the homomorphism. -/
def filtrationPreimageSubgroup (n : ℕ) : Subgroup H :=
  (UG.level (targetLevel n)).comap N

/--
Characterizes `x ∈ N.filtrationPreimageSubgroup UG targetLevel n` by the equivalent condition
`N x ∈ UG.level (targetLevel n)`.
-/
@[simp] theorem mem_filtrationPreimageSubgroup_iff (n : ℕ) (x : H) :
    x ∈ N.filtrationPreimageSubgroup UG targetLevel n ↔
      N x ∈ UG.level (targetLevel n) :=
  Iff.rfl

/--
Proves the bound `UH.level n ≤ N.filtrationPreimageSubgroup UG targetLevel n`.
-/
theorem level_le_filtrationPreimageSubgroup
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ) :
    UH.level n ≤
      N.filtrationPreimageSubgroup UG targetLevel n := by
  intro x hx
  exact hN n hx

/-- The subgroup appearing in `(N.filtrationPreimageSubgroup UG targetLevel n).Normal` is normal. -/
instance filtrationPreimageSubgroup_normal
    (n : ℕ) [(UG.level (targetLevel n)).Normal] :
    (N.filtrationPreimageSubgroup UG targetLevel n).Normal := by
  dsimp [filtrationPreimageSubgroup]
  infer_instance

/-- The class of the norm-preimage of the target filtration subgroup inside
the source quotient `H ⧸ U_H^n`. -/
def filtrationPreimageClassInQuotient (n : ℕ)
    [(UH.level n).Normal] :
    Subgroup (H ⧸ UH.level n) :=
  Subgroup.map (QuotientGroup.mk' (UH.level n))
    (N.filtrationPreimageSubgroup UG targetLevel n)

/--
The subgroup appearing in `(N.filtrationPreimageClassInQuotient UG UH targetLevel n).Normal` is
normal.
-/
instance filtrationPreimageClassInQuotient_normal
    (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    (N.filtrationPreimageClassInQuotient UG UH targetLevel n).Normal := by
  dsimp [filtrationPreimageClassInQuotient]
  infer_instance

/--
Characterizes `q ∈ N.filtrationPreimageClassInQuotient UG UH targetLevel n` by the equivalent
condition `∃ x : H, x ∈ N.filtrationPreimageSubgroup UG targetLevel n ∧ QuotientGroup.mk'
(UH.level n) x = q`.
-/
theorem mem_filtrationPreimageClassInQuotient_iff
    (n : ℕ) [(UH.level n).Normal]
    (q : H ⧸ UH.level n) :
    q ∈ N.filtrationPreimageClassInQuotient UG UH targetLevel n ↔
      ∃ x : H, x ∈ N.filtrationPreimageSubgroup UG targetLevel n ∧
        QuotientGroup.mk' (UH.level n) x = q :=
  Iff.rfl

/--
Characterizes `q ∈ N.filtrationPreimageClassInQuotient UG UH targetLevel n` by the equivalent
condition `∃ x : H, N x ∈ UG.level (targetLevel n) ∧ QuotientGroup.mk'
(UH.level n) x = q`.
-/
theorem mem_filtrationPreimageClassInQuotient_iff_exists_norm_mem
    (n : ℕ) [(UH.level n).Normal]
    (q : H ⧸ UH.level n) :
    q ∈ N.filtrationPreimageClassInQuotient UG UH targetLevel n ↔
      ∃ x : H, N x ∈ UG.level (targetLevel n) ∧
        QuotientGroup.mk' (UH.level n) x = q := by
  rw [N.mem_filtrationPreimageClassInQuotient_iff UG UH targetLevel n q]
  constructor
  · rintro ⟨x, hx, hxq⟩
    exact ⟨x, hx, hxq⟩
  · rintro ⟨x, hx, hxq⟩
    exact ⟨x, hx, hxq⟩

/--
Establishes the membership statement `QuotientGroup.mk' (UH.level n) x ∈
N.filtrationPreimageClassInQuotient UG UH targetLevel n`.
-/
theorem filtrationPreimageClassInQuotient_mk_mem
    {n : ℕ} [(UH.level n).Normal] {x : H}
    (hx : x ∈ N.filtrationPreimageSubgroup UG targetLevel n) :
    QuotientGroup.mk' (UH.level n) x ∈
      N.filtrationPreimageClassInQuotient UG UH targetLevel n :=
  Subgroup.mem_map_of_mem
    (QuotientGroup.mk' (UH.level n)) hx

/-- The kernel of the quotient norm map is the class of the preimage of the
target filtration subgroup in the source quotient. -/
theorem quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).ker =
      N.filtrationPreimageClassInQuotient UG UH targetLevel n := by
  exact QuotientGroup.ker_map (UH.level n)
    (UG.level (targetLevel n)) N (fun _ hx => hN n hx)

/--
Characterizes `q ∈ (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).ker` by the
equivalent condition `q ∈ N.filtrationPreimageClassInQuotient UG UH targetLevel n`.
-/
theorem mem_quotientMapOfMapsFiltrationLevels_ker_iff
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (q : H ⧸ UH.level n) :
    q ∈ (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).ker ↔
      q ∈ N.filtrationPreimageClassInQuotient UG UH targetLevel n := by
  rw [N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
    UG UH targetLevel hN n]

/-- Kernel criterion for arbitrary quotient elements under a filtration
quotient norm map. -/
theorem quotientMapOfMapsFiltrationLevels_eq_one_iff_mem_filtrationPreimageClass
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (q : H ⧸ UH.level n) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q = 1 ↔
      q ∈ N.filtrationPreimageClassInQuotient UG UH targetLevel n := by
  rw [← MonoidHom.mem_ker,
    N.mem_quotientMapOfMapsFiltrationLevels_ker_iff UG UH targetLevel hN n q]

/-- Kernel criterion for arbitrary quotient elements, expanded as a concrete
representative whose norm lies in the target filtration subgroup. -/
theorem quotientMapOfMapsFiltrationLevels_eq_one_iff_exists_norm_mem_repr
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (q : H ⧸ UH.level n) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q = 1 ↔
      ∃ x : H, N x ∈ UG.level (targetLevel n) ∧
        QuotientGroup.mk' (UH.level n) x = q := by
  rw [N.quotientMapOfMapsFiltrationLevels_eq_one_iff_mem_filtrationPreimageClass
      UG UH targetLevel hN n q,
    N.mem_filtrationPreimageClassInQuotient_iff_exists_norm_mem
      UG UH targetLevel n q]

/-- Equality criterion for arbitrary quotient elements under a filtration
quotient norm map, in right-quotient form. -/
theorem quotientMapOfMapsFiltrationLevels_eq_iff_div_mem_filtrationPreimageClass
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (q r : H ⧸ UH.level n) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q =
        quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n r ↔
      q / r ∈ N.filtrationPreimageClassInQuotient UG UH targetLevel n := by
  rw [← N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
      UG UH targetLevel hN n,
    MonoidHom.mem_ker, MonoidHom.map_div, div_eq_one]

/-- Equality criterion for arbitrary quotient elements, expanded as a concrete
representative of `q / r` whose norm lies in the target filtration subgroup. -/
theorem quotientMapOfMapsFiltrationLevels_eq_iff_exists_norm_mem_div_repr
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (q r : H ⧸ UH.level n) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q =
        quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n r ↔
      ∃ x : H, N x ∈ UG.level (targetLevel n) ∧
        QuotientGroup.mk' (UH.level n) x = q / r := by
  rw [N.quotientMapOfMapsFiltrationLevels_eq_iff_div_mem_filtrationPreimageClass
      UG UH targetLevel hN n q r,
    N.mem_filtrationPreimageClassInQuotient_iff_exists_norm_mem
      UG UH targetLevel n (q / r)]

/-- Equality criterion for arbitrary quotient elements under a filtration
quotient norm map, in left-quotient form. -/
theorem quotientMapOfMapsFiltrationLevels_eq_iff_inv_mul_mem_filtrationPreimageClass
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (q r : H ⧸ UH.level n) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q =
        quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n r ↔
      r⁻¹ * q ∈ N.filtrationPreimageClassInQuotient UG UH targetLevel n := by
  rw [N.quotientMapOfMapsFiltrationLevels_eq_iff_div_mem_filtrationPreimageClass
    UG UH targetLevel hN n q r]
  simpa [div_eq_mul_inv] using
    ((inferInstance :
      (N.filtrationPreimageClassInQuotient UG UH targetLevel n).Normal).mem_comm_iff
        (a := q) (b := r⁻¹))

/-- Equality criterion for arbitrary quotient elements, expanded as a concrete
representative of `r⁻¹ * q` whose norm lies in the target filtration subgroup. -/
theorem quotientMapOfMapsFiltrationLevels_eq_iff_exists_norm_mem_inv_mul_repr
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (q r : H ⧸ UH.level n) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q =
        quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n r ↔
      ∃ x : H, N x ∈ UG.level (targetLevel n) ∧
        QuotientGroup.mk' (UH.level n) x = r⁻¹ * q := by
  rw [N.quotientMapOfMapsFiltrationLevels_eq_iff_inv_mul_mem_filtrationPreimageClass
      UG UH targetLevel hN n q r,
    N.mem_filtrationPreimageClassInQuotient_iff_exists_norm_mem
      UG UH targetLevel n (r⁻¹ * q)]

/--
Characterizes `QuotientGroup.mk' (UH.level n) x ∈
N.filtrationPreimageClassInQuotient UG UH targetLevel n` by the equivalent condition `N x ∈
UG.level (targetLevel n)`.
-/
theorem quotientMapOfMapsFiltrationLevels_mk_mem_filtrationPreimageClass_iff
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] (x : H) :
    QuotientGroup.mk' (UH.level n) x ∈
        N.filtrationPreimageClassInQuotient UG UH targetLevel n ↔
      N x ∈ UG.level (targetLevel n) := by
  rw [← N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
    UG UH targetLevel hN n]
  change
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk' (UH.level n) x) = 1 ↔
      N x ∈ UG.level (targetLevel n)
  rw [N.quotientMapOfMapsFiltrationLevels_apply_mk' UG UH targetLevel hN n x]
  exact QuotientGroup.eq_one_iff (N x)

/-- Injectivity of the filtration quotient norm map is equivalent to the
filtration-preimage kernel class being trivial. -/
theorem quotientMapOfMapsFiltrationLevels_injective_iff_filtrationPreimageClass_eq_bot
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    Function.Injective
        (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) ↔
      N.filtrationPreimageClassInQuotient UG UH targetLevel n = ⊥ := by
  rw [← N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
    UG UH targetLevel hN n]
  exact (MonoidHom.ker_eq_bot_iff
    (f := quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)).symm

/-- Concrete representative criterion for injectivity of the filtration
quotient norm map.  An element whose norm lands in the target filtration must
already be trivial modulo the source filtration. -/
theorem quotientMapOfMapsFiltrationLevels_injective_iff_forall_norm_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    Function.Injective
        (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) ↔
      ∀ x : H, N x ∈ UG.level (targetLevel n) →
        QuotientGroup.mk' (UH.level n) x = 1 := by
  rw [N.quotientMapOfMapsFiltrationLevels_injective_iff_filtrationPreimageClass_eq_bot
    UG UH targetLevel hN n]
  constructor
  · intro hbot x hx
    have hxmem :
        QuotientGroup.mk' (UH.level n) x ∈
          N.filtrationPreimageClassInQuotient UG UH targetLevel n := by
      exact (N.quotientMapOfMapsFiltrationLevels_mk_mem_filtrationPreimageClass_iff
        UG UH targetLevel hN n x).2 hx
    have hxbot :
        QuotientGroup.mk' (UH.level n) x ∈
          (⊥ : Subgroup (H ⧸ UH.level n)) := by
      simpa [hbot] using hxmem
    simpa [Subgroup.mem_bot] using hxbot
  · intro h
    apply le_antisymm
    · intro q hq
      rw [Subgroup.mem_bot]
      rcases
        (N.mem_filtrationPreimageClassInQuotient_iff_exists_norm_mem
          UG UH targetLevel n q).1 hq with
        ⟨x, hx, hxq⟩
      rw [← hxq]
      exact h x hx
    · intro q hq
      rw [Subgroup.mem_bot] at hq
      subst q
      exact Subgroup.one_mem _

/-- A practical injectivity criterion for filtration quotient norm maps. -/
theorem quotientMapOfMapsFiltrationLevels_injective_of_forall_norm_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hKer : ∀ x : H,
      N x ∈ UG.level (targetLevel n) →
        QuotientGroup.mk' (UH.level n) x = 1) :
    Function.Injective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) :=
  (N.quotientMapOfMapsFiltrationLevels_injective_iff_forall_norm_mem
    UG UH targetLevel hN n).2 hKer

/-- One criterion in the double quotient by the filtration-preimage kernel
class. -/
theorem quotientModuloFiltrationPreimageClass_mk_eq_one_iff
    (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (q : H ⧸ UH.level n) :
    QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q = 1 ↔
      q ∈ N.filtrationPreimageClassInQuotient UG UH targetLevel n := by
  exact QuotientGroup.eq_one_iff _

/--
Characterizes `QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
(QuotientGroup.mk' (UH.level n) x) = 1` by the equivalent condition `N x ∈
UG.level (targetLevel n)`.
-/
theorem quotientModuloFiltrationPreimageClass_mk_mk_eq_one_iff
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] (x : H) :
    QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
        (QuotientGroup.mk' (UH.level n) x) = 1 ↔
      N x ∈ UG.level (targetLevel n) := by
  rw [N.quotientModuloFiltrationPreimageClass_mk_eq_one_iff UG UH targetLevel n,
    N.quotientMapOfMapsFiltrationLevels_mk_mem_filtrationPreimageClass_iff
      UG UH targetLevel hN n x]

/-- Equality criterion in the double quotient by the filtration-preimage kernel
class. -/
theorem quotientModuloFiltrationPreimageClass_mk_eq_iff_div_mem
    (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (q r : H ⧸ UH.level n) :
    QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n) r ↔
      q / r ∈ N.filtrationPreimageClassInQuotient UG UH targetLevel n := by
  simpa [QuotientGroup.mk'_apply] using
    (QuotientGroup.eq_iff_div_mem
      (N := N.filtrationPreimageClassInQuotient UG UH targetLevel n)
      (x := q) (y := r))

/--
Characterizes `QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
(QuotientGroup.mk' (UH.level n) x) = QuotientGroup.mk'
(N.filtrationPreimageClassInQuotient UG UH targetLevel n) (QuotientGroup.mk'
(UH.level n) y)` by the equivalent condition `N (x / y) ∈
UG.level (targetLevel n)`.
-/
theorem quotientModuloFiltrationPreimageClass_mk_mk_eq_iff
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] (x y : H) :
    QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
        (QuotientGroup.mk' (UH.level n) x) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
        (QuotientGroup.mk' (UH.level n) y) ↔
      N (x / y) ∈ UG.level (targetLevel n) := by
  rw [N.quotientModuloFiltrationPreimageClass_mk_eq_iff_div_mem
    UG UH targetLevel n]
  rw [← (QuotientGroup.mk' (UH.level n)).map_div x y,
    N.quotientMapOfMapsFiltrationLevels_mk_mem_filtrationPreimageClass_iff
      UG UH targetLevel hN n (x / y)]

/-- Left-quotient form of
`quotientModuloFiltrationPreimageClass_mk_mk_eq_iff`. -/
theorem quotientModuloFiltrationPreimageClass_mk_mk_eq_iff_inv_mul
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] (x y : H) :
    QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
        (QuotientGroup.mk' (UH.level n) x) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
        (QuotientGroup.mk' (UH.level n) y) ↔
      N (y⁻¹ * x) ∈ UG.level (targetLevel n) := by
  rw [N.quotientModuloFiltrationPreimageClass_mk_mk_eq_iff
    UG UH targetLevel hN n x y,
    N.map_div,
    UG.level_div_mem_iff_inv_mul_mem (targetLevel n)
      (N x) (N y)]
  rw [N.map_mul, N.map_inv]

/-- First-isomorphism form of the filtration quotient norm map, with codomain
the actual range when no surjectivity hypothesis is available. -/
noncomputable def quotientModuloFiltrationPreimageClassEquivRange
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    (H ⧸ UH.level n) ⧸
        N.filtrationPreimageClassInQuotient UG UH targetLevel n ≃*
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
        UG UH targetLevel hN n).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n))

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN n
(QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) =
(quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (q : H ⧸ UH.level n) :
    N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) =
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q :=
  rfl

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN n
(QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) (QuotientGroup.mk'
(UH.level n) x)) = (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN
n).rangeRestrict (QuotientGroup.mk' (UH.level n) x)`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_mk_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] (x : H) :
    N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
          (QuotientGroup.mk' (UH.level n) x)) =
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict
        (QuotientGroup.mk' (UH.level n) x) :=
  rfl

/--
Establishes the identity `((N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) :
(quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) : G ⧸ UG.level
(targetLevel n)) = quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q`.
-/
@[simp] theorem coe_quotientModuloFiltrationPreimageClassEquivRange_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (q : H ⧸ UH.level n) :
    ((N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) :
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) :
        G ⧸ UG.level (targetLevel n)) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q := by
  rw [N.quotientModuloFiltrationPreimageClassEquivRange_mk
    UG UH targetLevel hN n q]
  rfl

/--
Establishes the identity `((N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) (QuotientGroup.mk'
(UH.level n) x)) : (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN
n).range) : G ⧸ UG.level (targetLevel n)) = QuotientGroup.mk'
(UG.level (targetLevel n)) (N x)`.
-/
@[simp] theorem coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] (x : H) :
    ((N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
          (QuotientGroup.mk' (UH.level n) x)) :
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) :
        G ⧸ UG.level (targetLevel n)) =
      QuotientGroup.mk' (UG.level (targetLevel n))
        (N x) := by
  rw [N.coe_quotientModuloFiltrationPreimageClassEquivRange_mk
    UG UH targetLevel hN n
    (QuotientGroup.mk' (UH.level n) x),
    N.quotientMapOfMapsFiltrationLevels_apply_mk' UG UH targetLevel hN n x]

/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n).symm ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q) =
QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (q : H ⧸ UH.level n) :
    (N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n).symm
        ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q := by
  apply (N.quotientModuloFiltrationPreimageClassEquivRange
    UG UH targetLevel hN n).injective
  calc
    N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        ((N.quotientModuloFiltrationPreimageClassEquivRange
          UG UH targetLevel hN n).symm
          ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q)) =
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q := by
        exact
          (N.quotientModuloFiltrationPreimageClassEquivRange
            UG UH targetLevel hN n).apply_symm_apply _
    _ =
      N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) := by
        rw [N.quotientModuloFiltrationPreimageClassEquivRange_mk
          UG UH targetLevel hN n q]

/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n).symm ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict
(QuotientGroup.mk' (UH.level n) x)) = QuotientGroup.mk'
(N.filtrationPreimageClassInQuotient UG UH targetLevel n) (QuotientGroup.mk'
(UH.level n) x)`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] (x : H) :
    (N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n).symm
        ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict
          (QuotientGroup.mk' (UH.level n) x)) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
        (QuotientGroup.mk' (UH.level n) x) := by
  rw [N.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict
    UG UH targetLevel hN n]

/-- First-isomorphism form of a surjective filtration quotient norm map. -/
noncomputable def quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)) :
    (H ⧸ UH.level n) ⧸
        N.filtrationPreimageClassInQuotient UG UH targetLevel n ≃*
      G ⧸ UG.level (targetLevel n) :=
  (QuotientGroup.quotientMulEquivOfEq
      (N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
        UG UH targetLevel hN n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (φ := quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) hSurj)

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective UG UH
targetLevel hN n hSurj (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel
n) q) = quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n))
    (q : H ⧸ UH.level n) :
    N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q := by
  change QuotientGroup.kerLift
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)
      ((QuotientGroup.quotientMulEquivOfEq
        (N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
          UG UH targetLevel hN n).symm) (QuotientGroup.mk q)) =
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk
    (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) q

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective UG UH
targetLevel hN n hSurj (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel
n) (QuotientGroup.mk' (UH.level n) x)) = QuotientGroup.mk'
(UG.level (targetLevel n)) (N x)`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_mk_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)) (x : H) :
    N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
          (QuotientGroup.mk' (UH.level n) x)) =
      QuotientGroup.mk' (UG.level (targetLevel n))
        (N x) := by
  rw [N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_mk
    UG UH targetLevel hN n hSurj,
    N.quotientMapOfMapsFiltrationLevels_apply_mk' UG UH targetLevel hN n x]

/-- Under quotient-level surjectivity, the target-valued first-isomorphism
equivalence is the range-valued equivalence followed by the range inclusion. -/
theorem coe_quotientModuloFiltrationPreimageClassEquivRange_eq_targetOfSurjective
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n))
    (z : (H ⧸ UH.level n) ⧸
        N.filtrationPreimageClassInQuotient UG UH targetLevel n) :
    ((N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n z :
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) :
        G ⧸ UG.level (targetLevel n)) =
      N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj z := by
  refine QuotientGroup.induction_on z ?_
  intro q
  change
    ((N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) :
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) :
        G ⧸ UG.level (targetLevel n)) =
      N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q)
  rw [N.coe_quotientModuloFiltrationPreimageClassEquivRange_mk
    UG UH targetLevel hN n q,
    N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_mk
      UG UH targetLevel hN n hSurj q]

/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective UG UH
targetLevel hN n hSurj).symm (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q) =
QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_symm_map
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n))
    (q : H ⧸ UH.level n) :
    (N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj).symm
        (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q := by
  apply (N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
    UG UH targetLevel hN n hSurj).injective
  calc
    N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj
        ((N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
          UG UH targetLevel hN n hSurj).symm
          (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q)) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q := by
        exact
          (N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
            UG UH targetLevel hN n hSurj).apply_symm_apply _
    _ =
      N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) := by
        rw [N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_mk
          UG UH targetLevel hN n hSurj q]

/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective UG UH
targetLevel hN n hSurj).symm (QuotientGroup.mk' (UG.level (targetLevel n))
(N x)) = QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
(QuotientGroup.mk' (UH.level n) x)`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_symm_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)) (x : H) :
    (N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj).symm
        (QuotientGroup.mk' (UG.level (targetLevel n))
          (N x)) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
        (QuotientGroup.mk' (UH.level n) x) := by
  rw [← N.quotientMapOfMapsFiltrationLevels_apply_mk'
    UG UH targetLevel hN n x,
    N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_symm_map
      UG UH targetLevel hN n hSurj]

/-- Kernel criterion for the quotient map induced by filtration-compatible
norms. -/
theorem quotientMapOfMapsFiltrationLevels_mk_eq_one_iff
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] (x : H) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk x) = 1 ↔
      N x ∈ UG.level (targetLevel n) := by
  rw [quotientMapOfMapsFiltrationLevels_apply_mk]
  exact QuotientGroup.eq_one_iff (N x)

/-- Equality criterion for the quotient map induced by filtration-compatible
norms. -/
theorem quotientMapOfMapsFiltrationLevels_mk_eq_iff
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] (x y : H) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk x) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk y) ↔
      N (x / y) ∈ UG.level (targetLevel n) := by
  rw [quotientMapOfMapsFiltrationLevels_apply_mk,
    quotientMapOfMapsFiltrationLevels_apply_mk]
  simpa [N.map_div] using
    (QuotientGroup.eq_iff_div_mem
      (N := UG.level (targetLevel n))
      (x := N x) (y := N y))

/-- Left-quotient equality criterion for the quotient map induced by
filtration-compatible norms. -/
theorem quotientMapOfMapsFiltrationLevels_mk_eq_iff_inv_mul
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] (x y : H) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk x) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk y) ↔
      N (y⁻¹ * x) ∈ UG.level (targetLevel n) := by
  rw [quotientMapOfMapsFiltrationLevels_mk_eq_iff N UG UH targetLevel hN n x y,
    N.map_div,
    UG.level_div_mem_iff_inv_mul_mem (targetLevel n)
      (N x) (N y)]
  rw [N.map_mul, N.map_inv]

/-- Quotient-level surjectivity is equivalent to lifting every target element
up to the target filtration subgroup. -/
theorem quotientMapOfMapsFiltrationLevels_surjective_iff_exists_div_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) ↔
      ∀ g : G, ∃ x : H,
        N x / g ∈ UG.level (targetLevel n) := by
  constructor
  · intro hsurj g
    rcases hsurj (QuotientGroup.mk g) with ⟨q, hq⟩
    revert hq
    refine QuotientGroup.induction_on q ?_
    intro x hq
    rw [quotientMapOfMapsFiltrationLevels_apply_mk] at hq
    exact ⟨x,
      (QuotientGroup.eq_iff_div_mem
        (N := UG.level (targetLevel n))
        (x := N x) (y := g)).1 hq⟩
  · intro h gq
    refine QuotientGroup.induction_on gq ?_
    intro g
    rcases h g with ⟨x, hx⟩
    refine ⟨QuotientGroup.mk x, ?_⟩
    rw [quotientMapOfMapsFiltrationLevels_apply_mk]
    exact
      (QuotientGroup.eq_iff_div_mem
        (N := UG.level (targetLevel n))
        (x := N x) (y := g)).2 hx

/-- A practical quotient-surjectivity criterion: it is enough to lift every
target element modulo the target filtration subgroup. -/
theorem quotientMapOfMapsFiltrationLevels_surjective_of_exists_div_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hLift : ∀ g : G, ∃ x : H,
      N x / g ∈ UG.level (targetLevel n)) :
    Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) :=
  (N.quotientMapOfMapsFiltrationLevels_surjective_iff_exists_div_mem
    UG UH targetLevel hN n).2 hLift

/-- Quotient-map range is top exactly when every target element is a norm
modulo the target filtration subgroup. -/
theorem quotientMapOfMapsFiltrationLevels_range_eq_top_iff_exists_div_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range = ⊤ ↔
      ∀ g : G, ∃ x : H,
        N x / g ∈ UG.level (targetLevel n) := by
  rw [MonoidHom.range_eq_top,
    N.quotientMapOfMapsFiltrationLevels_surjective_iff_exists_div_mem
      UG UH targetLevel hN n]

/-- Left-quotient form of quotient-level surjectivity. -/
theorem quotientMapOfMapsFiltrationLevels_surjective_iff_exists_inv_mul_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) ↔
      ∀ g : G, ∃ x : H,
        g⁻¹ * N x ∈ UG.level (targetLevel n) := by
  rw [N.quotientMapOfMapsFiltrationLevels_surjective_iff_exists_div_mem
    UG UH targetLevel hN n]
  constructor
  · intro h g
    rcases h g with ⟨x, hx⟩
    exact ⟨x,
      (UG.level_div_mem_iff_inv_mul_mem (targetLevel n)
        (N x) g).1 hx⟩
  · intro h g
    rcases h g with ⟨x, hx⟩
    exact ⟨x,
      (UG.level_inv_mul_mem_iff_div_mem (targetLevel n)
        (N x) g).1 hx⟩

/-- A practical left-quotient criterion for quotient-level surjectivity. -/
theorem quotientMapOfMapsFiltrationLevels_surjective_of_exists_inv_mul_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hLift : ∀ g : G, ∃ x : H,
      g⁻¹ * N x ∈ UG.level (targetLevel n)) :
    Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) :=
  (N.quotientMapOfMapsFiltrationLevels_surjective_iff_exists_inv_mul_mem
    UG UH targetLevel hN n).2 hLift

/-- Coarsening the target filtration level commutes with the induced quotient
norm map. -/
theorem quotientMapOfMapsFiltrationLevels_comp_targetLevelChange
    {targetLevel' : ℕ → ℕ}
    (hN : MapsFiltrationLevels N UG UH targetLevel)
    (hle : ∀ n, targetLevel' n ≤ targetLevel n) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    [(UG.level (targetLevel' n)).Normal] :
    (UG.quotient_level_mapOfLe (hle n)).comp
        (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel'
        (N.mapsFiltrationLevels_of_le UG UH targetLevel hN hle) n := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  simp [quotientMapOfMapsFiltrationLevels_apply_mk]

/-- The quotient norm maps are natural in the source and target filtration
levels. -/
theorem quotientMapOfMapsFiltrationLevels_sourceLevelChange
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UH.level m).Normal]
    [(UG.level (targetLevel n)).Normal]
    [(UG.level (targetLevel m)).Normal] :
    (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN m).comp
        (UH.quotient_level_mapOfLe hmn) =
      (UG.quotient_level_mapOfLe htarget).comp
        (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  simp [quotientMapOfMapsFiltrationLevels_apply_mk]

/-- Surjectivity of a quotient norm map descends when the target filtration
level is coarsened. -/
theorem quotientMapOfMapsFiltrationLevels_surjective_of_targetLevelChange
    {targetLevel' : ℕ → ℕ}
    (hN : MapsFiltrationLevels N UG UH targetLevel)
    (hle : ∀ n, targetLevel' n ≤ targetLevel n) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    [(UG.level (targetLevel' n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)) :
    Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel'
        (N.mapsFiltrationLevels_of_le UG UH targetLevel hN hle) n) := by
  intro z
  rcases UG.quotient_level_mapOfLe_surjective (hle n) z with
    ⟨y, hy⟩
  rcases hSurj y with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [← N.quotientMapOfMapsFiltrationLevels_comp_targetLevelChange
    UG UH targetLevel hN hle n]
  simp [MonoidHom.comp_apply, hx, hy]

/-- Range-top form of
`quotientMapOfMapsFiltrationLevels_surjective_of_targetLevelChange`. -/
theorem quotientMapOfMapsFiltrationLevels_range_eq_top_of_targetLevelChange
    {targetLevel' : ℕ → ℕ}
    (hN : MapsFiltrationLevels N UG UH targetLevel)
    (hle : ∀ n, targetLevel' n ≤ targetLevel n) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    [(UG.level (targetLevel' n)).Normal]
    (hRange :
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range =
        ⊤) :
    (quotientMapOfMapsFiltrationLevels N UG UH targetLevel'
      (N.mapsFiltrationLevels_of_le UG UH targetLevel hN hle) n).range =
        ⊤ := by
  rw [MonoidHom.range_eq_top] at hRange ⊢
  exact N.quotientMapOfMapsFiltrationLevels_surjective_of_targetLevelChange
    UG UH targetLevel hN hle n hRange

/-- Surjectivity of quotient norm maps descends along compatible source and
target filtration level changes. -/
theorem quotientMapOfMapsFiltrationLevels_surjective_of_sourceLevelChange
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UH.level m).Normal]
    [(UG.level (targetLevel n)).Normal]
    [(UG.level (targetLevel m)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)) :
    Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN m) := by
  intro z
  rcases UG.quotient_level_mapOfLe_surjective htarget z with
    ⟨y, hy⟩
  rcases hSurj y with ⟨x, hx⟩
  refine ⟨UH.quotient_level_mapOfLe hmn x, ?_⟩
  change
    ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN m).comp
        (UH.quotient_level_mapOfLe hmn)) x = z
  rw [N.quotientMapOfMapsFiltrationLevels_sourceLevelChange
    UG UH targetLevel hN hmn htarget]
  simp [MonoidHom.comp_apply, hx, hy]

/-- A filtration-compatible norm induces maps on principal-unit subquotients:
`U_H^m/U_H^n → U_G^(targetLevel m)/U_G^(targetLevel n)`. -/
def principalUnitSubquotientMapOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (_hmn : m ≤ n) (_htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    UH.principalUnitSubquotient m n →*
      UG.principalUnitSubquotient (targetLevel m) (targetLevel n) :=
  UH.principalUnitSubquotientLift m n
    ((UG.principalUnitSubquotientMk (targetLevel m) (targetLevel n)).comp
      (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m))
    (by
      intro x hx
      change UG.principalUnitSubquotientMk (targetLevel m) (targetLevel n)
          (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x) = 1
      rw [UG.principalUnitSubquotient_mk_eq_one_iff]
      exact hN n hx)

/--
The defining evaluation formula for `principalUnitSubquotientMapOfMapsFiltrationLevels` is
`N.principalUnitSubquotientMapOfMapsFiltrationLevels UG UH targetLevel hN hmn htarget
(UH.principalUnitSubquotientMk m n x) = UG.principalUnitSubquotientMk (targetLevel m) (targetLevel
n) (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x)`.
-/
@[simp] theorem principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (x : UH.level m) :
    N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget
        (UH.principalUnitSubquotientMk m n x) =
      UG.principalUnitSubquotientMk (targetLevel m) (targetLevel n)
        (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x) :=
  rfl

/-- The subquotient norm map agrees with the ambient quotient norm map under
the canonical embeddings of subquotients as classes in ambient quotients. -/
@[simp] theorem coe_principalUnitSubquotientEquivClassInQuotient_map
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (z : UH.principalUnitSubquotient m n) :
    ((UG.principalUnitSubquotientEquivClassInQuotientOfLe htarget
        (N.principalUnitSubquotientMapOfMapsFiltrationLevels
          UG UH targetLevel hN hmn htarget z) :
      UG.levelClassInQuotient (targetLevel m)
        (targetLevel n)) :
      G ⧸ UG.level (targetLevel n)) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        ((UH.principalUnitSubquotientEquivClassInQuotientOfLe hmn z :
          UH.levelClassInQuotient m n) :
          H ⧸ UH.level n) := by
  refine
    AntitoneSubgroupFiltration.principalUnitSubquotient.inductionOn
      UH m n
        (motive := fun z' ↦
          ((UG.principalUnitSubquotientEquivClassInQuotientOfLe htarget
              (N.principalUnitSubquotientMapOfMapsFiltrationLevels
                UG UH targetLevel hN hmn htarget z') :
            UG.levelClassInQuotient (targetLevel m)
              (targetLevel n)) :
            G ⧸ UG.level (targetLevel n)) =
          quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
            ((UH.principalUnitSubquotientEquivClassInQuotientOfLe hmn z' :
              UH.levelClassInQuotient m n) :
              H ⧸ UH.level n)) z ?_
  intro x
  rw [principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk,
    UG.coe_principalUnitSubquotientEquivClassInQuotientOfLe_mk,
    UH.coe_principalUnitSubquotientEquivClassInQuotientOfLe_mk,
    quotientMapOfMapsFiltrationLevels_apply_mk', mapLevelOfMapsFiltrationLevels_apply]

/-- The graded-piece form of
`principalUnitSubquotientMapOfMapsFiltrationLevels`. -/
def principalUnitGradedPieceMapOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.level (n + 1)).Normal]
    [(UG.level (targetLevel (n + 1))).Normal] :
    UH.principalUnitGradedPiece n →*
      UG.principalUnitSubquotient (targetLevel n) (targetLevel (n + 1)) :=
  (N.principalUnitSubquotientMapOfMapsFiltrationLevels
    UG UH targetLevel hN (Nat.le_succ n) htarget).comp
      (UH.principalUnitGradedPieceEquivSubquotient n).toMonoidHom

/--
The defining evaluation formula for `principalUnitGradedPieceMapOfMapsFiltrationLevels` is
`N.principalUnitGradedPieceMapOfMapsFiltrationLevels UG UH targetLevel hN n htarget
(UH.principalUnitGradedPieceMk n x) = UG.principalUnitSubquotientMk (targetLevel n) (targetLevel
(n + 1)) (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x)`.
-/
@[simp] theorem principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.level (n + 1)).Normal]
    [(UG.level (targetLevel (n + 1))).Normal]
    (x : UH.level n) :
    N.principalUnitGradedPieceMapOfMapsFiltrationLevels
        UG UH targetLevel hN n htarget
        (UH.principalUnitGradedPieceMk n x) =
      UG.principalUnitSubquotientMk (targetLevel n) (targetLevel (n + 1))
        (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x) :=
  rfl

/-- Kernel criterion on representatives for the principal-unit subquotient
map induced by a filtration-compatible norm. -/
theorem principalUnitSubquotientMapOfMapsFiltrationLevels_mk_eq_one_iff
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (x : UH.level m) :
    N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget
        (UH.principalUnitSubquotientMk m n x) = 1 ↔
      N (x : H) ∈ UG.level (targetLevel n) := by
  rw [N.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk
    UG UH targetLevel hN hmn htarget x]
  simpa [mapLevelOfMapsFiltrationLevels_apply] using
    UG.principalUnitSubquotient_mk_eq_one_iff
      (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x)

/-- Equality criterion on representatives for the principal-unit subquotient
map induced by a filtration-compatible norm, in right-quotient form. -/
theorem principalUnitSubquotientMapOfMapsFiltrationLevels_mk_eq_iff_div_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (x y : UH.level m) :
    N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget
        (UH.principalUnitSubquotientMk m n x) =
      N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget
        (UH.principalUnitSubquotientMk m n y) ↔
      N ((x / y : UH.level m) : H) ∈
        UG.level (targetLevel n) := by
  rw [N.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk
      UG UH targetLevel hN hmn htarget x,
    N.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk
      UG UH targetLevel hN hmn htarget y]
  simpa [mapLevelOfMapsFiltrationLevels_apply, N.map_div] using
    UG.principalUnitSubquotient_mk_eq_iff_div_mem
      (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x)
      (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m y)

/-- Equality criterion on representatives for the principal-unit subquotient
map induced by a filtration-compatible norm, in left-quotient form. -/
theorem principalUnitSubquotientMapOfMapsFiltrationLevels_mk_eq_iff_inv_mul_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (x y : UH.level m) :
    N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget
        (UH.principalUnitSubquotientMk m n x) =
      N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget
        (UH.principalUnitSubquotientMk m n y) ↔
      N ((y⁻¹ * x : UH.level m) : H) ∈
        UG.level (targetLevel n) := by
  rw [N.principalUnitSubquotientMapOfMapsFiltrationLevels_mk_eq_iff_div_mem
      UG UH targetLevel hN hmn htarget x y]
  simpa [N.map_div, N.map_mul, N.map_inv] using
    UG.level_div_mem_iff_inv_mul_mem (targetLevel n)
      (N (x : H)) (N (y : H))

/-- Surjectivity of the principal-unit subquotient norm map is equivalent to
lifting every target representative modulo the next target level. -/
theorem principalUnitSubquotientMapOfMapsFiltrationLevels_surjective_iff_exists_div_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    Function.Surjective
        (N.principalUnitSubquotientMapOfMapsFiltrationLevels
          UG UH targetLevel hN hmn htarget) ↔
      ∀ y : UG.level (targetLevel m),
        ∃ x : UH.level m,
          N (x : H) / (y : G) ∈
            UG.level (targetLevel n) := by
  constructor
  · intro hsurj y
    rcases hsurj
        (UG.principalUnitSubquotientMk (targetLevel m) (targetLevel n) y) with
      ⟨z, hz⟩
    revert hz
    refine
      AntitoneSubgroupFiltration.principalUnitSubquotient.inductionOn
        UH m n
          (motive := fun z' ↦
            N.principalUnitSubquotientMapOfMapsFiltrationLevels
                UG UH targetLevel hN hmn htarget z' =
              UG.principalUnitSubquotientMk
                (targetLevel m) (targetLevel n) y →
            ∃ x : UH.level m,
              N (x : H) / (y : G) ∈
                UG.level (targetLevel n)) z ?_
    intro x hx
    rw [N.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk
      UG UH targetLevel hN hmn htarget x] at hx
    exact ⟨x, by
      simpa [mapLevelOfMapsFiltrationLevels_apply] using
        (UG.principalUnitSubquotient_mk_eq_iff_div_mem
          (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x) y).1 hx⟩
  · intro h q
    refine
      AntitoneSubgroupFiltration.principalUnitSubquotient.inductionOn
        UG (targetLevel m) (targetLevel n)
          (motive := fun q' ↦
            ∃ a,
              N.principalUnitSubquotientMapOfMapsFiltrationLevels
                UG UH targetLevel hN hmn htarget a = q') q ?_
    intro y
    rcases h y with ⟨x, hx⟩
    refine ⟨UH.principalUnitSubquotientMk m n x, ?_⟩
    rw [N.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk
      UG UH targetLevel hN hmn htarget x]
    exact
      (UG.principalUnitSubquotient_mk_eq_iff_div_mem
        (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x) y).2
        (by simpa [mapLevelOfMapsFiltrationLevels_apply] using hx)

/-- A practical surjectivity criterion for principal-unit subquotient norm
maps. -/
theorem principalUnitSubquotientMapOfMapsFiltrationLevels_surjective_of_exists_div_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hLift : ∀ y : UG.level (targetLevel m),
      ∃ x : UH.level m,
        N (x : H) / (y : G) ∈
          UG.level (targetLevel n)) :
    Function.Surjective
      (N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget) :=
  (N.principalUnitSubquotientMapOfMapsFiltrationLevels_surjective_iff_exists_div_mem
    UG UH targetLevel hN hmn htarget).2 hLift

/-- Range-top form of the principal-unit subquotient norm map surjectivity
criterion. -/
theorem principalUnitSubquotientMapOfMapsFiltrationLevels_range_eq_top_iff_exists_div_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    (N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget).range = ⊤ ↔
      ∀ y : UG.level (targetLevel m),
        ∃ x : UH.level m,
          N (x : H) / (y : G) ∈
            UG.level (targetLevel n) := by
  rw [MonoidHom.range_eq_top,
    N.principalUnitSubquotientMapOfMapsFiltrationLevels_surjective_iff_exists_div_mem
      UG UH targetLevel hN hmn htarget]

/-- Range-top form of
`principalUnitSubquotientMapOfMapsFiltrationLevels_surjective_of_exists_div_mem`. -/
theorem principalUnitSubquotientMapOfMapsFiltrationLevels_range_eq_top_of_exists_div_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hLift : ∀ y : UG.level (targetLevel m),
      ∃ x : UH.level m,
        N (x : H) / (y : G) ∈
          UG.level (targetLevel n)) :
    (N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget).range = ⊤ :=
  (N.principalUnitSubquotientMapOfMapsFiltrationLevels_range_eq_top_iff_exists_div_mem
    UG UH targetLevel hN hmn htarget).2 hLift

/-- Left-quotient form of principal-unit subquotient norm map surjectivity. -/
theorem principalUnitSubquotientMapOfMapsFiltrationLevels_surjective_iff_exists_inv_mul_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    Function.Surjective
        (N.principalUnitSubquotientMapOfMapsFiltrationLevels
          UG UH targetLevel hN hmn htarget) ↔
      ∀ y : UG.level (targetLevel m),
        ∃ x : UH.level m,
          (y : G)⁻¹ * N (x : H) ∈
            UG.level (targetLevel n) := by
  rw [N.principalUnitSubquotientMapOfMapsFiltrationLevels_surjective_iff_exists_div_mem
    UG UH targetLevel hN hmn htarget]
  constructor
  · intro h y
    rcases h y with ⟨x, hx⟩
    exact ⟨x,
      (UG.level_div_mem_iff_inv_mul_mem (targetLevel n)
        (N (x : H)) (y : G)).1 hx⟩
  · intro h y
    rcases h y with ⟨x, hx⟩
    exact ⟨x,
      (UG.level_inv_mul_mem_iff_div_mem (targetLevel n)
        (N (x : H)) (y : G)).1 hx⟩

/-- A practical left-quotient surjectivity criterion for principal-unit
subquotient norm maps. -/
theorem principalUnitSubquotientMapOfMapsFiltrationLevels_surjective_of_exists_inv_mul_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hLift : ∀ y : UG.level (targetLevel m),
      ∃ x : UH.level m,
        (y : G)⁻¹ * N (x : H) ∈
          UG.level (targetLevel n)) :
    Function.Surjective
      (N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget) :=
  (N.principalUnitSubquotientMapOfMapsFiltrationLevels_surjective_iff_exists_inv_mul_mem
    UG UH targetLevel hN hmn htarget).2 hLift

/-- Range-top left-quotient criterion for principal-unit subquotient norm maps. -/
theorem principalUnitSubquotientMapOfMapsFiltrationLevels_range_eq_top_iff_exists_inv_mul_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal] :
    (N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget).range = ⊤ ↔
      ∀ y : UG.level (targetLevel m),
        ∃ x : UH.level m,
          (y : G)⁻¹ * N (x : H) ∈
            UG.level (targetLevel n) := by
  rw [MonoidHom.range_eq_top,
    N.principalUnitSubquotientMapOfMapsFiltrationLevels_surjective_iff_exists_inv_mul_mem
      UG UH targetLevel hN hmn htarget]

/-- Range-top form of
`principalUnitSubquotientMapOfMapsFiltrationLevels_surjective_of_exists_inv_mul_mem`. -/
theorem principalUnitSubquotientMapOfMapsFiltrationLevels_range_eq_top_of_exists_inv_mul_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hLift : ∀ y : UG.level (targetLevel m),
      ∃ x : UH.level m,
        (y : G)⁻¹ * N (x : H) ∈
          UG.level (targetLevel n)) :
    (N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget).range = ⊤ :=
  (N.principalUnitSubquotientMapOfMapsFiltrationLevels_range_eq_top_iff_exists_inv_mul_mem
    UG UH targetLevel hN hmn htarget).2 hLift

/-- Kernel criterion on representatives for the graded-piece norm map. -/
theorem principalUnitGradedPieceMapOfMapsFiltrationLevels_mk_eq_one_iff
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.level (n + 1)).Normal]
    [(UG.level (targetLevel (n + 1))).Normal]
    (x : UH.level n) :
    N.principalUnitGradedPieceMapOfMapsFiltrationLevels
        UG UH targetLevel hN n htarget
        (UH.principalUnitGradedPieceMk n x) = 1 ↔
      N (x : H) ∈ UG.level (targetLevel (n + 1)) :=
  N.principalUnitSubquotientMapOfMapsFiltrationLevels_mk_eq_one_iff
    UG UH targetLevel hN (Nat.le_succ n) htarget x

/-- Right-quotient equality criterion on representatives for the graded-piece
norm map. -/
theorem principalUnitGradedPieceMapOfMapsFiltrationLevels_mk_eq_iff_div_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.level (n + 1)).Normal]
    [(UG.level (targetLevel (n + 1))).Normal]
    (x y : UH.level n) :
    N.principalUnitGradedPieceMapOfMapsFiltrationLevels
        UG UH targetLevel hN n htarget
        (UH.principalUnitGradedPieceMk n x) =
      N.principalUnitGradedPieceMapOfMapsFiltrationLevels
        UG UH targetLevel hN n htarget
        (UH.principalUnitGradedPieceMk n y) ↔
      N ((x / y : UH.level n) : H) ∈
        UG.level (targetLevel (n + 1)) :=
  N.principalUnitSubquotientMapOfMapsFiltrationLevels_mk_eq_iff_div_mem
    UG UH targetLevel hN (Nat.le_succ n) htarget x y

/-- Left-quotient equality criterion on representatives for the graded-piece
norm map. -/
theorem principalUnitGradedPieceMapOfMapsFiltrationLevels_mk_eq_iff_inv_mul_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.level (n + 1)).Normal]
    [(UG.level (targetLevel (n + 1))).Normal]
    (x y : UH.level n) :
    N.principalUnitGradedPieceMapOfMapsFiltrationLevels
        UG UH targetLevel hN n htarget
        (UH.principalUnitGradedPieceMk n x) =
      N.principalUnitGradedPieceMapOfMapsFiltrationLevels
        UG UH targetLevel hN n htarget
        (UH.principalUnitGradedPieceMk n y) ↔
      N ((y⁻¹ * x : UH.level n) : H) ∈
        UG.level (targetLevel (n + 1)) :=
  N.principalUnitSubquotientMapOfMapsFiltrationLevels_mk_eq_iff_inv_mul_mem
    UG UH targetLevel hN (Nat.le_succ n) htarget x y

/-- Right-quotient surjectivity criterion for the graded-piece norm map. -/
theorem principalUnitGradedPieceMapOfMapsFiltrationLevels_surjective_iff_exists_div_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.level (n + 1)).Normal]
    [(UG.level (targetLevel (n + 1))).Normal] :
    Function.Surjective
        (N.principalUnitGradedPieceMapOfMapsFiltrationLevels
          UG UH targetLevel hN n htarget) ↔
      ∀ y : UG.level (targetLevel n),
        ∃ x : UH.level n,
          N (x : H) / (y : G) ∈
            UG.level (targetLevel (n + 1)) :=
  N.principalUnitSubquotientMapOfMapsFiltrationLevels_surjective_iff_exists_div_mem
    UG UH targetLevel hN (Nat.le_succ n) htarget

/-- Left-quotient surjectivity criterion for the graded-piece norm map. -/
theorem principalUnitGradedPieceMapOfMapsFiltrationLevels_surjective_iff_exists_inv_mul_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.level (n + 1)).Normal]
    [(UG.level (targetLevel (n + 1))).Normal] :
    Function.Surjective
        (N.principalUnitGradedPieceMapOfMapsFiltrationLevels
          UG UH targetLevel hN n htarget) ↔
      ∀ y : UG.level (targetLevel n),
        ∃ x : UH.level n,
          (y : G)⁻¹ * N (x : H) ∈
            UG.level (targetLevel (n + 1)) :=
  N.principalUnitSubquotientMapOfMapsFiltrationLevels_surjective_iff_exists_inv_mul_mem
    UG UH targetLevel hN (Nat.le_succ n) htarget

/-- Range-top right-quotient criterion for the graded-piece norm map. -/
theorem principalUnitGradedPieceMapOfMapsFiltrationLevels_range_eq_top_iff_exists_div_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.level (n + 1)).Normal]
    [(UG.level (targetLevel (n + 1))).Normal] :
    (N.principalUnitGradedPieceMapOfMapsFiltrationLevels
        UG UH targetLevel hN n htarget).range = ⊤ ↔
      ∀ y : UG.level (targetLevel n),
        ∃ x : UH.level n,
          N (x : H) / (y : G) ∈
            UG.level (targetLevel (n + 1)) :=
  N.principalUnitSubquotientMapOfMapsFiltrationLevels_range_eq_top_iff_exists_div_mem
    UG UH targetLevel hN (Nat.le_succ n) htarget

/-- Range-top left-quotient criterion for the graded-piece norm map. -/
theorem principalUnitGradedPieceMapOfMapsFiltrationLevels_range_eq_top_iff_exists_inv_mul_mem
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.level (n + 1)).Normal]
    [(UG.level (targetLevel (n + 1))).Normal] :
    (N.principalUnitGradedPieceMapOfMapsFiltrationLevels
        UG UH targetLevel hN n htarget).range = ⊤ ↔
      ∀ y : UG.level (targetLevel n),
        ∃ x : UH.level n,
          (y : G)⁻¹ * N (x : H) ∈
            UG.level (targetLevel (n + 1)) :=
  N.principalUnitSubquotientMapOfMapsFiltrationLevels_range_eq_top_iff_exists_inv_mul_mem
    UG UH targetLevel hN (Nat.le_succ n) htarget

/-- Range-top form of
`quotientMapOfMapsFiltrationLevels_surjective_of_sourceLevelChange`. -/
theorem quotientMapOfMapsFiltrationLevels_range_eq_top_of_sourceLevelChange
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.level n).Normal]
    [(UH.level m).Normal]
    [(UG.level (targetLevel n)).Normal]
    [(UG.level (targetLevel m)).Normal]
    (hRange :
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range =
        ⊤) :
    (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN m).range =
        ⊤ := by
  rw [MonoidHom.range_eq_top] at hRange ⊢
  exact N.quotientMapOfMapsFiltrationLevels_surjective_of_sourceLevelChange
    UG UH targetLevel hN hmn htarget hRange

/-- A surjective valued norm induces a surjective map on the quotients by any
compatible filtration level. -/
theorem quotientMapOfMapsFiltrationLevels_surjective_of_surjective
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.level n).Normal]
    [(UG.level (targetLevel n)).Normal]
    (hSurj : Function.Surjective N) :
    Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) := by
  intro y
  refine QuotientGroup.induction_on y ?_
  intro g
  rcases hSurj g with ⟨x, rfl⟩
  exact ⟨QuotientGroup.mk x,
    QuotientGroup.map_mk (UH.level n)
      (UG.level (targetLevel n)) N (fun _ hx => hN n hx) x⟩

end MonoidHom

end
