/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Tensor exactness and covering diagrams

The tensor functor retains independent base-ring, tensor-factor and source universes.
Its right exactness follows from an explicitly constructed tensor-Hom adjunction in the
larger module universe and a proved natural comparison with universe lifting.

The categorical covering diagrams construct their kernel lifts and cokernel descents.
They can be used without reopening the concrete module instances of every diagram object.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.FlatTensor

universe u v w a b c

/-- The same concrete tensor functor, polymorphic in the source carrier universe. -/
noncomputable def tensorFunctor {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    ModuleCat.{w} R ⥤ ModuleCat.{max v w} R where
  obj N := ModuleCat.of R (M ⊗[R] N)
  map f := ModuleCat.ofHom (f.hom.lTensor M)
  map_id N := by
    apply ModuleCat.hom_ext
    exact LinearMap.lTensor_id M N
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.lTensor_comp M g.hom f.hom

section NativeHomFactories

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {X : Type a} [AddCommGroup X] [Module R X]
variable {Y : Type b} [AddCommGroup Y] [Module R Y]

/-- The actual linear map of postcomposition on a Hom module. -/
private def postcompose (f : X →ₗ[R] Y) : (M →ₗ[R] X) →ₗ[R] (M →ₗ[R] Y) where
  toFun g := f ∘ₗ g
  map_add' g h := LinearMap.comp_add g h f
  map_smul' r g := LinearMap.comp_smul f r g

/-- Curry in the orientation needed for M ⊗ - ⊣ Hom(M,-). -/
private def curryFlip (f : M ⊗[R] X →ₗ[R] Y) : X →ₗ[R] M →ₗ[R] Y :=
  (TensorProduct.curry f).flip

/-- The actual bilinear lift inverse to curryFlip. -/
private def uncurryFlip (f : X →ₗ[R] M →ₗ[R] Y) : M ⊗[R] X →ₗ[R] Y :=
  TensorProduct.lift f.flip

private theorem uncurryFlip_curryFlip (f : M ⊗[R] X →ₗ[R] Y) :
    uncurryFlip (curryFlip f) = f := by
  apply TensorProduct.ext'
  intro m x
  rfl

private theorem curryFlip_uncurryFlip (f : X →ₗ[R] M →ₗ[R] Y) :
    curryFlip (uncurryFlip f) = f := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro m
  rfl

end NativeHomFactories

/-- The actual Hom module object, constructed once at its own owner boundary. -/
private def tensorHomObject {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (X : ModuleCat.{max u v} R) :
    ModuleCat.{max u v} R := ModuleCat.of R (M →ₗ[R] X)

/-- The actual native postcomposition arrow between the constructed Hom objects. -/
private def tensorHomMap {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    {X Y : ModuleCat.{max u v} R} (f : X ⟶ Y) :
    tensorHomObject M X ⟶ tensorHomObject M Y :=
  ModuleCat.ofHom (postcompose (M := M) f.hom)

/-- Hom(M,-) in a universe large enough to contain M and all its values. -/
private def tensorHomFunctor {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R where
  obj N := tensorHomObject M N
  map f := tensorHomMap M f
  map_id N := by
    change tensorHomMap M (𝟙 N) = 𝟙 (tensorHomObject M N)
    rfl
  map_comp f g := by
    change tensorHomMap M (f ≫ g) = tensorHomMap M f ≫ tensorHomMap M g
    rfl

/-- The actual forward arrow of the tensor-Hom correspondence. -/
private noncomputable def tensorCurryHom {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    {X Y : ModuleCat.{max u v} R} (f : (tensorFunctor M).obj X ⟶ Y) :
    X ⟶ (tensorHomFunctor M).obj Y :=
  ModuleCat.ofHom (curryFlip f.hom)

/-- The actual inverse arrow of the tensor-Hom correspondence. -/
private def tensorUncurryHom {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    {X Y : ModuleCat.{max u v} R} (f : X ⟶ (tensorHomFunctor M).obj Y) :
    (tensorFunctor M).obj X ⟶ Y :=
  ModuleCat.ofHom (uncurryFlip f.hom)

private theorem tensorUncurryHom_curry {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    {X Y : ModuleCat.{max u v} R} (f : (tensorFunctor M).obj X ⟶ Y) :
    tensorUncurryHom M (tensorCurryHom M f) = f :=
  ModuleCat.hom_ext (uncurryFlip_curryFlip f.hom)

private theorem tensorCurryHom_uncurry {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    {X Y : ModuleCat.{max u v} R} (f : X ⟶ (tensorHomFunctor M).obj Y) :
    tensorCurryHom M (tensorUncurryHom M f) = f :=
  ModuleCat.hom_ext (curryFlip_uncurryFlip f.hom)

/-- Naturality of the actual inverse arrows, before any Equiv applications are present. -/
private theorem tensorUncurryHom_naturality_left {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    {X' X Y : ModuleCat.{max u v} R} (f : X' ⟶ X)
    (g : X ⟶ (tensorHomFunctor M).obj Y) :
    tensorUncurryHom M (f ≫ g) = (tensorFunctor M).map f ≫ tensorUncurryHom M g := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m x
  rfl

/-- Naturality of the actual forward arrows, with its own two-variable linear owner. -/
private theorem tensorCurryHom_naturality_right {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    {X Y Y' : ModuleCat.{max u v} R} (f : (tensorFunctor M).obj X ⟶ Y)
    (g : Y ⟶ Y') :
    tensorCurryHom M (f ≫ g) = tensorCurryHom M f ≫ (tensorHomFunctor M).map g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro m
  rfl

private noncomputable def tensorHomEquiv {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (X Y : ModuleCat.{max u v} R) :
    ((tensorFunctor M).obj X ⟶ Y) ≃ (X ⟶ (tensorHomFunctor M).obj Y) where
  toFun f := tensorCurryHom M f
  invFun f := tensorUncurryHom M f
  left_inv f := tensorUncurryHom_curry M f
  right_inv f := tensorCurryHom_uncurry M f

/-- The large-source adjunction assembles already proved native arrow computations. -/
private noncomputable def tensorHomAdjunction {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    (tensorFunctor M : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R) ⊣
      tensorHomFunctor M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv M
      homEquiv_naturality_left_symm := tensorUncurryHom_naturality_left M
      homEquiv_naturality_right := tensorCurryHom_naturality_right M }

/-- The actual comparison on one universe-lifted source object. -/
private noncomputable def tensorUliftComponent {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (X : ModuleCat.{u} R) :
    (tensorFunctor M).obj ((ModuleCat.uliftFunctor.{v, u} R).obj X) ≅
      (tensorFunctor M).obj X :=
  (TensorProduct.congr (LinearEquiv.refl R M)
    (ULift.moduleEquiv : ULift.{v, u} X ≃ₗ[R] X)).toModuleIso

/-- The small-source tensor functor is obtained from the large one via a proved comparison. -/
noncomputable def tensorUliftIso {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    ModuleCat.uliftFunctor.{v, u} R ⋙
        (tensorFunctor M : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R) ≅
      (tensorFunctor M : ModuleCat.{u} R ⥤ ModuleCat.{max u v} R) :=
  NatIso.ofComponents (tensorUliftComponent M) (by
    intro X Y f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m x
    rfl)

/-- The constructed large-source adjunction preserves colimits of every index size. -/
theorem tensorFunctor_preservesColimits_large {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    PreservesColimitsOfSize.{a, b}
      (tensorFunctor M : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R) :=
  (tensorHomAdjunction M).leftAdjoint_preservesColimits

/-- Right exactness is inherited through an actual adjunction and the proved ULift comparison. -/
theorem tensorFunctor_preservesFiniteColimits {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    PreservesFiniteColimits
      (tensorFunctor M : ModuleCat.{u} R ⥤ ModuleCat.{max u v} R) := by
  have : PreservesColimitsOfSize.{0, 0}
      (tensorFunctor M : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R) :=
    (tensorHomAdjunction M).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits
      (tensorFunctor M : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : PreservesFiniteColimits
      (ModuleCat.uliftFunctor.{v, u} R ⋙
        (tensorFunctor M : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R)) := inferInstance
  exact preservesFiniteColimits_of_natIso (tensorUliftIso M)

/-- Zero-map preservation is supplied by the constructed preservation of initial objects. -/
private instance tensorFunctor_preservesZeroMorphisms {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    (tensorFunctor M : ModuleCat.{u} R ⥤ ModuleCat.{max u v} R).PreservesZeroMorphisms := by
  have : PreservesFiniteColimits
      (tensorFunctor M : ModuleCat.{u} R ⥤ ModuleCat.{max u v} R) :=
    tensorFunctor_preservesFiniteColimits M
  infer_instance

/-- The actual tensor functor preserves exactness of a right exact complex. -/
theorem tensorFunctor_map_exact {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.Exact) (hg : Epi S.g) :
    (S.map (tensorFunctor M)).Exact := by
  have : Epi S.g := hg
  have : PreservesFiniteColimits
      (tensorFunctor M : ModuleCat.{u} R ⥤ ModuleCat.{max u v} R) :=
    tensorFunctor_preservesFiniteColimits M
  exact hS.map_of_epi_of_preservesCokernel (tensorFunctor M) hg inferInstance

end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.FlatTensor






open CategoryTheory CategoryTheory.Limits

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.FlatTensor

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Descent of a monomorphism through an exact covering row. The upper row only needs
to be a complex with an epimorphic last map. -/
theorem mono_of_cover
    {K L G X Y : C} (f : X ⟶ Y) (p : G ⟶ Y) (i : L ⟶ G)
    (q : L ⟶ X) (k : K ⟶ G) (j : K ⟶ L)
    (hq : Epi q) (hcomm : i ≫ p = q ≫ f)
    (w : k ≫ p = 0) (hk : (ShortComplex.mk k p w).Exact)
    (hji : j ≫ i = k) (hjq : j ≫ q = 0) (hi : Mono i) : Mono f := by
  let φ : CategoryTheory.ComposableArrows.mk₂ j q ⟶
      CategoryTheory.ComposableArrows.mk₂ k p :=
    CategoryTheory.ComposableArrows.homMk₂ (𝟙 K) i f
      (by
        change j ≫ i = (𝟙 K) ≫ k
        rw [Category.id_comp]
        exact hji) hcomm.symm
  exact CategoryTheory.Abelian.mono_of_epi_of_epi_mono' φ hjq hq
    hk.exact_toComposableArrows (inferInstance : Epi (𝟙 K)) hi

/-- In a morphism of complexes, monic left and right vertical maps and a monic
lower-left map make the middle vertical map monic when the upper row is exact. -/
theorem mono_middle_of_exact_subquotient
    {S T : ShortComplex C} (φ : S ⟶ T) (hS : S.Exact)
    (hleft : Mono T.f) (hvertical : Mono φ.τ₁)
    (hright : Mono φ.τ₃) : Mono φ.τ₂ := by
  have : Mono T.f := hleft
  have : Mono φ.τ₁ := hvertical
  have : Mono (φ.τ₁ ≫ T.f) := inferInstance
  have : Mono S.f := mono_of_mono_fac φ.comm₁₂.symm
  have : Mono φ.τ₃ := hright
  exact ShortComplex.mono_τ₂_of_exact_of_mono φ hS

end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.FlatTensor






open CategoryTheory CategoryTheory.Limits

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.FlatTensor

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [PreservesFiniteColimits F] [F.PreservesZeroMorphisms]

/-- A functor preserving the actual kernel cokernel cofork sends an epi to an epi. -/
theorem map_epi_of_finite_colimits {X Y : C} (p : X ⟶ Y) (hp : Epi p) :
    Epi (F.map p) := by
  have : Epi (ShortComplex.kernelSequence p).g := by
    change Epi p
    exact hp
  exact epi_of_isColimit_cofork
    (CokernelCofork.mapIsColimit _ (ShortComplex.kernelSequence_exact p).gIsCokernel F)

/-- The actual kernel lift and the exact covering diagram prove descent of a mapped mono. -/
theorem mono_map_of_pullback {X Y G : C}
    (f : X ⟶ Y) (p : G ⟶ Y) (s : PullbackCone p f) (hs : IsLimit s)
    (hp : Epi p) (hi : Mono (F.map s.fst)) : Mono (F.map f) := by
  let j : kernel p ⟶ s.pt :=
    PullbackCone.IsLimit.lift hs (kernel.ι p) 0
      (by rw [kernel.condition, zero_comp])
  have hji : j ≫ s.fst = kernel.ι p := PullbackCone.IsLimit.lift_fst hs _ _ _
  have hjq : j ≫ s.snd = 0 := PullbackCone.IsLimit.lift_snd hs _ _ _
  have : Epi p := hp
  have hq : Epi s.snd := CategoryTheory.Abelian.epi_snd_of_isLimit p f hs
  refine mono_of_cover (F.map f) (F.map p) (F.map s.fst) (F.map s.snd)
    (F.map (kernel.ι p)) (F.map j) (map_epi_of_finite_colimits F s.snd hq) ?_
    ((ShortComplex.kernelSequence p).map F).zero
    ((ShortComplex.kernelSequence_exact p).map_of_epi_of_preservesCokernel F hp inferInstance)
    ?_ ?_ hi
  · rw [← F.map_comp, ← F.map_comp, s.condition]
  · rw [← F.map_comp, hji]
  · rw [← F.map_comp, hjq, F.map_zero]

end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.FlatTensor
