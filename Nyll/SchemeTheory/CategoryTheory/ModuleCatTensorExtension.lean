/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729

Algebra-tensor representation of scalar extension.
The pinned ModuleCat implementation is used unchanged.
-/

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.CategoryTheory.NatIso
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Algebra.Basic

/-!
# Scalar extension represented by algebra tensors

Compares native scalar extension with algebra tensors using the given ring homomorphism.
-/

universe u
open CategoryTheory TensorProduct
namespace ModuleCat
open scoped ChangeOfRings

/-- The native restriction action and the algebra action from the same ring
map agree as module structures, including their scalar multiplication. -/
theorem compHom_eq_module_toAlgebra
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Module.compHom S f = (letI : Algebra R S := f.toAlgebra; inferInstanceAs (Module R S)) := by
  apply Module.ext'
  intro r s
  rfl

/-- A scalar extension represented by the raw algebra tensor used by the
maintained presentation and descent APIs. Its action is fixed by the ring map. -/
noncomputable def algebraTensorObj
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) : ModuleCat.{u} S :=
  letI : Algebra R S := f.toAlgebra
  ModuleCat.of S (S ⊗[R] M)

/-- Explicit scalar-preserving identification of the native extension with
the algebra-tensor representation. Both directions preserve the actual values. -/
noncomputable def extendScalarsAlgebraTensorEquiv
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) :
    letI : Algebra R S := f.toAlgebra
    (extendScalars f).obj M ≃ₗ[S] S ⊗[R] M := by
  let : Algebra R S := f.toAlgebra
  exact
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem extendScalarsAlgebraTensorEquiv_tmul
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) (s : S) (m : M) :
    letI : Algebra R S := f.toAlgebra
    extendScalarsAlgebraTensorEquiv f M (s ⊗ₜ[R,f] m) = s ⊗ₜ[R] m := by
  rfl

theorem extendScalarsAlgebraTensorEquiv_smul
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) (s : S) (x : (extendScalars f).obj M) :
    letI : Algebra R S := f.toAlgebra
    extendScalarsAlgebraTensorEquiv f M (s • x) = s • extendScalarsAlgebraTensorEquiv f M x := by
  exact LinearEquiv.map_smul (extendScalarsAlgebraTensorEquiv f M) s x

/-- The concrete representation is isomorphic to the pinned native extension. -/
noncomputable def algebraTensorIsoExtendScalars
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) : algebraTensorObj f M ≅ (extendScalars f).obj M := by
  let : Algebra R S := f.toAlgebra
  exact (extendScalarsAlgebraTensorEquiv f M).symm.toModuleIso

/-- Scalar extension with one algebra-tensor representation for both objects
and maps. This uses the same ring map and scalar multiplication as the raw
presentation API, rather than asking callers to reconcile native carriers. -/
noncomputable def algebraTensorExtension
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} S := by
  let : Algebra R S := f.toAlgebra
  exact
    { obj := algebraTensorObj f
      map := fun g => ModuleCat.ofHom (g.hom.baseChange S)
      map_id := fun M => ModuleCat.hom_ext (LinearMap.baseChange_id (R := R) (A := S) (M := M))
      map_comp := fun g h => ModuleCat.hom_ext (LinearMap.baseChange_comp (A := S) g.hom h.hom) }

/-- The new representation maps pure tensors to the same pure tensors as
the original raw LinearMap.baseChange operation. -/
theorem algebraTensorExtension_map_tmul
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {M N : ModuleCat.{u} R} (g : M ⟶ N) (s : S) (m : M) :
    letI : Algebra R S := f.toAlgebra
    (algebraTensorExtension f).map g (show algebraTensorObj f M from s ⊗ₜ[R] m) =
      (show algebraTensorObj f N from s ⊗ₜ[R] g m) := by
  let : Algebra R S := f.toAlgebra
  change g.hom.baseChange S (s ⊗ₜ[R] m) = s ⊗ₜ[R] g m
  exact LinearMap.baseChange_tmul g.hom s m

/-- The coherent algebra-tensor functor agrees naturally with the pinned
native scalar-extension functor; the component isomorphisms preserve values. -/
noncomputable def algebraTensorExtensionIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    algebraTensorExtension f ≅ extendScalars f := by
  let : Algebra R S := f.toAlgebra
  refine NatIso.ofComponents (algebraTensorIsoExtendScalars f) ?_
  intro M N g
  apply ModuleCat.hom_ext
  let lhs : algebraTensorObj f M →ₗ[S] (extendScalars f).obj N :=
    ((algebraTensorExtension f).map g ≫ (algebraTensorIsoExtendScalars f N).hom).hom
  let rhs : algebraTensorObj f M →ₗ[S] (extendScalars f).obj N :=
    ((algebraTensorIsoExtendScalars f M).hom ≫ (extendScalars f).map g).hom
  change lhs = rhs
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    change (s ⊗ₜ[R,f] g m : (extendScalars f).obj N) =
      (extendScalars f).map g (s ⊗ₜ[R,f] m)
    exact (ExtendScalars.map_tmul f g s m).symm
  | add x y hx hy =>
    exact (lhs.map_add x y).trans
      ((congrArg₂ (fun a b : (extendScalars f).obj N => a + b) hx hy).trans
        (rhs.map_add x y).symm)

/-- The chosen representation has exactly the original raw tensor scalar
action; this identifies the action itself, not merely an unstructured bijection. -/
theorem algebraTensorObj_smul
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) (s : S) (x : algebraTensorObj f M) :
    letI : Algebra R S := f.toAlgebra
    (show S ⊗[R] M from s • x) = s • (show S ⊗[R] M from x) := by
  rfl

/-- The pure-tensor constructor in the chosen representation. -/
noncomputable def algebraTensorTmul
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) (s : S) (m : M) : algebraTensorObj f M :=
  letI : Algebra R S := f.toAlgebra
  s ⊗ₜ[R] m

theorem algebraTensorTmul_eq
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) (s : S) (m : M) :
    letI : Algebra R S := f.toAlgebra
    (show S ⊗[R] M from algebraTensorTmul f M s m) = s ⊗ₜ[R] m := by
  rfl

theorem extendScalarsAlgebraTensorEquiv_symm_tmul
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) (s : S) (m : M) :
    (extendScalarsAlgebraTensorEquiv f M).symm (algebraTensorTmul f M s m) =
      (s ⊗ₜ[R,f] m : (extendScalars f).obj M) := by
  rfl

/-- Realize an algebra-tensor object through the explicit native comparison.
Callers receive a linear equivalence with the presentation's actual source action. -/
noncomputable def algebraTensorRealization
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) {N : Type*} [AddCommGroup N] [Module S N]
    (I : (extendScalars f).obj M ≃ₗ[S] N) : algebraTensorObj f M ≃ₗ[S] N :=
  (extendScalarsAlgebraTensorEquiv f M).symm ≪≫ₗ I

theorem algebraTensorRealization_tmul
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) {N : Type*} [AddCommGroup N] [Module S N]
    (I : (extendScalars f).obj M ≃ₗ[S] N) (s : S) (m : M) :
    algebraTensorRealization f M I (algebraTensorTmul f M s m) = I (s ⊗ₜ[R,f] m) := by
  change I ((extendScalarsAlgebraTensorEquiv f M).symm (algebraTensorTmul f M s m)) = _
  exact congrArg I (extendScalarsAlgebraTensorEquiv_symm_tmul f M s m)

theorem algebraTensorRealization_apply_native
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) {N : Type*} [AddCommGroup N] [Module S N]
    (I : (extendScalars f).obj M ≃ₗ[S] N) (x : (extendScalars f).obj M) :
    algebraTensorRealization f M I (extendScalarsAlgebraTensorEquiv f M x) = I x := by
  change I ((extendScalarsAlgebraTensorEquiv f M).symm
    (extendScalarsAlgebraTensorEquiv f M x)) = I x
  exact congrArg I ((extendScalarsAlgebraTensorEquiv f M).symm_apply_apply x)

/-- Transport a chart and overlap realization into the coherent tensor
representation, together with their original unit-generator restriction law. -/
theorem exists_algebraTensor_realization_pair
    {B C V U : Type u} [CommRing B] [CommRing C] [CommRing V] [CommRing U]
    (p : B →+* V) (q : B →+* C) (g : C →+* U) (X : ModuleCat.{u} B)
    {N O : Type*} [AddCommGroup N] [Module V N] [AddCommGroup O] [Module U O]
    (I : (extendScalars p).obj X ≃ₗ[V] N)
    (J : (extendScalars g).obj ((extendScalars q).obj X) ≃ₗ[U] O) (r : N → O)
    (hJ : ∀ (a : U) (x : X),
      J (a ⊗ₜ[C,g] (show (extendScalars q).obj X from
        (extendRestrictScalarsAdj q).unit.app X x)) =
      a • r (I ((extendRestrictScalarsAdj p).unit.app X x))) :
    let Q : ModuleCat.{u} C := (extendScalars q).obj X
    ∃ (newI : algebraTensorObj p X ≃ₗ[V] N) (Xi : algebraTensorObj g Q ≃ₗ[U] O),
      (∀ z : (extendScalars p).obj X, newI (extendScalarsAlgebraTensorEquiv p X z) = I z) ∧
      (∀ z : (extendScalars g).obj Q, Xi (extendScalarsAlgebraTensorEquiv g Q z) = J z) ∧
      ∀ (a : U) (x : X),
        Xi (algebraTensorTmul g Q a (show Q from (extendRestrictScalarsAdj q).unit.app X x)) =
        a • r (newI (algebraTensorTmul p X (1 : V) x)) := by
  let Q : ModuleCat.{u} C := (extendScalars q).obj X
  let newI : algebraTensorObj p X ≃ₗ[V] N := algebraTensorRealization p X I
  let Xi : algebraTensorObj g Q ≃ₗ[U] O := algebraTensorRealization g Q J
  refine ⟨newI, Xi, algebraTensorRealization_apply_native p X I,
    algebraTensorRealization_apply_native g Q J, ?_⟩
  intro a x
  have hleft := algebraTensorRealization_tmul g Q J a
    (show Q from (extendRestrictScalarsAdj q).unit.app X x)
  have hright := (algebraTensorRealization_tmul p X I (1 : V) x).trans
    (congrArg I (extendRestrictScalarsAdj_unit_app_apply p X x).symm)
  exact hleft.trans ((hJ a x).trans (congrArg (fun n : N => a • r n) hright.symm))

/-- Preserve the actual commuting realization square in native scalar
extensions before transporting its representation. -/
theorem realization_extendScalars_compat
    {R U : Type u} [CommRing R] [CommRing U] (f : R →+* U)
    (X0 X1 : ModuleCat.{u} R) (Y0 Y1 : ModuleCat.{u} U)
    {N : Type*} [AddCommGroup N] [Module U N]
    (σ : X0 ≅ X1) (F0 : (extendScalars f).obj X0 ≅ Y0)
    (F1 : (extendScalars f).obj X1 ≅ Y1) (τ : Y0 ≅ Y1)
    (I0 : (extendScalars f).obj X0 ≃ₗ[U] N) (I1 : (extendScalars f).obj X1 ≃ₗ[U] N)
    (J0 : Y0 ≃ₗ[U] N) (J1 : Y1 ≃ₗ[U] N)
    (h0 : ∀ z : (extendScalars f).obj X0, I0 z = J0 (F0.hom z))
    (h1 : ∀ z : (extendScalars f).obj X1, I1 z = J1 (F1.hom z))
    (hτ : ∀ y : Y0, J1 (τ.hom y) = J0 y)
    (hsquare : (extendScalars f).mapIso σ ≪≫ F1 = F0 ≪≫ τ) :
    ∀ z : (extendScalars f).obj X0, I1 (((extendScalars f).mapIso σ).hom z) = I0 z := by
  intro z
  have hleft : ((extendScalars f).mapIso σ ≪≫ F1).hom z =
      F1.hom (((extendScalars f).mapIso σ).hom z) :=
    ModuleCat.comp_apply ((extendScalars f).mapIso σ).hom F1.hom z
  have heval : ((extendScalars f).mapIso σ ≪≫ F1).hom z = (F0 ≪≫ τ).hom z :=
    congrArg (fun e : (extendScalars f).obj X0 ≅ Y1 => e.hom z) hsquare
  have hright : (F0 ≪≫ τ).hom z = τ.hom (F0.hom z) :=
    ModuleCat.comp_apply F0.hom τ.hom z
  exact (h1 (((extendScalars f).mapIso σ).hom z)).trans
    ((congrArg J1 (hleft.symm.trans (heval.trans hright))).trans
      ((hτ (F0.hom z)).trans (h0 z).symm))

/-- Transport a proved native realization comparison to the original raw
base-change map through the natural representation isomorphism. -/
theorem algebraTensor_realization_baseChange_compat
    {R U : Type u} [CommRing R] [CommRing U] (f : R →+* U)
    (X0 X1 : ModuleCat.{u} R) (σ : X0 ≅ X1) {N : Type*}
    (I0 : (extendScalars f).obj X0 → N) (I1 : (extendScalars f).obj X1 → N)
    (J0 : algebraTensorObj f X0 → N) (J1 : algebraTensorObj f X1 → N)
    (h0 : ∀ z : (extendScalars f).obj X0, J0 (extendScalarsAlgebraTensorEquiv f X0 z) = I0 z)
    (h1 : ∀ z : (extendScalars f).obj X1, J1 (extendScalarsAlgebraTensorEquiv f X1 z) = I1 z)
    (hI : ∀ z : (extendScalars f).obj X0, I1 (((extendScalars f).mapIso σ).hom z) = I0 z) :
    letI : Algebra R U := f.toAlgebra
    ∀ z : U ⊗[R] X0,
      J1 (LinearEquiv.baseChange R U X0 X1 σ.toLinearEquiv z) = J0 z := by
  let : Algebra R U := f.toAlgebra
  let E0 := extendScalarsAlgebraTensorEquiv f X0
  let E1 := extendScalarsAlgebraTensorEquiv f X1
  intro z
  have hnat := congrArg
    (fun k : (extendScalars f).obj X0 ⟶ algebraTensorObj f X1 => k (E0.symm z))
    ((algebraTensorExtensionIso f).inv.naturality σ.hom)
  change E1 (((extendScalars f).mapIso σ).hom (E0.symm z)) =
    LinearEquiv.baseChange R U X0 X1 σ.toLinearEquiv (E0 (E0.symm z)) at hnat
  have hcoords := hnat.trans
    (congrArg (LinearEquiv.baseChange R U X0 X1 σ.toLinearEquiv) (E0.apply_symm_apply z))
  exact (congrArg J1 hcoords.symm).trans
    ((h1 (((extendScalars f).mapIso σ).hom (E0.symm z))).trans
      ((hI (E0.symm z)).trans
        ((h0 (E0.symm z)).symm.trans (congrArg J0 (E0.apply_symm_apply z)))))

/-- The categorical comparison for a prescribed commuting triangle of ring maps
is the inverse of tensor cancellation with those same prescribed scalar actions. -/
theorem extendScalars_comparison_eq_cancel
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T)
    (hcomp : g.comp f = h) (M : ModuleCat.{u} R) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra R T := h.toAlgebra
    letI : IsScalarTower R S T :=
      IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun hcomp r).symm
    let c : extendScalars h ≅ extendScalars f ⋙ extendScalars g :=
      (eqToIso (congrArg (fun q : R →+* T => extendScalars.{u, u, u} q) hcomp)).symm ≪≫
        extendScalarsComp f g
    c.app M =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M).symm.toModuleIso := by
  let : Algebra R S := f.toAlgebra
  let : Algebra S T := g.toAlgebra
  let : Algebra R T := h.toAlgebra
  let : IsScalarTower R S T :=
    IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun hcomp r).symm
  let c : extendScalars h ≅ extendScalars f ⋙ extendScalars g :=
    (eqToIso (congrArg (fun q : R →+* T => extendScalars.{u, u, u} q) hcomp)).symm ≪≫
      extendScalarsComp f g
  change c.app M = _
  have hcast : ∀ (a b : R →+* T) (w : a = b) (N : ModuleCat.{u} R) (n : N),
      (eqToIso (congrArg (fun q : R →+* T => extendScalars.{u, u, u} q) w)).inv.app N
        ((1 : T) ⊗ₜ[R,b] n) = (1 : T) ⊗ₜ[R,a] n := by
    intro a b w N n
    subst b
    rfl
  apply CategoryTheory.Iso.ext
  apply ExtendScalars.hom_ext (f := h)
  intro m
  change (extendScalarsComp f g).hom.app M
      ((eqToIso (congrArg (fun q : R →+* T => extendScalars.{u, u, u} q) hcomp)).inv.app M
        ((1 : T) ⊗ₜ[R,h] m)) = _
  rw [hcast (g.comp f) h hcomp M m]
  exact extendScalarsComp_hom_app_one_tmul f g M m

/-- The canonical scalar-extension comparison of a commuting ring square sends
 an elementary chart tensor to its restricted coefficient on the overlap. -/
theorem extendScalars_square_tmul
    {B J C D : Type u} [CommRing B] [CommRing J] [CommRing C] [CommRing D]
    (a : B →+* J) (q : B →+* C) (r : J →+* D) (s : C →+* D)
    (hsquare : r.comp a = s.comp q) (X : ModuleCat.{u} B) (x : X) (j : J) :
    let P : ModuleCat.{u} J := (extendScalars a).obj X
    let Q : ModuleCat.{u} C := (extendScalars q).obj X
    let c : extendScalars (r.comp a) ≅ extendScalars q ⋙ extendScalars s :=
      (eqToIso (congrArg (fun t : B →+* D => extendScalars.{u, u, u} t) hsquare.symm)).symm ≪≫
        extendScalarsComp q s
    let square : (extendScalars r).obj P ≅ (extendScalars s).obj Q :=
      (extendScalarsComp a r).symm.app X ≪≫ c.app X
    let xj : P := j ⊗ₜ[B,a] x
    let xq : Q := (extendRestrictScalarsAdj q).unit.app X x
    square.hom ((1 : D) ⊗ₜ[J,r] xj) = r j ⊗ₜ[C,s] xq := by
  let : Algebra B J := a.toAlgebra
  let : Algebra B C := q.toAlgebra
  let : Algebra J D := r.toAlgebra
  let : Algebra C D := s.toAlgebra
  let : Algebra B D := (r.comp a).toAlgebra
  have : IsScalarTower B J D := IsScalarTower.of_algebraMap_eq fun b => rfl
  have : IsScalarTower B C D := IsScalarTower.of_algebraMap_eq fun b =>
    RingHom.congr_fun hsquare b
  let P : ModuleCat.{u} J := (extendScalars a).obj X
  let Q : ModuleCat.{u} C := (extendScalars q).obj X
  let c : extendScalars (r.comp a) ≅ extendScalars q ⋙ extendScalars s :=
    (eqToIso (congrArg (fun t : B →+* D => extendScalars.{u, u, u} t) hsquare.symm)).symm ≪≫
      extendScalarsComp q s
  let square : (extendScalars r).obj P ≅ (extendScalars s).obj Q :=
    (extendScalarsComp a r).symm.app X ≪≫ c.app X
  let xj : P := j ⊗ₜ[B,a] x
  let xq : Q := (extendRestrictScalarsAdj q).unit.app X x
  change square.hom ((1 : D) ⊗ₜ[J,r] xj) = r j ⊗ₜ[C,s] xq
  have hleft : (extendScalarsComp a r).app X =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B J D D X).symm.toModuleIso :=
    extendScalars_comparison_eq_cancel a r (r.comp a) rfl X
  have hright : c.app X =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B C D D X).symm.toModuleIso :=
    extendScalars_comparison_eq_cancel q s (r.comp a) hsquare.symm X
  have hsquareIso : square =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B J D D X).toModuleIso ≪≫
        (TensorProduct.AlgebraTensorModule.cancelBaseChange B C D D X).symm.toModuleIso := by
    change ((extendScalarsComp a r).app X).symm ≪≫ c.app X = _
    rw [hleft, hright]
    rfl
  rw [hsquareIso]
  change (TensorProduct.AlgebraTensorModule.cancelBaseChange B C D D X).symm
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B J D D X
        ((1 : D) ⊗ₜ[J] (j ⊗ₜ[B] x))) = r j ⊗ₜ[C] ((1 : C) ⊗ₜ[B] x)
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  change (TensorProduct.AlgebraTensorModule.cancelBaseChange B C D D X).symm
    ((r j * 1) ⊗ₜ[B] x) = _
  rw [mul_one, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]

/-- Transport a clutching isomorphism through two commuting scalar-extension
 squares. The chart comparisons, their tensor formulas, and the complete
 intertwining equation for the transported clutching are constructed together. -/
theorem exists_clutching_of_commuting_squares
    {B0 B1 C J0 J1 D : Type u}
    [CommRing B0] [CommRing B1] [CommRing C]
    [CommRing J0] [CommRing J1] [CommRing D]
    (t0 : B0 →+* J0) (t1 : B1 →+* J1)
    (q0 : B0 →+* C) (q1 : B1 →+* C)
    (r0 : J0 →+* D) (r1 : J1 →+* D) (s : C →+* D)
    (h0 : r0.comp t0 = s.comp q0) (h1 : r1.comp t1 = s.comp q1)
    (X0 : ModuleCat.{u} B0) (X1 : ModuleCat.{u} B1)
    (σ : (extendScalars q0).obj X0 ≅ (extendScalars q1).obj X1) :
    letI : Algebra J0 D := r0.toAlgebra
    letI : Algebra J1 D := r1.toAlgebra
    letI : Algebra C D := s.toAlgebra
    let P0 : ModuleCat.{u} J0 := (extendScalars t0).obj X0
    let P1 : ModuleCat.{u} J1 := (extendScalars t1).obj X1
    let Q0 : ModuleCat.{u} C := (extendScalars q0).obj X0
    let Q1 : ModuleCat.{u} C := (extendScalars q1).obj X1
    ∃ (kappa0 : D ⊗[J0] P0 ≃ₗ[D] D ⊗[C] Q0)
      (kappa1 : D ⊗[J1] P1 ≃ₗ[D] D ⊗[C] Q1)
      (sigmaD : D ⊗[J0] P0 ≃ₗ[D] D ⊗[J1] P1),
      (∀ (j : J0) (x : X0),
        kappa0 ((1 : D) ⊗ₜ[J0] (show P0 from j ⊗ₜ[B0,t0] x)) =
          r0 j ⊗ₜ[C] (show Q0 from (extendRestrictScalarsAdj q0).unit.app X0 x)) ∧
      (∀ (j : J1) (x : X1),
        kappa1 ((1 : D) ⊗ₜ[J1] (show P1 from j ⊗ₜ[B1,t1] x)) =
          r1 j ⊗ₜ[C] (show Q1 from (extendRestrictScalarsAdj q1).unit.app X1 x)) ∧
      ∀ z : D ⊗[J0] P0,
        kappa1 (sigmaD z) =
          LinearEquiv.baseChange C D Q0 Q1 σ.toLinearEquiv (kappa0 z) := by
  let : Algebra J0 D := r0.toAlgebra
  let : Algebra J1 D := r1.toAlgebra
  let : Algebra C D := s.toAlgebra
  let P0 : ModuleCat.{u} J0 := (extendScalars t0).obj X0
  let P1 : ModuleCat.{u} J1 := (extendScalars t1).obj X1
  let Q0 : ModuleCat.{u} C := (extendScalars q0).obj X0
  let Q1 : ModuleCat.{u} C := (extendScalars q1).obj X1
  let c0 : extendScalars (r0.comp t0) ≅ extendScalars q0 ⋙ extendScalars s :=
    (eqToIso (congrArg (fun f : B0 →+* D => extendScalars.{u, u, u} f) h0.symm)).symm ≪≫
      extendScalarsComp q0 s
  let square0 : (extendScalars r0).obj P0 ≅ (extendScalars s).obj Q0 :=
    (extendScalarsComp t0 r0).symm.app X0 ≪≫ c0.app X0
  let c1 : extendScalars (r1.comp t1) ≅ extendScalars q1 ⋙ extendScalars s :=
    (eqToIso (congrArg (fun f : B1 →+* D => extendScalars.{u, u, u} f) h1.symm)).symm ≪≫
      extendScalarsComp q1 s
  let square1 : (extendScalars r1).obj P1 ≅ (extendScalars s).obj Q1 :=
    (extendScalarsComp t1 r1).symm.app X1 ≪≫ c1.app X1
  let kappa0 : D ⊗[J0] P0 ≃ₗ[D] D ⊗[C] Q0 := square0.toLinearEquiv
  let kappa1 : D ⊗[J1] P1 ≃ₗ[D] D ⊗[C] Q1 := square1.toLinearEquiv
  let sigmaBase : D ⊗[C] Q0 ≃ₗ[D] D ⊗[C] Q1 :=
    LinearEquiv.baseChange C D Q0 Q1 σ.toLinearEquiv
  let sigmaD : D ⊗[J0] P0 ≃ₗ[D] D ⊗[J1] P1 :=
    kappa0 ≪≫ₗ sigmaBase ≪≫ₗ kappa1.symm
  refine ⟨kappa0, kappa1, sigmaD, ?_, ?_, ?_⟩
  · intro j x
    exact extendScalars_square_tmul t0 q0 r0 s h0 X0 x j
  · intro j x
    exact extendScalars_square_tmul t1 q1 r1 s h1 X1 x j
  · intro z
    have houter : sigmaD z = kappa1.symm ((kappa0 ≪≫ₗ sigmaBase) z) :=
      LinearEquiv.trans_apply (e₁₂ := kappa0 ≪≫ₗ sigmaBase) (e₂₃ := kappa1.symm) z
    have hinner : (kappa0 ≪≫ₗ sigmaBase) z = sigmaBase (kappa0 z) :=
      LinearEquiv.trans_apply (e₁₂ := kappa0) (e₂₃ := sigmaBase) z
    exact (congrArg kappa1 (houter.trans (congrArg kappa1.symm hinner))).trans
      (kappa1.apply_symm_apply (sigmaBase (kappa0 z)))

/-- Build the original clutching in the algebra-tensor chart representation.
Both source identifications are the proved scalar-preserving comparisons;
the supplied commuting squares and stage isomorphism remain the only inputs. -/
theorem exists_algebraTensor_clutching_of_commuting_squares
    {B0 B1 C J0 J1 D : Type u}
    [CommRing B0] [CommRing B1] [CommRing C]
    [CommRing J0] [CommRing J1] [CommRing D]
    (t0 : B0 →+* J0) (t1 : B1 →+* J1)
    (q0 : B0 →+* C) (q1 : B1 →+* C)
    (r0 : J0 →+* D) (r1 : J1 →+* D) (s : C →+* D)
    (h0 : r0.comp t0 = s.comp q0) (h1 : r1.comp t1 = s.comp q1)
    (X0 : ModuleCat.{u} B0) (X1 : ModuleCat.{u} B1)
    (σ : (extendScalars q0).obj X0 ≅ (extendScalars q1).obj X1) :
    letI : Algebra J0 D := r0.toAlgebra
    letI : Algebra J1 D := r1.toAlgebra
    letI : Algebra C D := s.toAlgebra
    let P0 : ModuleCat.{u} J0 := algebraTensorObj t0 X0
    let P1 : ModuleCat.{u} J1 := algebraTensorObj t1 X1
    let Q0 : ModuleCat.{u} C := (extendScalars q0).obj X0
    let Q1 : ModuleCat.{u} C := (extendScalars q1).obj X1
    ∃ (kappa0 : D ⊗[J0] P0 ≃ₗ[D] D ⊗[C] Q0)
      (kappa1 : D ⊗[J1] P1 ≃ₗ[D] D ⊗[C] Q1)
      (sigmaD : D ⊗[J0] P0 ≃ₗ[D] D ⊗[J1] P1),
      (∀ (j : J0) (x : X0),
        kappa0 ((1 : D) ⊗ₜ[J0] algebraTensorTmul t0 X0 j x) =
          r0 j ⊗ₜ[C] (show Q0 from (extendRestrictScalarsAdj q0).unit.app X0 x)) ∧
      (∀ (j : J1) (x : X1),
        kappa1 ((1 : D) ⊗ₜ[J1] algebraTensorTmul t1 X1 j x) =
          r1 j ⊗ₜ[C] (show Q1 from (extendRestrictScalarsAdj q1).unit.app X1 x)) ∧
      ∀ z : D ⊗[J0] P0,
        kappa1 (sigmaD z) =
          LinearEquiv.baseChange C D Q0 Q1 σ.toLinearEquiv (kappa0 z) := by
  let : Algebra J0 D := r0.toAlgebra
  let : Algebra J1 D := r1.toAlgebra
  let : Algebra C D := s.toAlgebra
  let P0 : ModuleCat.{u} J0 := algebraTensorObj t0 X0
  let P1 : ModuleCat.{u} J1 := algebraTensorObj t1 X1
  let Q0 : ModuleCat.{u} C := (extendScalars q0).obj X0
  let Q1 : ModuleCat.{u} C := (extendScalars q1).obj X1
  obtain ⟨K0, K1, _, hK0, hK1, _⟩ :=
    exists_clutching_of_commuting_squares t0 t1 q0 q1 r0 r1 s h0 h1 X0 X1 σ
  let E0 : P0 ≃ₗ[J0] (extendScalars t0).obj X0 :=
    (extendScalarsAlgebraTensorEquiv t0 X0).symm
  let E1 : P1 ≃ₗ[J1] (extendScalars t1).obj X1 :=
    (extendScalarsAlgebraTensorEquiv t1 X1).symm
  let T0 : D ⊗[J0] P0 ≃ₗ[D] D ⊗[J0] (extendScalars t0).obj X0 :=
    LinearEquiv.baseChange J0 D P0 ((extendScalars t0).obj X0) E0
  let T1 : D ⊗[J1] P1 ≃ₗ[D] D ⊗[J1] (extendScalars t1).obj X1 :=
    LinearEquiv.baseChange J1 D P1 ((extendScalars t1).obj X1) E1
  let kappa0 : D ⊗[J0] P0 ≃ₗ[D] D ⊗[C] Q0 := T0 ≪≫ₗ K0
  let kappa1 : D ⊗[J1] P1 ≃ₗ[D] D ⊗[C] Q1 := T1 ≪≫ₗ K1
  let sigmaBase : D ⊗[C] Q0 ≃ₗ[D] D ⊗[C] Q1 :=
    LinearEquiv.baseChange C D Q0 Q1 σ.toLinearEquiv
  let sigmaD : D ⊗[J0] P0 ≃ₗ[D] D ⊗[J1] P1 :=
    kappa0 ≪≫ₗ sigmaBase ≪≫ₗ kappa1.symm
  refine ⟨kappa0, kappa1, sigmaD, ?_, ?_, ?_⟩
  · intro j x
    change K0 (T0 ((1 : D) ⊗ₜ[J0] algebraTensorTmul t0 X0 j x)) = _
    have ht := LinearEquiv.baseChange_tmul
      (R := J0) (A := D) (M := P0) (N := (extendScalars t0).obj X0) (e := E0)
      (1 : D) (algebraTensorTmul t0 X0 j x)
    have hv := extendScalarsAlgebraTensorEquiv_symm_tmul t0 X0 j x
    exact (congrArg K0 (ht.trans
      (congrArg (fun p : (extendScalars t0).obj X0 => (1 : D) ⊗ₜ[J0] p) hv))).trans (hK0 j x)
  · intro j x
    change K1 (T1 ((1 : D) ⊗ₜ[J1] algebraTensorTmul t1 X1 j x)) = _
    have ht := LinearEquiv.baseChange_tmul
      (R := J1) (A := D) (M := P1) (N := (extendScalars t1).obj X1) (e := E1)
      (1 : D) (algebraTensorTmul t1 X1 j x)
    have hv := extendScalarsAlgebraTensorEquiv_symm_tmul t1 X1 j x
    exact (congrArg K1 (ht.trans
      (congrArg (fun p : (extendScalars t1).obj X1 => (1 : D) ⊗ₜ[J1] p) hv))).trans (hK1 j x)
  · intro z
    have houter : sigmaD z = kappa1.symm ((kappa0 ≪≫ₗ sigmaBase) z) :=
      LinearEquiv.trans_apply (e₁₂ := kappa0 ≪≫ₗ sigmaBase) (e₂₃ := kappa1.symm) z
    have hinner : (kappa0 ≪≫ₗ sigmaBase) z = sigmaBase (kappa0 z) :=
      LinearEquiv.trans_apply (e₁₂ := kappa0) (e₂₃ := sigmaBase) z
    exact (congrArg kappa1 (houter.trans (congrArg kappa1.symm hinner))).trans
      (kappa1.apply_symm_apply (sigmaBase (kappa0 z)))

/-- Invertibility is preserved by the chosen algebra-tensor representation. -/
theorem invertible_algebraTensorObj_of_invertible
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) [Module.Invertible R M] :
    Module.Invertible S (algebraTensorObj f M) := by
  let : Algebra R S := f.toAlgebra
  exact inferInstanceAs (Module.Invertible S (S ⊗[R] M))

/-- Evaluate a linear map on a pure tensor in the chosen representation
using its value on the unit tensor. -/
theorem algebraTensor_linearMap_tmul_of_unit
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) {N : Type*} [AddCommGroup N] [Module S N]
    (e : algebraTensorObj f M →ₗ[S] N) (m : M) (s : S) :
    e (algebraTensorTmul f M s m) = s • e (algebraTensorTmul f M (1 : S) m) := by
  let : Algebra R S := f.toAlgebra
  have hfactor : algebraTensorTmul f M s m = s • algebraTensorTmul f M (1 : S) m := by
    change (s ⊗ₜ[R] m : S ⊗[R] M) = s • ((1 : S) ⊗ₜ[R] m)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact (congrArg e hfactor).trans (e.map_smul s (algebraTensorTmul f M (1 : S) m))

/-- Evaluate an overlap presentation with the coherent algebra-tensor
realization. All scalar actions are those of the existing presentation. -/
theorem algebraTensor_presented_overlap_generator
    {J C D U : Type u} [CommRing J] [CommRing C] [CommRing D] [CommRing U]
    (r : J →+* D) (s : C →+* D) (t : C →+* U)
    (P : ModuleCat.{u} J) (Q : ModuleCat.{u} C)
    {X N : Type*} [AddCommGroup N] [Module U N]
    (g : J → X → P) (η : X → Q) (ψ : D → U) (b : X → N)
    (κ : letI : Algebra J D := r.toAlgebra; letI : Algebra C D := s.toAlgebra;
      D ⊗[J] P ≃ₗ[D] D ⊗[C] Q)
    (F : letI : Algebra C D := s.toAlgebra; letI : Algebra C U := t.toAlgebra;
      D ⊗[C] Q → U ⊗[C] Q)
    (I : algebraTensorObj t Q ≃ₗ[U] N)
    (hκ : letI : Algebra J D := r.toAlgebra; letI : Algebra C D := s.toAlgebra;
      ∀ (j : J) (x : X), κ ((1 : D) ⊗ₜ[J] g j x) = r j ⊗ₜ[C] η x)
    (hF : letI : Algebra C D := s.toAlgebra; letI : Algebra C U := t.toAlgebra;
      ∀ (d : D) (q : Q), F (d ⊗ₜ[C] q) = ψ d ⊗ₜ[C] q)
    (hI : ∀ (a : U) (x : X), I (algebraTensorTmul t Q a (η x)) = a • b x) :
    letI : Algebra J D := r.toAlgebra
    letI : Algebra C D := s.toAlgebra
    letI : Algebra C U := t.toAlgebra
    ∀ (j : J) (x : X), I (F (κ ((1 : D) ⊗ₜ[J] g j x))) = ψ (r j) • b x := by
  let : Algebra J D := r.toAlgebra
  let : Algebra C D := s.toAlgebra
  let : Algebra C U := t.toAlgebra
  intro j x
  exact (congrArg (fun z : D ⊗[C] Q => I (F z)) (hκ j x)).trans
    ((congrArg I (hF (r j) (η x))).trans (hI (ψ (r j)) x))

end ModuleCat

namespace TensorProduct

/-- Realize a tensor presentation while constructing its scalar compatibility
from the presentation's original scalar law and the realization's linearity. -/
theorem exists_realized_tensorPresentation_with_scalar
    (k A U : Type*) [CommRing k] [CommRing A] [CommRing U]
    [Algebra k A] [Algebra A U]
    {S P Q N : Type*} [AddCommGroup P] [Module k P] [SMul S P]
    [AddCommGroup Q] [Module A Q] [Module U Q] [IsScalarTower A U Q]
    [AddCommGroup N] [Module A N] [Module U N] [IsScalarTower A U N]
    (φ : S → U) (F : A ⊗[k] P ≃ₗ[A] Q) (G : Q ≃ₗ[U] N)
    (hF : ∀ (s : S) (p : P),
      F ((1 : A) ⊗ₜ[k] (s • p)) = ((1 : A) • φ s) • F ((1 : A) ⊗ₜ[k] p)) :
    ∃ H : A ⊗[k] P ≃ₗ[A] N,
      (∀ (a : A) (p : P), H (a ⊗ₜ[k] p) = G (F (a ⊗ₜ[k] p))) ∧
      ∀ (s : S) (p : P), H ((1 : A) ⊗ₜ[k] (s • p)) = φ s • H ((1 : A) ⊗ₜ[k] p) := by
  let H : A ⊗[k] P ≃ₗ[A] N := F ≪≫ₗ G.restrictScalars A
  refine ⟨H, (fun _ _ => rfl), ?_⟩
  intro s p
  change G (F ((1 : A) ⊗ₜ[k] (s • p))) = φ s • G (F ((1 : A) ⊗ₜ[k] p))
  exact (congrArg G (hF s p)).trans
    ((G.map_smul ((1 : A) • φ s) (F ((1 : A) ⊗ₜ[k] p))).trans
      (congrArg (fun u : U => u • G (F ((1 : A) ⊗ₜ[k] p))) (one_smul A (φ s))))

/-- Extend the given source-coordinate equivalence and construct both the
full generator formula and its scalar compatibility. All source and target
actions are the supplied actions, with the supplied scalar-tower properties. -/
theorem exists_coordinate_realization_with_scalar
    (k A S : Type*) [CommRing k] [CommRing A] [CommRing S]
    [Algebra k A] [Algebra k S]
    {M P N U X : Type*}
    [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    [AddCommGroup P] [Module k P] [Module S P] [IsScalarTower k S P]
    [AddCommGroup N] [Module A N] [SMul U N]
    (φ : S → U) (e : M ≃ₗ[S] P) (H : A ⊗[k] P ≃ₗ[A] N)
    (F : A ⊗[k] P → X) (G : X → N)
    (hH : ∀ (a : A) (p : P), H (a ⊗ₜ[k] p) = G (F (a ⊗ₜ[k] p)))
    (hHs : ∀ (s : S) (p : P),
      H ((1 : A) ⊗ₜ[k] (s • p)) = φ s • H ((1 : A) ⊗ₜ[k] p)) :
    ∃ Z : A ⊗[k] M ≃ₗ[A] N,
      (∀ (a : A) (m : M), Z (a ⊗ₜ[k] m) = G (F (a ⊗ₜ[k] e m))) ∧
      ∀ (s : S) (m : M), Z ((1 : A) ⊗ₜ[k] (s • m)) = φ s • Z ((1 : A) ⊗ₜ[k] m) := by
  let Z : A ⊗[k] M ≃ₗ[A] N :=
    (LinearEquiv.baseChange k A M P (e.restrictScalars k)) ≪≫ₗ H
  have hZ : ∀ (a : A) (m : M), Z (a ⊗ₜ[k] m) = H (a ⊗ₜ[k] e m) := by
    intro a m
    exact congrArg H (LinearEquiv.baseChange_tmul
      (R := k) (A := A) (M := M) (N := P) (e := e.restrictScalars k) a m)
  refine ⟨Z, (fun a m => (hZ a m).trans (hH a (e m))), ?_⟩
  intro s m
  have hcoord := congrArg (fun p : P => H ((1 : A) ⊗ₜ[k] p)) (e.map_smul s m)
  exact (hZ (1 : A) (s • m)).trans
    (hcoord.trans ((hHs s (e m)).trans
      (congrArg (fun n : N => φ s • n) (hZ (1 : A) m).symm)))

end TensorProduct

namespace ModuleCat

universe w w'
open scoped ChangeOfRings

/-- Scalar extension maps preserve the canonical unit, by adjunction naturality. -/
theorem extendScalars_map_unit
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {M N : ModuleCat.{u} R} (l : M ⟶ N) (m : M) :
    (extendScalars f).map l ((extendRestrictScalarsAdj f).unit.app M m) =
      (extendRestrictScalarsAdj f).unit.app N (l m) := by
  have h := congrArg
    (fun k : M ⟶ (restrictScalars f).obj ((extendScalars f).obj N) => k m)
    ((extendRestrictScalarsAdj f).unit.naturality l)
  exact h.symm

/-- The composition comparison preserves the iterated canonical unit, including
 the actual equality transport identifying the composite ring map. -/
theorem extendScalars_comparison_hom_unit
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T)
    (w : g.comp f = h) (M : ModuleCat.{u} R) (m : M) :
    let c : extendScalars h ≅ extendScalars f ⋙ extendScalars g :=
      (eqToIso (congrArg (fun q : R →+* T => extendScalars.{u, u, u} q) w)).symm ≪≫
        extendScalarsComp f g
    c.hom.app M ((extendRestrictScalarsAdj h).unit.app M m) =
      (extendRestrictScalarsAdj g).unit.app ((extendScalars f).obj M)
        ((extendRestrictScalarsAdj f).unit.app M m) := by
  subst h
  change (extendScalarsComp f g).hom.app M
    ((extendRestrictScalarsAdj (g.comp f)).unit.app M m) = _
  exact extendScalarsComp_hom_app_one_tmul f g M m

/-- The inverse composition comparison contracts iterated canonical units. -/
theorem extendScalars_comparison_inv_unit
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T)
    (w : g.comp f = h) (M : ModuleCat.{u} R) (m : M) :
    let c : extendScalars h ≅ extendScalars f ⋙ extendScalars g :=
      (eqToIso (congrArg (fun q : R →+* T => extendScalars.{u, u, u} q) w)).symm ≪≫
        extendScalarsComp f g
    c.inv.app M
        ((extendRestrictScalarsAdj g).unit.app ((extendScalars f).obj M)
          ((extendRestrictScalarsAdj f).unit.app M m)) =
      (extendRestrictScalarsAdj h).unit.app M m := by
  let c : extendScalars h ≅ extendScalars f ⋙ extendScalars g :=
    (eqToIso (congrArg (fun q : R →+* T => extendScalars.{u, u, u} q) w)).symm ≪≫
      extendScalarsComp f g
  change c.inv.app M
    ((extendRestrictScalarsAdj g).unit.app ((extendScalars f).obj M)
      ((extendRestrictScalarsAdj f).unit.app M m)) = _
  have hunit := extendScalars_comparison_hom_unit f g h w M m
  change c.hom.app M ((extendRestrictScalarsAdj h).unit.app M m) = _ at hunit
  rw [← hunit]
  change (c.hom.app M ≫ c.inv.app M) ((extendRestrictScalarsAdj h).unit.app M m) = _
  rw [c.hom_inv_id_app]
  rfl

/-- The canonical realization comparison for a stage transition followed by
an overlap restriction. Both the triangle and square use their prescribed
ring maps and the supplied commuting equalities. -/
noncomputable def transitionRealizationComparison
    {B0 B C V U : Type u}
    [CommRing B0] [CommRing B] [CommRing C] [CommRing V] [CommRing U]
    (t : B0 →+* B) (p0 : B0 →+* V) (p : B →+* V)
    (q : B →+* C) (uC : C →+* U) (v : V →+* U)
    (ht : p.comp t = p0) (hs : uC.comp q = v.comp p) (X : ModuleCat.{u} B0) :
    (extendScalars uC).obj ((extendScalars q).obj ((extendScalars t).obj X)) ≅
      (extendScalars v).obj ((extendScalars p0).obj X) :=
  let L : ModuleCat.{u} B := (extendScalars t).obj X
  let M : ModuleCat.{u} V := (extendScalars p0).obj X
  let cChart : extendScalars p0 ≅ extendScalars t ⋙ extendScalars p :=
    (eqToIso (congrArg (fun f : B0 →+* V => extendScalars.{u, u, u} f) ht)).symm ≪≫
      extendScalarsComp t p
  let eChart : (extendScalars p).obj L ≅ M := cChart.symm.app X ≪≫ Iso.refl M
  let cNew : extendScalars (v.comp p) ≅ extendScalars q ⋙ extendScalars uC :=
    (eqToIso (congrArg (fun f : B →+* U => extendScalars.{u, u, u} f) hs)).symm ≪≫
      extendScalarsComp q uC
  cNew.symm.app L ≪≫ (extendScalarsComp p v).app L ≪≫ (extendScalars v).mapIso eChart

/-- The canonical realization of a chart module preserves its generating unit,
 with the prescribed commuting square of ring maps. -/
theorem extendScalars_realization_unit
    {B C V U : Type u} [CommRing B] [CommRing C] [CommRing V] [CommRing U]
    (q : B →+* C) (p : B →+* V) (uC : C →+* U) (v : V →+* U)
    (hcomm : uC.comp q = v.comp p)
    (X : ModuleCat.{u} B) (M : ModuleCat.{u} V)
    (e : (extendScalars p).obj X ≅ M) (x : X) :
    let c : extendScalars (v.comp p) ≅ extendScalars q ⋙ extendScalars uC :=
      (eqToIso (congrArg (fun t : B →+* U => extendScalars.{u, u, u} t) hcomm)).symm ≪≫
        extendScalarsComp q uC
    let F : (extendScalars uC).obj ((extendScalars q).obj X) ≅ (extendScalars v).obj M :=
      c.symm.app X ≪≫ (extendScalarsComp p v).app X ≪≫ (extendScalars v).mapIso e
    F.hom ((extendRestrictScalarsAdj uC).unit.app ((extendScalars q).obj X)
        ((extendRestrictScalarsAdj q).unit.app X x)) =
      (extendRestrictScalarsAdj v).unit.app M
        (e.hom ((extendRestrictScalarsAdj p).unit.app X x)) := by
  let c : extendScalars (v.comp p) ≅ extendScalars q ⋙ extendScalars uC :=
    (eqToIso (congrArg (fun t : B →+* U => extendScalars.{u, u, u} t) hcomm)).symm ≪≫
      extendScalarsComp q uC
  change (extendScalars v).map e.hom
    ((extendScalarsComp p v).hom.app X
      (c.inv.app X ((extendRestrictScalarsAdj uC).unit.app ((extendScalars q).obj X)
        ((extendRestrictScalarsAdj q).unit.app X x)))) = _
  have hcontract := extendScalars_comparison_inv_unit q uC (v.comp p) hcomm X x
  have hexpand := extendScalars_comparison_hom_unit p v (v.comp p) rfl X x
  change (extendScalarsComp p v).hom.app X
    ((extendRestrictScalarsAdj (v.comp p)).unit.app X x) = _ at hexpand
  exact (congrArg
    (fun z : (extendScalars (v.comp p)).obj X =>
      (extendScalars v).map e.hom ((extendScalarsComp p v).hom.app X z))
    hcontract).trans
    ((congrArg
      (fun z : (extendScalars v).obj ((extendScalars p).obj X) =>
        (extendScalars v).map e.hom z) hexpand).trans
      (extendScalars_map_unit v e.hom ((extendRestrictScalarsAdj p).unit.app X x)))

/-- An S-linear map on a scalar extension has its value on s⊗q determined by
 its already known value on the canonical unit tensor of q. -/
theorem linearMap_tmul_of_unit
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (Q : ModuleCat.{u} R)
    {N : Type w} [AddCommGroup N] [Module S N]
    (e : (extendScalars f).obj Q →ₗ[S] N) (q : Q) {y : N}
    (hunit : e ((extendRestrictScalarsAdj f).unit.app Q q) = y) (s : S) :
    e (s ⊗ₜ[R,f] q) = s • y := by
  let uq : (extendScalars f).obj Q := (extendRestrictScalarsAdj f).unit.app Q q
  have hs : s • uq = (s * 1) ⊗ₜ[R,f] q :=
    ExtendScalars.smul_tmul (f := f) (M := Q) s (1 : S) q
  have hfactor : (s ⊗ₜ[R,f] q : (extendScalars f).obj Q) = s • uq :=
    (congrArg (fun t : S => (t ⊗ₜ[R,f] q : (extendScalars f).obj Q))
      (mul_one s)).symm.trans hs.symm
  exact (congrArg e hfactor).trans
    ((e.map_smul s uq).trans (congrArg (fun n : N => s • n) hunit))

/-- Change a chart realization across a commuting ring square. The two new
 realization isomorphisms are constructed, their canonical comparison formula
 is proved, and the original restriction law is transported to every pure
 generator. No algebra action is installed beyond the fixed-map ModuleCat owners. -/
theorem exists_realization_of_commuting_square
    {B C V U : Type u} [CommRing B] [CommRing C] [CommRing V] [CommRing U]
    (q : B →+* C) (p : B →+* V) (uC : C →+* U) (v : V →+* U)
    (hcomm : uC.comp q = v.comp p)
    (X : ModuleCat.{u} B) (M : ModuleCat.{u} V)
    {N : Type w} [AddCommGroup N] [Module V N]
    {O : Type w'} [AddCommGroup O] [Module U O]
    (e : (extendScalars p).obj X ≅ M)
    (I : M ≃ₗ[V] N) (J : (extendScalars v).obj M ≃ₗ[U] O)
    (r : N → O)
    (hJ : ∀ m : M, J ((extendRestrictScalarsAdj v).unit.app M m) = r (I m)) :
    let c : extendScalars (v.comp p) ≅ extendScalars q ⋙ extendScalars uC :=
      (eqToIso (congrArg (fun t : B →+* U => extendScalars.{u, u, u} t) hcomm)).symm ≪≫
        extendScalarsComp q uC
    let F : (extendScalars uC).obj ((extendScalars q).obj X) ≅ (extendScalars v).obj M :=
      c.symm.app X ≪≫ (extendScalarsComp p v).app X ≪≫ (extendScalars v).mapIso e
    ∃ (newI : (extendScalars p).obj X ≃ₗ[V] N)
      (Xi : (extendScalars uC).obj ((extendScalars q).obj X) ≃ₗ[U] O),
      (∀ z : (extendScalars p).obj X, newI z = I (e.hom z)) ∧
      (∀ z : (extendScalars uC).obj ((extendScalars q).obj X), Xi z = J (F.hom z)) ∧
      ∀ (a : U) (x : X),
        Xi (a ⊗ₜ[C,uC] (show (extendScalars q).obj X from
          (extendRestrictScalarsAdj q).unit.app X x)) =
        a • r (newI ((extendRestrictScalarsAdj p).unit.app X x)) := by
  let c : extendScalars (v.comp p) ≅ extendScalars q ⋙ extendScalars uC :=
    (eqToIso (congrArg (fun t : B →+* U => extendScalars.{u, u, u} t) hcomm)).symm ≪≫
      extendScalarsComp q uC
  let F : (extendScalars uC).obj ((extendScalars q).obj X) ≅ (extendScalars v).obj M :=
    c.symm.app X ≪≫ (extendScalarsComp p v).app X ≪≫ (extendScalars v).mapIso e
  let newI : (extendScalars p).obj X ≃ₗ[V] N := e.toLinearEquiv ≪≫ₗ I
  let Xi : (extendScalars uC).obj ((extendScalars q).obj X) ≃ₗ[U] O :=
    F.toLinearEquiv ≪≫ₗ J
  refine ⟨newI, Xi, (fun z => rfl), (fun z => rfl), ?_⟩
  intro a x
  have hunit : Xi ((extendRestrictScalarsAdj uC).unit.app ((extendScalars q).obj X)
      (show (extendScalars q).obj X from (extendRestrictScalarsAdj q).unit.app X x)) =
      r (newI ((extendRestrictScalarsAdj p).unit.app X x)) :=
    (congrArg J (extendScalars_realization_unit q p uC v hcomm X M e x)).trans
      (hJ (e.hom ((extendRestrictScalarsAdj p).unit.app X x)))
  exact linearMap_tmul_of_unit uC ((extendScalars q).obj X) Xi.toLinearMap
    (show (extendScalars q).obj X from (extendRestrictScalarsAdj q).unit.app X x) hunit a

/-- Construct both realizations after a stage transition and prove their
canonical comparison formula and overlap generator law from the original
restriction law. All intermediate scalar extensions use fixed ring-map owners. -/
theorem exists_realization_after_transition
    {B0 B C V U : Type u}
    [CommRing B0] [CommRing B] [CommRing C] [CommRing V] [CommRing U]
    (t : B0 →+* B) (p0 : B0 →+* V) (p : B →+* V)
    (q : B →+* C) (uC : C →+* U) (v : V →+* U)
    (ht : p.comp t = p0) (hs : uC.comp q = v.comp p) (X : ModuleCat.{u} B0)
    {N : Type w} [AddCommGroup N] [Module V N]
    {O : Type w'} [AddCommGroup O] [Module U O]
    (I : (extendScalars p0).obj X ≃ₗ[V] N)
    (J : (extendScalars v).obj ((extendScalars p0).obj X) ≃ₗ[U] O)
    (r : N → O)
    (hJ : ∀ m : (extendScalars p0).obj X,
      J ((extendRestrictScalarsAdj v).unit.app ((extendScalars p0).obj X) m) = r (I m)) :
    let L : ModuleCat.{u} B := (extendScalars t).obj X
    ∃ (newI : (extendScalars p).obj L ≃ₗ[V] N)
      (Xi : (extendScalars uC).obj ((extendScalars q).obj L) ≃ₗ[U] O),
      (∀ z : (extendScalars uC).obj ((extendScalars q).obj L),
        Xi z = J ((transitionRealizationComparison t p0 p q uC v ht hs X).hom z)) ∧
      ∀ (a : U) (x : L),
        Xi (a ⊗ₜ[C,uC] (show (extendScalars q).obj L from
          (extendRestrictScalarsAdj q).unit.app L x)) =
        a • r (newI ((extendRestrictScalarsAdj p).unit.app L x)) := by
  let L : ModuleCat.{u} B := (extendScalars t).obj X
  let M : ModuleCat.{u} V := (extendScalars p0).obj X
  let cChart : extendScalars p0 ≅ extendScalars t ⋙ extendScalars p :=
    (eqToIso (congrArg (fun f : B0 →+* V => extendScalars.{u, u, u} f) ht)).symm ≪≫
      extendScalarsComp t p
  let eChart : (extendScalars p).obj L ≅ M := cChart.symm.app X ≪≫ Iso.refl M
  obtain ⟨newI, Xi, _, hXi, hgen⟩ :=
    exists_realization_of_commuting_square q p uC v hs L M eChart I J r hJ
  exact ⟨newI, Xi, hXi, hgen⟩

/-- Construct the coherent chart and overlap realizations in the same
stage-transition scope. The native comparison is retained only as the proved
interface needed by the supplied common-stage square. -/
theorem exists_algebraTensor_realization_after_transition
    {B0 B C V U : Type u}
    [CommRing B0] [CommRing B] [CommRing C] [CommRing V] [CommRing U]
    (t : B0 →+* B) (p0 : B0 →+* V) (p : B →+* V)
    (q : B →+* C) (g : C →+* U) (v : V →+* U)
    (ht : p.comp t = p0) (hs : g.comp q = v.comp p) (X : ModuleCat.{u} B0)
    {N : Type w} [AddCommGroup N] [Module V N]
    {O : Type w'} [AddCommGroup O] [Module U O]
    (I : (extendScalars p0).obj X ≃ₗ[V] N)
    (J : (extendScalars v).obj ((extendScalars p0).obj X) ≃ₗ[U] O)
    (r : N → O)
    (hJ : ∀ m : (extendScalars p0).obj X,
      J ((extendRestrictScalarsAdj v).unit.app ((extendScalars p0).obj X) m) = r (I m)) :
    let L : ModuleCat.{u} B := (extendScalars t).obj X
    let Q : ModuleCat.{u} C := (extendScalars q).obj L
    ∃ (newI : algebraTensorObj p L ≃ₗ[V] N)
      (Xi : algebraTensorObj g Q ≃ₗ[U] O)
      (XiNative : (extendScalars g).obj Q ≃ₗ[U] O),
      (∀ z : (extendScalars g).obj Q,
        XiNative z = J ((transitionRealizationComparison t p0 p q g v ht hs X).hom z)) ∧
      (∀ z : (extendScalars g).obj Q, Xi (extendScalarsAlgebraTensorEquiv g Q z) = XiNative z) ∧
      ∀ (a : U) (x : L),
        Xi (algebraTensorTmul g Q a (show Q from (extendRestrictScalarsAdj q).unit.app L x)) =
        a • r (newI (algebraTensorTmul p L (1 : V) x)) := by
  let L : ModuleCat.{u} B := (extendScalars t).obj X
  obtain ⟨nativeI, nativeXi, hReal, hGen⟩ :=
    exists_realization_after_transition t p0 p q g v ht hs X I J r hJ
  obtain ⟨newI, Xi, _, hXi, hRawGen⟩ :=
    exists_algebraTensor_realization_pair p q g L nativeI nativeXi r hGen
  exact ⟨newI, Xi, nativeXi, hReal, hXi, hRawGen⟩

end ModuleCat

namespace ModuleCat

universe w w'
open scoped ChangeOfRings

/-- Realize the chart and overlap maps already constructed by descent.
The supplied unit law is the proved law of those actual maps; no canonical
comparison is recomputed at the caller. -/
theorem exists_algebraTensor_realization_of_maps
    {B C V U : Type u} [CommRing B] [CommRing C] [CommRing V] [CommRing U]
    (p : B →+* V) (q : B →+* C) (g : C →+* U) (v : V →+* U)
    (X : ModuleCat.{u} B) (M : ModuleCat.{u} V)
    {N : Type w} [AddCommGroup N] [Module V N]
    {O : Type w'} [AddCommGroup O] [Module U O]
    (e : (extendScalars p).obj X ≅ M)
    (F : (extendScalars g).obj ((extendScalars q).obj X) ≅ (extendScalars v).obj M)
    (I : M ≃ₗ[V] N) (J : (extendScalars v).obj M ≃ₗ[U] O) (r : N → O)
    (hF : ∀ x : X,
      F.hom ((extendRestrictScalarsAdj g).unit.app ((extendScalars q).obj X)
        (show (extendScalars q).obj X from (extendRestrictScalarsAdj q).unit.app X x)) =
      (extendRestrictScalarsAdj v).unit.app M
        (e.hom ((extendRestrictScalarsAdj p).unit.app X x)))
    (hJ : ∀ m : M, J ((extendRestrictScalarsAdj v).unit.app M m) = r (I m)) :
    let Q : ModuleCat.{u} C := (extendScalars q).obj X
    ∃ (newI : algebraTensorObj p X ≃ₗ[V] N) (Xi : algebraTensorObj g Q ≃ₗ[U] O)
      (XiNative : (extendScalars g).obj Q ≃ₗ[U] O),
      (∀ z : (extendScalars g).obj Q, XiNative z = J (F.hom z)) ∧
      (∀ z : (extendScalars g).obj Q, Xi (extendScalarsAlgebraTensorEquiv g Q z) = XiNative z) ∧
      ∀ (a : U) (x : X),
        Xi (algebraTensorTmul g Q a (show Q from (extendRestrictScalarsAdj q).unit.app X x)) =
        a • r (newI (algebraTensorTmul p X (1 : V) x)) := by
  let nativeI : (extendScalars p).obj X ≃ₗ[V] N := e.toLinearEquiv ≪≫ₗ I
  let nativeXi : (extendScalars g).obj ((extendScalars q).obj X) ≃ₗ[U] O :=
    F.toLinearEquiv ≪≫ₗ J
  have hGen : ∀ (a : U) (x : X),
      nativeXi (a ⊗ₜ[C,g] (show (extendScalars q).obj X from
        (extendRestrictScalarsAdj q).unit.app X x)) =
      a • r (nativeI ((extendRestrictScalarsAdj p).unit.app X x)) := by
    intro a x
    have hunit : nativeXi ((extendRestrictScalarsAdj g).unit.app ((extendScalars q).obj X)
        (show (extendScalars q).obj X from (extendRestrictScalarsAdj q).unit.app X x)) =
        r (nativeI ((extendRestrictScalarsAdj p).unit.app X x)) :=
      (congrArg J (hF x)).trans (hJ (e.hom ((extendRestrictScalarsAdj p).unit.app X x)))
    exact linearMap_tmul_of_unit g ((extendScalars q).obj X) nativeXi.toLinearMap
      (show (extendScalars q).obj X from (extendRestrictScalarsAdj q).unit.app X x) hunit a
  obtain ⟨newI, Xi, _, hXi, hRawGen⟩ :=
    exists_algebraTensor_realization_pair p q g X nativeI nativeXi r hGen
  exact ⟨newI, Xi, nativeXi, (fun _ => rfl), hXi, hRawGen⟩

end ModuleCat
