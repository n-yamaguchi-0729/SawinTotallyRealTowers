/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Topology.FiniteModelPrincipalStalk
import Nyll.SchemeTheory.Topology.FiniteModelSheafDiagram
import Nyll.SchemeTheory.Topology.FiniteModelStalkColimit
import Nyll.SchemeTheory.Topology.SheafApproximationGerms
import Nyll.SchemeTheory.Topology.SheafPullbackStalks

/-!
# Stalks of the actual finite-model approximation diagram

The stalk of `q⁻¹q_*F` is identified with sections of `F` on the inverse
image of the finite model's principal neighborhood. The comparison uses
the actual principal-open germ and the actual inverse-image stalk
isomorphism, so its naturality can be checked on those germs.

The Lean constructions and proofs are original.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Topology Opposite

namespace SchemeTheory.CompactOpenFiniteModel

variable {X : TopCat.{u}}

/-- Principal-neighborhood sections identify with the actual stalk of
each finite-model inverse-image/direct-image approximation. -/
def stageStalkIso
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
    (x : X) (S : Finset (CompactOpens X)) :
    (sectionDiagram F x).obj S ≅
      TopCat.Presheaf.stalk ((sheafDiagram F).obj S).obj x :=
  principalOpenStalkIso ((TopCat.Sheaf.pushforward (Type u) (quotient S)).obj F).obj
      (quotient S x) ≪≫
    sheafStalkPullbackIso (quotient S)
      ((TopCat.Sheaf.pushforward (Type u) (quotient S)).obj F) x

/-- The stage stalk comparisons form a natural isomorphism: forgetting
compact-open coordinates acts by ordinary restriction of sections. -/
def stalkDiagramIso
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) (x : X) :
    sectionDiagram F x ≅ sheafDiagram F ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) (Type u) ⋙
        TopCat.Presheaf.stalkFunctor (Type u) x :=
  NatIso.ofComponents (stageStalkIso F x) (fun {S T} h => by
    let q : X ⟶ Space T := quotient T
    let p : Space T ⟶ Space S := refinement (leOfHom h)
    let U : Opens (Space S) := Alexandrov.principalOpen (quotient S x)
    let V : Opens (Space T) := Alexandrov.principalOpen (quotient T x)
    let i : V ⟶ (Opens.map p).obj U := homOfLE
      ((Alexandrov.principalOpen_le_iff ((Opens.map p).obj U)).mpr
        (show p (quotient T x) ∈ U from
          Alexandrov.self_mem_principalOpen (quotient S x)))
    exact (sheafApproximationTransition_germ q p F x U V i
      (Alexandrov.self_mem_principalOpen (quotient T x))).symm)

/-- The natural stage isomorphisms identify the actual counit cocone on
stalks with the ordinary germ cocone of principal-neighborhood sections. -/
theorem stageStalkIso_hom_counit
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
    (x : X) (S : Finset (CompactOpens X)) :
    (stageStalkIso F x S).hom ≫
        (TopCat.Presheaf.stalkFunctor (Type u) x).map
          ((sheafCocone F).ι.app S).hom =
      (sectionCocone F x).ι.app S := by
  let q : X ⟶ Space S := quotient S
  let U : Opens (Space S) := Alexandrov.principalOpen (q x)
  let V : Opens X := (Opens.map q).obj U
  let P : X.Presheaf (Type u) := F.obj
  let G : CategoryTheory.Sheaf (Opens.grothendieckTopology (Space S)) (Type u) :=
    (TopCat.Sheaf.pushforward (Type u) q).obj F
  let Q : (Space S).Presheaf (Type u) := G.obj
  let A : X.Presheaf (Type u) := ((TopCat.Sheaf.pullback (Type u) q).obj G).obj
  let e : Q.stalk (q x) ≅ A.stalk x := sheafStalkPullbackIso q G x
  let g : P.obj (op V) ⟶ Q.stalk (q x) := Q.germ U (q x)
    (Alexandrov.self_mem_principalOpen (q x))
  let m : A.stalk x ⟶ P.stalk x :=
    (TopCat.Presheaf.stalkFunctor (Type u) x).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) q).counit.app F).hom
  let c : Q.stalk (q x) ⟶ P.stalk x := TopCat.Presheaf.stalkPushforward (Type u) q P x
  let v : P.obj (op V) ⟶ P.stalk x := P.germ V x
    (Alexandrov.self_mem_principalOpen (q x))
  have hc : e.hom ≫ m = c := sheafStalkPullbackIso_hom_counit q F x
  have hg : g ≫ c = v := TopCat.Presheaf.stalkPushforward_germ (Type u) q P U x
    (Alexandrov.self_mem_principalOpen (q x))
  change (g ≫ e.hom) ≫ m = v
  exact (Category.assoc g e.hom m).trans ((congrArg (fun k => g ≫ k) hc).trans hg)

end SchemeTheory.CompactOpenFiniteModel
