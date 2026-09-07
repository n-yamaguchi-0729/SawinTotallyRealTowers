import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.Map
import ProCGroups.CompletedGroupAlgebra.InClassFunctoriality.Maps
import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteComparison

set_option autoImplicit false

/-!
# Completed Group Algebra / All Finite Functoriality / Within a Class Naturality

This module proves that the comparison between the all-finite and \(C\)-indexed completions is
natural for continuous group homomorphisms, in ring-, algebra-, and equivalence-valued forms.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
Continuous ring homomorphisms from the all-finite completed group algebra to a \(C\)-indexed
completed group algebra are determined by their values on the dense abstract group algebra.
-/
theorem completedGroupAlgebraRingHomToInClass_ext_of_comp_toCompleted
    (C : ProCGroups.FiniteGroupClass.{v})
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    {f g : CompletedGroupAlgebraCarrier R G →+* CompletedGroupAlgebraInClass C R H}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : f.comp (toCompletedGroupAlgebraRingHom R G) =
      g.comp (toCompletedGroupAlgebraRingHom R G)) :
    f = g := by
  let : T2Space (CompletedGroupAlgebraInClass C R H) :=
    completedGroupAlgebraInClass_t2Space (R := R) (G := H) C
  have hdense : DenseRange (toCompletedGroupAlgebraRingHom R G) :=
    denseRange_toCompletedGroupAlgebraRingHom (R := R) (G := G)
  have hcomp : (f : CompletedGroupAlgebraCarrier R G → CompletedGroupAlgebraInClass C R H) ∘
        (toCompletedGroupAlgebraRingHom R G) =
      (g : CompletedGroupAlgebraCarrier R G → CompletedGroupAlgebraInClass C R H) ∘
        (toCompletedGroupAlgebraRingHom R G) := by
    funext x
    exact congrFun (congrArg DFunLike.coe hfg) x
  have hfun : (f : CompletedGroupAlgebraCarrier R G → CompletedGroupAlgebraInClass C R H) = g :=
    DenseRange.equalizer hdense hf hg hcomp
  exact RingHom.ext fun x => congrFun hfun x

/--
Naturality of the comparison from the all-finite completed group algebra to the \(C\)-indexed
completed group algebra in the group variable.
-/
theorem completedGroupAlgebraToInClassRingHom_naturality
    (C : ProCGroups.FiniteGroupClass.{v})
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ).comp
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C ) =
      (completedGroupAlgebraToInClassRingHom (R := R) (G := H) C ).comp
        (completedGroupAlgebraMap (G := G) (H := H) R φ hφ) := by
  apply completedGroupAlgebraRingHomToInClass_ext_of_comp_toCompleted
    (R := R) (G := G) (H := H) C
  · exact (continuous_completedGroupAlgebraMapInClass (R := R) (G := G) (H := H)
      C hHer φ hφ).comp
        (continuous_completedGroupAlgebraToInClass (R := R) (G := G) C )
  · exact (continuous_completedGroupAlgebraToInClass (R := R) (G := H) C ).comp
      (continuous_completedGroupAlgebraMap (R := R) (G := G) (H := H) φ hφ)
  · apply RingHom.ext
    intro x
    have htoG := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraToInClass_comp_toCompletedGroupAlgebra
          (R := R) (G := G) C ))
      x
    have hmapC := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMapInClass_comp_toCompletedGroupAlgebraInClass
          (R := R) (G := G) (H := H) C hHer φ hφ))
      x
    have hmapAll := congrFun
      (congrArg DFunLike.coe
          (completedGroupAlgebraMap_comp_toCompletedGroupAlgebra
            (R := R) (G := G) (H := H) φ hφ))
      x
    have htoH := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraToInClass_comp_toCompletedGroupAlgebra
          (R := R) (G := H) C ))
      (MonoidAlgebra.mapDomainRingHom R φ x)
    calc
      ((((completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ).comp
          (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C )).comp
          (toCompletedGroupAlgebraRingHom R G)) x) =
        completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ
          ((completedGroupAlgebraToInClassRingHom (R := R) (G := G) C )
            (toCompletedGroupAlgebraRingHom R G x)) := rfl
      _ =
        completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ
          (toCompletedGroupAlgebraInClassRingHom C R G x) := by
          exact congrArg (completedGroupAlgebraMapInClass (G := G) (H := H)
            C hHer R φ hφ) (by
              exact htoG)
      _ =
        toCompletedGroupAlgebraInClassRingHom C R H
          (MonoidAlgebra.mapDomainRingHom R φ x) := by
          simpa [RingHom.comp_apply] using hmapC
      _ =
        completedGroupAlgebraToInClassRingHom (R := R) (G := H) C
          (toCompletedGroupAlgebraRingHom R H (MonoidAlgebra.mapDomainRingHom R φ x)) := by
          have htoH' :
              completedGroupAlgebraToInClassRingHom (R := R) (G := H) C
                  (toCompletedGroupAlgebraRingHom R H
                    (MonoidAlgebra.mapDomainRingHom R φ x)) =
                toCompletedGroupAlgebraInClassRingHom C R H
                  (MonoidAlgebra.mapDomainRingHom R φ x) := by
            exact htoH
          exact htoH'.symm
      _ =
        completedGroupAlgebraToInClassRingHom (R := R) (G := H) C
          (completedGroupAlgebraMap (G := G) (H := H) R φ hφ
            (toCompletedGroupAlgebraRingHom R G x)) := by
          have hmapAll' :
              completedGroupAlgebraMap (G := G) (H := H) R φ hφ
                  (toCompletedGroupAlgebraRingHom R G x) =
                toCompletedGroupAlgebraRingHom R H (MonoidAlgebra.mapDomainRingHom R φ x) := by
            exact hmapAll
          exact congrArg (completedGroupAlgebraToInClassRingHom (R := R) (G := H) C )
            hmapAll'.symm
      _ =
        ((((completedGroupAlgebraToInClassRingHom (R := R) (G := H) C ).comp
          (completedGroupAlgebraMap (G := G) (H := H) R φ hφ)).comp
          (toCompletedGroupAlgebraRingHom R G)) x) := rfl

/--
Algebra-homomorphism form of the naturality of the comparison from the all-finite completed
group algebra to the \(C\)-indexed completed group algebra.
-/
theorem completedGroupAlgebraToInClassAlgHom_naturality
    (C : ProCGroups.FiniteGroupClass.{v})
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraMapAlgHomInClass (G := G) (H := H) C hHer R φ hφ).comp
        (completedGroupAlgebraToInClassAlgHom (R := R) (G := G) C ) =
      (completedGroupAlgebraToInClassAlgHom (R := R) (G := H) C ).comp
        (completedGroupAlgebraMapAlgHom (G := G) (H := H) R φ hφ) := by
  apply AlgHom.ext
  intro x
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraToInClassRingHom_naturality
        (R := R) (G := G) (H := H) C hHer φ hφ))
    x
  simpa using h

/--
Naturality of the inverse comparison from the \(C\)-indexed completed group algebra back to the
all-finite completed group algebra, for pro-\(C\) groups.
-/
theorem completedGroupAlgebraFromInClassRingHom_naturality
    (C : ProCGroups.FiniteGroupClass.{v})
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (hG : HasOpenNormalBasisInClass C G) (hH : HasOpenNormalBasisInClass C H)
    (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraMap (G := G) (H := H) R φ hφ).comp
        (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG) =
      (completedGroupAlgebraFromInClassRingHom (R := R) (G := H) C hForm hH).comp
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ) := by
  apply RingHom.ext
  intro x
  rcases completedGroupAlgebraToInClass_surjective (R := R) (G := G) C hForm hG x with
    ⟨y, rfl⟩
  have hnat := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraToInClassRingHom_naturality
        (R := R) (G := G) (H := H) C hHer φ hφ))
    y
  calc
    ((completedGroupAlgebraMap (G := G) (H := H) R φ hφ).comp
        (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG))
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C y)
        =
      completedGroupAlgebraMap (G := G) (H := H) R φ hφ
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hForm hG
          (completedGroupAlgebraToInClass (R := R) (G := G) C y)) := rfl
    _ =
      completedGroupAlgebraMap (G := G) (H := H) R φ hφ y := by
        rw [completedGroupAlgebraFromInClass_toInClass]
    _ =
      completedGroupAlgebraFromInClass (R := R) (G := H) C hForm hH
        (completedGroupAlgebraToInClass (R := R) (G := H) C
          (completedGroupAlgebraMap (G := G) (H := H) R φ hφ y)) := by
        rw [completedGroupAlgebraFromInClass_toInClass]
    _ =
      completedGroupAlgebraFromInClass (R := R) (G := H) C hForm hH
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ
          (completedGroupAlgebraToInClass (R := R) (G := G) C y)) := by
        exact congrArg (completedGroupAlgebraFromInClass (R := R) (G := H) C hForm hH)
          hnat.symm
    _ =
      ((completedGroupAlgebraFromInClassRingHom (R := R) (G := H) C hForm hH).comp
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ))
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C y) := rfl

/--
Algebra-homomorphism form of the naturality of the inverse comparison from the \(C\)-indexed
completed group algebra back to the all-finite completed group algebra.
-/
theorem completedGroupAlgebraFromInClassAlgHom_naturality
    (C : ProCGroups.FiniteGroupClass.{v})
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (hG : HasOpenNormalBasisInClass C G) (hH : HasOpenNormalBasisInClass C H)
    (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraMapAlgHom (G := G) (H := H) R φ hφ).comp
        (completedGroupAlgebraFromInClassAlgHom (R := R) (G := G) C hForm hG) =
      (completedGroupAlgebraFromInClassAlgHom (R := R) (G := H) C hForm hH).comp
        (completedGroupAlgebraMapAlgHomInClass (G := G) (H := H) C hHer R φ hφ) := by
  apply AlgHom.ext
  intro x
  have h := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraFromInClassRingHom_naturality
        (R := R) (G := G) (H := H) C hHer hForm hG hH φ hφ))
    x
  simpa using h

/-- The ring equivalence from all-finite to in-class completions is natural in the group. -/
@[simp]
theorem completedGroupAlgebraInClassRingEquiv_naturality
    (C : ProCGroups.FiniteGroupClass.{v})
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (hG : HasOpenNormalBasisInClass C G) (hH : HasOpenNormalBasisInClass C H)
    (φ : G →* H) (hφ : Continuous φ) (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ
        (completedGroupAlgebraInClassRingEquiv (R := R) (G := G) C hForm hG x) =
      completedGroupAlgebraInClassRingEquiv (R := R) (G := H) C hForm hH
        (completedGroupAlgebraMap (G := G) (H := H) R φ hφ x) := by
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraToInClassRingHom_naturality
        (R := R) (G := G) (H := H) C hHer φ hφ))
    x
  simpa [RingHom.comp_apply] using h

/-- The inverse ring equivalence from in-class to all-finite completions is natural in the group. -/
@[simp]
theorem completedGroupAlgebraInClassRingEquiv_symm_naturality
    (C : ProCGroups.FiniteGroupClass.{v})
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (hG : HasOpenNormalBasisInClass C G) (hH : HasOpenNormalBasisInClass C H)
    (φ : G →* H) (hφ : Continuous φ) (x : CompletedGroupAlgebraInClass C R G) :
    completedGroupAlgebraMap (G := G) (H := H) R φ hφ
        ((completedGroupAlgebraInClassRingEquiv (R := R) (G := G) C hForm hG).symm x) =
      (completedGroupAlgebraInClassRingEquiv (R := R) (G := H) C hForm hH).symm
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hHer R φ hφ x) := by
  have h := congrFun
      (congrArg DFunLike.coe
      (completedGroupAlgebraFromInClassRingHom_naturality
        (R := R) (G := G) (H := H) C hHer hForm hG hH φ hφ))
    x
  simpa [RingHom.comp_apply] using h

/-- The algebra equivalence from all-finite to in-class completions is natural in the group. -/
@[simp]
theorem completedGroupAlgebraInClassAlgEquiv_naturality
    (C : ProCGroups.FiniteGroupClass.{v})
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (hG : HasOpenNormalBasisInClass C G) (hH : HasOpenNormalBasisInClass C H)
    (φ : G →* H) (hφ : Continuous φ) (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraMapAlgHomInClass (G := G) (H := H) C hHer R φ hφ
        (completedGroupAlgebraInClassAlgEquiv (R := R) (G := G) C hForm hG x) =
      completedGroupAlgebraInClassAlgEquiv (R := R) (G := H) C hForm hH
        (completedGroupAlgebraMapAlgHom (G := G) (H := H) R φ hφ x) := by
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraToInClassAlgHom_naturality
        (R := R) (G := G) (H := H) C hHer φ hφ))
    x
  simpa using h

/--
The inverse algebra equivalence from in-class to all-finite completions is natural in the group.
-/
@[simp]
theorem completedGroupAlgebraInClassAlgEquiv_symm_naturality
    (C : ProCGroups.FiniteGroupClass.{v})
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (hG : HasOpenNormalBasisInClass C G) (hH : HasOpenNormalBasisInClass C H)
    (φ : G →* H) (hφ : Continuous φ) (x : CompletedGroupAlgebraInClass C R G) :
    completedGroupAlgebraMapAlgHom (G := G) (H := H) R φ hφ
        ((completedGroupAlgebraInClassAlgEquiv (R := R) (G := G) C hForm hG).symm x) =
      (completedGroupAlgebraInClassAlgEquiv (R := R) (G := H) C hForm hH).symm
        (completedGroupAlgebraMapAlgHomInClass (G := G) (H := H) C hHer R φ hφ x) := by
  have h := congrFun
      (congrArg DFunLike.coe
      (completedGroupAlgebraFromInClassAlgHom_naturality
        (R := R) (G := G) (H := H) C hHer hForm hG hH φ hφ))
    x
  simpa using h

end

end CompletedGroupAlgebra
