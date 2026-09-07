import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteComparison
import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.GroupLike
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

set_option autoImplicit false

/-!
# Completed Group Algebra / Universal Property / Basic

This module packages canonical completed-group-algebra models by their finite-stage cone and
inverse-limit universal property, derives comparison equivalences, and develops the continuous
group-like map and its spanning properties.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w z

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Certificate that a profinite ring realizes the inverse limit of the finite group algebras
`R[G/U]` for bundled profinite coefficients and group.

The data are the bundled finite-stage ring homomorphisms, their compatibility with the specified
algebraic map, and the inverse-limit universal property.  Continuity and transition compatibility
of the projections are contained in `isInverseLimit`.  In particular, no comparison with the
canonical carrier is assumed: the comparison homeomorphism and ring equivalence below are derived
from the universal property.  Profiniteness is inherited from the three bundled objects rather
than repeated as certificate fields. -/
structure CanonicalCompletedGroupAlgebraModel
    (R : ProfiniteCommRing.{u}) (G : ProfiniteGrp.{v}) (RG : ProfiniteRing.{w})
    (algebraicMap : CompletedGroupAlgebraNaturalSource R G →+* RG) where
  /-- The projection from the candidate model to each finite group-algebra stage. -/
  stageProjection : ∀ U : CompletedGroupAlgebraIndex G,
    RG →+* CompletedGroupAlgebraStage R G U
  /-- Each stage projection agrees with the canonical stage map on the algebraic source. -/
  stageProjection_comp_algebraicMap : ∀ U : CompletedGroupAlgebraIndex G,
    (stageProjection U).comp algebraicMap = completedGroupAlgebraNaturalSourceStageMap R G U
  /-- The stage projections exhibit the candidate carrier as the inverse limit. -/
  isInverseLimit :
    (completedGroupAlgebraSystem R G).IsInverseLimit
      (fun U x => stageProjection U x)

namespace CanonicalCompletedGroupAlgebraModel

variable {R : ProfiniteCommRing.{u}} {G : ProfiniteGrp.{v}}
variable {RG : ProfiniteRing.{w}}
variable {algebraicMap : CompletedGroupAlgebraNaturalSource R G →+* RG}

/-- Each model projection is continuous, as a consequence of the inverse-limit witness. -/
theorem stageProjection_continuous
    (h : CanonicalCompletedGroupAlgebraModel R G RG algebraicMap)
    (U : CompletedGroupAlgebraIndex G) :
    letI : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
      (completedGroupAlgebraSystem R G).topologicalSpace U
    Continuous (h.stageProjection U) := by
  let : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    (completedGroupAlgebraSystem R G).topologicalSpace U
  exact h.isInverseLimit.continuous_proj U

/-- Model projections commute with finite-stage transition ring homomorphisms. -/
theorem stageProjection_compatible
    (h : CanonicalCompletedGroupAlgebraModel R G RG algebraicMap)
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (completedGroupAlgebraTransition R G hUV).comp (h.stageProjection V) =
      h.stageProjection U := by
  apply RingHom.ext
  intro x
  change
    (completedGroupAlgebraSystem R G).map hUV (h.stageProjection V x) =
      h.stageProjection U x
  exact congrFun (h.isInverseLimit.compatible U V hUV) x

/-- The comparison homeomorphism with the concrete inverse-limit carrier, derived solely from
the two inverse-limit universal properties. -/
noncomputable def comparisonHomeomorph
    (h : CanonicalCompletedGroupAlgebraModel R G RG algebraicMap) :
    RG ≃ₜ CompletedGroupAlgebraCarrier R G :=
  h.isInverseLimit.homeomorphToInverseLimit

/-- The derived comparison is characterized by every finite-stage projection. -/
@[simp]
theorem completedGroupAlgebraProjection_comparisonHomeomorph
    (h : CanonicalCompletedGroupAlgebraModel R G RG algebraicMap)
    (U : CompletedGroupAlgebraIndex G) (x : RG) :
    completedGroupAlgebraProjection R G U (h.comparisonHomeomorph x) =
      h.stageProjection U x := by
  rfl

/-- The comparison homeomorphism preserves the ring operations because all model projections are
ring homomorphisms. -/
noncomputable def comparisonRingEquiv
    (h : CanonicalCompletedGroupAlgebraModel R G RG algebraicMap) :
    RG ≃+* CompletedGroupAlgebraCarrier R G where
  toEquiv := h.comparisonHomeomorph.toEquiv
  map_add' x y := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    change completedGroupAlgebraProjection R G U (h.comparisonHomeomorph (x + y)) =
      completedGroupAlgebraProjection R G U
        (h.comparisonHomeomorph x + h.comparisonHomeomorph y)
    calc
      completedGroupAlgebraProjection R G U (h.comparisonHomeomorph (x + y)) =
          h.stageProjection U (x + y) :=
        h.completedGroupAlgebraProjection_comparisonHomeomorph U (x + y)
      _ = h.stageProjection U x + h.stageProjection U y := map_add _ x y
      _ = completedGroupAlgebraProjection R G U (h.comparisonHomeomorph x) +
          completedGroupAlgebraProjection R G U (h.comparisonHomeomorph y) :=
        congrArg₂ (· + ·)
          (h.completedGroupAlgebraProjection_comparisonHomeomorph U x).symm
          (h.completedGroupAlgebraProjection_comparisonHomeomorph U y).symm
      _ = completedGroupAlgebraProjection R G U
          (h.comparisonHomeomorph x + h.comparisonHomeomorph y) :=
        (map_add (completedGroupAlgebraProjection R G U) _ _).symm
  map_mul' x y := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    change completedGroupAlgebraProjection R G U (h.comparisonHomeomorph (x * y)) =
      completedGroupAlgebraProjection R G U
        (h.comparisonHomeomorph x * h.comparisonHomeomorph y)
    calc
      completedGroupAlgebraProjection R G U (h.comparisonHomeomorph (x * y)) =
          h.stageProjection U (x * y) :=
        h.completedGroupAlgebraProjection_comparisonHomeomorph U (x * y)
      _ = h.stageProjection U x * h.stageProjection U y := map_mul _ x y
      _ = completedGroupAlgebraProjection R G U (h.comparisonHomeomorph x) *
          completedGroupAlgebraProjection R G U (h.comparisonHomeomorph y) :=
        congrArg₂ (· * ·)
          (h.completedGroupAlgebraProjection_comparisonHomeomorph U x).symm
          (h.completedGroupAlgebraProjection_comparisonHomeomorph U y).symm
      _ = completedGroupAlgebraProjection R G U
          (h.comparisonHomeomorph x * h.comparisonHomeomorph y) :=
        (map_mul (completedGroupAlgebraProjection R G U) _ _).symm

/-- Ring-equivalence form of the finite-stage characterization. -/
@[simp]
theorem completedGroupAlgebraProjection_comparisonRingEquiv
    (h : CanonicalCompletedGroupAlgebraModel R G RG algebraicMap)
    (U : CompletedGroupAlgebraIndex G) (x : RG) :
    completedGroupAlgebraProjection R G U (h.comparisonRingEquiv x) =
      h.stageProjection U x :=
  h.completedGroupAlgebraProjection_comparisonHomeomorph U x

/-- The derived comparison ring equivalence is continuous. -/
theorem comparisonRingEquiv_continuous
    (h : CanonicalCompletedGroupAlgebraModel R G RG algebraicMap) :
    Continuous h.comparisonRingEquiv := by
  change Continuous h.comparisonHomeomorph
  exact h.comparisonHomeomorph.continuous

/-- The inverse of the derived comparison ring equivalence is continuous. -/
theorem comparisonRingEquiv_symm_continuous
    (h : CanonicalCompletedGroupAlgebraModel R G RG algebraicMap) :
    Continuous h.comparisonRingEquiv.symm := by
  change Continuous h.comparisonHomeomorph.symm
  exact h.comparisonHomeomorph.symm.continuous

/-- The derived comparison extends the specified algebraic map. -/
@[simp]
theorem comparisonRingEquiv_algebraicMap
    (h : CanonicalCompletedGroupAlgebraModel R G RG algebraicMap)
    (x : CompletedGroupAlgebraNaturalSource R G) :
    h.comparisonRingEquiv (algebraicMap x) =
      toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G) x := by
  apply completedGroupAlgebra_ext (R := R) (G := G)
  intro U
  calc
    completedGroupAlgebraProjection R G U
        (h.comparisonRingEquiv (algebraicMap x)) =
        h.stageProjection U (algebraicMap x) :=
      h.completedGroupAlgebraProjection_comparisonRingEquiv U (algebraicMap x)
    _ = completedGroupAlgebraNaturalSourceStageMap R G U x :=
      congrFun (congrArg DFunLike.coe (h.stageProjection_comp_algebraicMap U)) x
    _ = completedGroupAlgebraProjection R G U
        (toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G) x) := by
      rw [completedGroupAlgebraNaturalSourceStageMap_apply]
      change completedGroupAlgebraStageMap R G U x.toMonoidAlgebra =
        completedGroupAlgebraProjection R G U
          (toCompletedGroupAlgebra R G x.toMonoidAlgebra)
      exact
        (completedGroupAlgebraProjection_toCompletedGroupAlgebra
          (R := R) (G := G) U x.toMonoidAlgebra).symm

/-- Bundled ring-homomorphism form of algebraic-map compatibility. -/
theorem comparisonRingEquiv_comp_algebraicMap
    (h : CanonicalCompletedGroupAlgebraModel R G RG algebraicMap) :
    h.comparisonRingEquiv.toRingHom.comp algebraicMap =
      toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G) := by
  apply RingHom.ext
  intro x
  exact h.comparisonRingEquiv_algebraicMap x

/-- The specified algebraic map is forced by the finite-stage cone: it is the canonical map
followed by the inverse comparison equivalence. -/
theorem algebraicMap_eq_comparisonRingEquiv_symm_comp
    (h : CanonicalCompletedGroupAlgebraModel R G RG algebraicMap) :
    algebraicMap = h.comparisonRingEquiv.symm.toRingHom.comp
      (toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G)) := by
  apply RingHom.ext
  intro x
  apply h.comparisonRingEquiv.injective
  change h.comparisonRingEquiv (algebraicMap x) =
    h.comparisonRingEquiv
      (h.comparisonRingEquiv.symm
        (toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G) x))
  calc
    h.comparisonRingEquiv (algebraicMap x) =
        toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G) x :=
      h.comparisonRingEquiv_algebraicMap x
    _ = h.comparisonRingEquiv
        (h.comparisonRingEquiv.symm
          (toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G) x)) :=
      (h.comparisonRingEquiv.apply_symm_apply _).symm

/-- Continuity of the specified algebraic map is derived from the inverse-limit comparison. -/
theorem algebraicMap_continuous
    (h : CanonicalCompletedGroupAlgebraModel R G RG algebraicMap) :
    Continuous algebraicMap := by
  rw [h.algebraicMap_eq_comparisonRingEquiv_symm_comp]
  exact h.comparisonRingEquiv_symm_continuous.comp
    (continuous_toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G))

/-- Density of the specified algebraic map is likewise forced by the canonical inverse-limit
model; it is not independent structure data. -/
theorem algebraicMap_dense
    (h : CanonicalCompletedGroupAlgebraModel R G RG algebraicMap) :
    DenseRange algebraicMap := by
  rw [h.algebraicMap_eq_comparisonRingEquiv_symm_comp]
  exact h.comparisonRingEquiv.symm.surjective.denseRange.comp
    (denseRange_toCompletedGroupAlgebraNaturalSourceRingHom
      (R := R) (G := G))
    h.comparisonRingEquiv_symm_continuous

variable {RG₁ : ProfiniteRing.{w}} {RG₂ : ProfiniteRing.{z}}
variable {algebraicMap₁ : CompletedGroupAlgebraNaturalSource R G →+* RG₁}
variable {algebraicMap₂ : CompletedGroupAlgebraNaturalSource R G →+* RG₂}

/-- The canonical homeomorphism between two finite-stage inverse-limit models. -/
noncomputable def modelToModelHomeomorph
    (h₁ : CanonicalCompletedGroupAlgebraModel R G RG₁ algebraicMap₁)
    (h₂ : CanonicalCompletedGroupAlgebraModel R G RG₂ algebraicMap₂) :
    RG₁ ≃ₜ RG₂ :=
  h₁.comparisonHomeomorph.trans h₂.comparisonHomeomorph.symm

/-- The canonical ring equivalence between two finite-stage inverse-limit models. -/
noncomputable def modelToModelRingEquiv
    (h₁ : CanonicalCompletedGroupAlgebraModel R G RG₁ algebraicMap₁)
    (h₂ : CanonicalCompletedGroupAlgebraModel R G RG₂ algebraicMap₂) :
    RG₁ ≃+* RG₂ :=
  h₁.comparisonRingEquiv.trans h₂.comparisonRingEquiv.symm

/-- The model-to-model equivalence commutes with every finite-stage projection. -/
@[simp]
theorem stageProjection_modelToModelRingEquiv
    (h₁ : CanonicalCompletedGroupAlgebraModel R G RG₁ algebraicMap₁)
    (h₂ : CanonicalCompletedGroupAlgebraModel R G RG₂ algebraicMap₂)
    (U : CompletedGroupAlgebraIndex G) (x : RG₁) :
    h₂.stageProjection U (h₁.modelToModelRingEquiv h₂ x) =
      h₁.stageProjection U x := by
  change h₂.stageProjection U
      (h₂.comparisonRingEquiv.symm (h₁.comparisonRingEquiv x)) =
    h₁.stageProjection U x
  calc
    h₂.stageProjection U
        (h₂.comparisonRingEquiv.symm (h₁.comparisonRingEquiv x)) =
        completedGroupAlgebraProjection R G U
          (h₂.comparisonRingEquiv
            (h₂.comparisonRingEquiv.symm (h₁.comparisonRingEquiv x))) :=
      (h₂.completedGroupAlgebraProjection_comparisonRingEquiv U
        (h₂.comparisonRingEquiv.symm (h₁.comparisonRingEquiv x))).symm
    _ = completedGroupAlgebraProjection R G U (h₁.comparisonRingEquiv x) := by
      rw [RingEquiv.apply_symm_apply]
    _ = h₁.stageProjection U x :=
      h₁.completedGroupAlgebraProjection_comparisonRingEquiv U x

/-- The canonical model-to-model ring equivalence is continuous. -/
theorem modelToModelRingEquiv_continuous
    (h₁ : CanonicalCompletedGroupAlgebraModel R G RG₁ algebraicMap₁)
    (h₂ : CanonicalCompletedGroupAlgebraModel R G RG₂ algebraicMap₂) :
    Continuous (h₁.modelToModelRingEquiv h₂) := by
  change Continuous (h₁.modelToModelHomeomorph h₂)
  exact (h₁.modelToModelHomeomorph h₂).continuous

/-- The inverse of the canonical model-to-model ring equivalence is continuous. -/
theorem modelToModelRingEquiv_symm_continuous
    (h₁ : CanonicalCompletedGroupAlgebraModel R G RG₁ algebraicMap₁)
    (h₂ : CanonicalCompletedGroupAlgebraModel R G RG₂ algebraicMap₂) :
    Continuous (h₁.modelToModelRingEquiv h₂).symm := by
  change Continuous (h₁.modelToModelHomeomorph h₂).symm
  exact (h₁.modelToModelHomeomorph h₂).symm.continuous

/-- The canonical model-to-model equivalence carries one specified algebraic map to the other. -/
@[simp]
theorem modelToModelRingEquiv_algebraicMap
    (h₁ : CanonicalCompletedGroupAlgebraModel R G RG₁ algebraicMap₁)
    (h₂ : CanonicalCompletedGroupAlgebraModel R G RG₂ algebraicMap₂)
    (x : CompletedGroupAlgebraNaturalSource R G) :
    h₁.modelToModelRingEquiv h₂ (algebraicMap₁ x) = algebraicMap₂ x := by
  apply h₂.comparisonRingEquiv.injective
  change h₂.comparisonRingEquiv
      (h₂.comparisonRingEquiv.symm
        (h₁.comparisonRingEquiv (algebraicMap₁ x))) =
    h₂.comparisonRingEquiv (algebraicMap₂ x)
  rw [RingEquiv.apply_symm_apply, h₁.comparisonRingEquiv_algebraicMap,
    h₂.comparisonRingEquiv_algebraicMap]

/-- Bundled ring-homomorphism form of model-to-model algebraic-map compatibility. -/
theorem modelToModelRingEquiv_comp_algebraicMap
    (h₁ : CanonicalCompletedGroupAlgebraModel R G RG₁ algebraicMap₁)
    (h₂ : CanonicalCompletedGroupAlgebraModel R G RG₂ algebraicMap₂) :
    (h₁.modelToModelRingEquiv h₂).toRingHom.comp algebraicMap₁ = algebraicMap₂ := by
  apply RingHom.ext
  intro x
  exact h₁.modelToModelRingEquiv_algebraicMap h₂ x

/-- A ring equivalence commuting with all finite-stage projections is the canonical
model-to-model equivalence.  Joint injectivity of the canonical stage projections makes a
separate continuity hypothesis unnecessary. -/
theorem modelToModelRingEquiv_unique
    (h₁ : CanonicalCompletedGroupAlgebraModel R G RG₁ algebraicMap₁)
    (h₂ : CanonicalCompletedGroupAlgebraModel R G RG₂ algebraicMap₂)
    (e : RG₁ ≃+* RG₂)
    (hstage : ∀ U : CompletedGroupAlgebraIndex G,
      (h₂.stageProjection U).comp e.toRingHom = h₁.stageProjection U) :
    e = h₁.modelToModelRingEquiv h₂ := by
  apply RingEquiv.ext
  intro x
  apply h₂.comparisonRingEquiv.injective
  apply completedGroupAlgebra_ext (R := R) (G := G)
  intro U
  calc
    completedGroupAlgebraProjection R G U (h₂.comparisonRingEquiv (e x)) =
        h₂.stageProjection U (e x) :=
      h₂.completedGroupAlgebraProjection_comparisonRingEquiv U (e x)
    _ = h₁.stageProjection U x :=
      congrFun (congrArg DFunLike.coe (hstage U)) x
    _ = h₂.stageProjection U (h₁.modelToModelRingEquiv h₂ x) :=
      (h₁.stageProjection_modelToModelRingEquiv h₂ U x).symm
    _ = completedGroupAlgebraProjection R G U
        (h₂.comparisonRingEquiv (h₁.modelToModelRingEquiv h₂ x)) :=
      (h₂.completedGroupAlgebraProjection_comparisonRingEquiv U
        (h₁.modelToModelRingEquiv h₂ x)).symm

end CanonicalCompletedGroupAlgebraModel

/-- A completed group algebra model whose coefficient ring, profinite carrier, and group are
genuine bundled objects.

The data fields contain the algebraic map and the finite-stage cone with its universal property.
Continuity, density, and carrier profiniteness are theorems forced by comparison with the concrete
inverse limit; they are not stored as independent witnesses.  Likewise, all input profiniteness
structure is inherited from the objects. `CompletedGroupAlgebraModel.certificate` reconstructs
the finite-stage certificate when needed. -/
structure CompletedGroupAlgebraModel
    (R : ProfiniteCommRing.{u}) (G : ProfiniteGrp.{v}) where
  /-- The profinite ring underlying the completed group-algebra model. -/
  carrier : ProfiniteRing.{w}
  /-- The canonical map from the algebraic group algebra into the model. -/
  algebraicMap : CompletedGroupAlgebraNaturalSource R G →+* carrier
  /-- The projection from the model to each finite group-algebra stage. -/
  stageProjection : ∀ U : CompletedGroupAlgebraIndex G,
    carrier →+* CompletedGroupAlgebraStage R G U
  /-- Each stage projection agrees with the canonical stage map on the algebraic source. -/
  stageProjection_comp_algebraicMap : ∀ U : CompletedGroupAlgebraIndex G,
    (stageProjection U).comp algebraicMap = completedGroupAlgebraNaturalSourceStageMap R G U
  /-- The stage projections exhibit the model carrier as the inverse limit. -/
  isInverseLimit :
    (completedGroupAlgebraSystem R G).IsInverseLimit
      (fun U x => stageProjection U x)

namespace CompletedGroupAlgebraModel

variable {R : ProfiniteCommRing.{u}} {G : ProfiniteGrp.{v}}

/-- Expose the bundled model's finite-stage inverse-limit certificate. -/
def certificate (M : CompletedGroupAlgebraModel R G) :
    CanonicalCompletedGroupAlgebraModel R G M.carrier M.algebraicMap where
  stageProjection := M.stageProjection
  stageProjection_comp_algebraicMap := M.stageProjection_comp_algebraicMap
  isInverseLimit := M.isInverseLimit

/-- Package a finite-stage certificate as a completed-group-algebra model. -/
def ofCertificate (carrier : ProfiniteRing.{w})
    (algebraicMap : CompletedGroupAlgebraNaturalSource R G →+* carrier)
    (h : CanonicalCompletedGroupAlgebraModel R G carrier algebraicMap) :
    CompletedGroupAlgebraModel R G where
  carrier := carrier
  algebraicMap := algebraicMap
  stageProjection := h.stageProjection
  stageProjection_comp_algebraicMap := h.stageProjection_comp_algebraicMap
  isInverseLimit := h.isInverseLimit

/-- The bundled model's specified algebraic map is continuous; this is derived, not stored. -/
theorem algebraicMap_continuous (M : CompletedGroupAlgebraModel R G) :
    Continuous M.algebraicMap :=
  M.certificate.algebraicMap_continuous

/-- The bundled model's specified algebraic map has dense range; this is derived, not stored. -/
theorem algebraicMap_dense (M : CompletedGroupAlgebraModel R G) :
    DenseRange M.algebraicMap :=
  M.certificate.algebraicMap_dense

/-- Restriction of the algebraic map to the coefficient ring. -/
def coefficientMap (M : CompletedGroupAlgebraModel R G) : R →+* M.carrier :=
  M.algebraicMap.comp
    (completedGroupAlgebraNaturalSourceCoefficientRingHom (R := R) (G := G))

/-- Restriction of the algebraic map to group-like elements. -/
def groupMap (M : CompletedGroupAlgebraModel R G) : G →* M.carrier :=
  M.algebraicMap.toMonoidHom.comp
    (completedGroupAlgebraNaturalSourceGroupMonoidHom (R := R) (G := G))

/-- Group-like elements land in units; this is the object-level unit representation of a model. -/
def groupUnitsMap (M : CompletedGroupAlgebraModel R G) : G →* M.carrierˣ :=
  M.groupMap.toHomUnits

/-- Forgetting the unit structure from a model's group map recovers its underlying group-like
element. -/
@[simp]
theorem groupUnitsMap_coe (M : CompletedGroupAlgebraModel R G) (g : G) :
    ((M.groupUnitsMap g : M.carrierˣ) : M.carrier) = M.groupMap g :=
  rfl

/-- The derived comparison with the concrete compatible-family model. -/
noncomputable def comparisonRingEquiv (M : CompletedGroupAlgebraModel R G) :
    M.carrier ≃+* CompletedGroupAlgebraCarrier R G :=
  M.certificate.comparisonRingEquiv

/-- The derived comparison is a homeomorphism. -/
noncomputable def comparisonHomeomorph (M : CompletedGroupAlgebraModel R G) :
    M.carrier ≃ₜ CompletedGroupAlgebraCarrier R G :=
  M.certificate.comparisonHomeomorph

/-- The bundled comparison is characterized by every finite-stage projection. -/
@[simp]
theorem completedGroupAlgebraProjection_comparisonRingEquiv
    (M : CompletedGroupAlgebraModel R G) (U : CompletedGroupAlgebraIndex G) (x : M.carrier) :
    completedGroupAlgebraProjection R G U (M.comparisonRingEquiv x) =
      M.stageProjection U x :=
  M.certificate.completedGroupAlgebraProjection_comparisonRingEquiv U x

/-- The bundled comparison extends the model's full algebraic map. -/
@[simp]
theorem comparisonRingEquiv_algebraicMap (M : CompletedGroupAlgebraModel R G)
    (x : CompletedGroupAlgebraNaturalSource R G) :
    M.comparisonRingEquiv (M.algebraicMap x) =
      toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G) x :=
  M.certificate.comparisonRingEquiv_algebraicMap x

/-- The comparison therefore respects the coefficient-ring embedding. -/
@[simp]
theorem comparisonRingEquiv_coefficientMap (M : CompletedGroupAlgebraModel R G) (r : R) :
    M.comparisonRingEquiv (M.coefficientMap r) =
      algebraMap R (CompletedGroupAlgebraCarrier R G) r := by
  change M.comparisonRingEquiv
      (M.algebraicMap
        (completedGroupAlgebraNaturalSourceCoefficientRingHom (R := R) (G := G) r)) =
    algebraMap R (CompletedGroupAlgebraCarrier R G) r
  exact
    (M.comparisonRingEquiv_algebraicMap
      (completedGroupAlgebraNaturalSourceCoefficientRingHom (R := R) (G := G) r)).trans
      (toCompletedGroupAlgebraNaturalSourceRingHom_coefficient (R := R) (G := G) r)

/-- Source-wrapper form of compatibility with the group-like map.  The normalized
`completedGroupAlgebraOf` form is stated after that canonical map is introduced below. -/
@[simp]
theorem comparisonRingEquiv_groupMap_source (M : CompletedGroupAlgebraModel R G) (g : G) :
    M.comparisonRingEquiv (M.groupMap g) =
      toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G)
        (completedGroupAlgebraNaturalSourceGroupMonoidHom (R := R) (G := G) g) :=
  M.comparisonRingEquiv_algebraicMap
    (completedGroupAlgebraNaturalSourceGroupMonoidHom (R := R) (G := G) g)

/-- Canonical equivalence between any two bundled models. -/
noncomputable def modelEquiv (M : CompletedGroupAlgebraModel.{u, v, w} R G)
    (N : CompletedGroupAlgebraModel.{u, v, z} R G) :
    M.carrier ≃+* N.carrier :=
  M.certificate.modelToModelRingEquiv N.certificate

/-- The model equivalence carries the specified algebraic map to the specified algebraic map. -/
@[simp]
theorem modelEquiv_algebraicMap (M : CompletedGroupAlgebraModel.{u, v, w} R G)
    (N : CompletedGroupAlgebraModel.{u, v, z} R G)
    (x : CompletedGroupAlgebraNaturalSource R G) :
    M.modelEquiv N (M.algebraicMap x) = N.algebraicMap x :=
  M.certificate.modelToModelRingEquiv_algebraicMap N.certificate x

/-- The canonical equivalence commutes with every finite-stage projection. -/
@[simp]
theorem stageProjection_modelEquiv (M : CompletedGroupAlgebraModel.{u, v, w} R G)
    (N : CompletedGroupAlgebraModel.{u, v, z} R G)
    (U : CompletedGroupAlgebraIndex G) (x : M.carrier) :
    N.stageProjection U (M.modelEquiv N x) = M.stageProjection U x :=
  M.certificate.stageProjection_modelToModelRingEquiv N.certificate U x

/-- The canonical equivalence restricts to the identity on coefficient-ring data. -/
@[simp]
theorem modelEquiv_coefficientMap (M : CompletedGroupAlgebraModel.{u, v, w} R G)
    (N : CompletedGroupAlgebraModel.{u, v, z} R G) (r : R) :
    M.modelEquiv N (M.coefficientMap r) = N.coefficientMap r :=
  M.modelEquiv_algebraicMap N
    (completedGroupAlgebraNaturalSourceCoefficientRingHom (R := R) (G := G) r)

/-- The canonical equivalence restricts to the identity on group-like data. -/
@[simp]
theorem modelEquiv_groupMap (M : CompletedGroupAlgebraModel.{u, v, w} R G)
    (N : CompletedGroupAlgebraModel.{u, v, z} R G) (g : G) :
    M.modelEquiv N (M.groupMap g) = N.groupMap g :=
  M.modelEquiv_algebraicMap N
    (completedGroupAlgebraNaturalSourceGroupMonoidHom (R := R) (G := G) g)

/-- The canonical equivalence between bundled models is continuous. -/
theorem modelEquiv_continuous (M : CompletedGroupAlgebraModel.{u, v, w} R G)
    (N : CompletedGroupAlgebraModel.{u, v, z} R G) :
    Continuous (M.modelEquiv N) :=
  M.certificate.modelToModelRingEquiv_continuous N.certificate

/-- Its inverse is continuous as well. -/
theorem modelEquiv_symm_continuous (M : CompletedGroupAlgebraModel.{u, v, w} R G)
    (N : CompletedGroupAlgebraModel.{u, v, z} R G) :
    Continuous (M.modelEquiv N).symm :=
  M.certificate.modelToModelRingEquiv_symm_continuous N.certificate

/-- Public bundled uniqueness theorem: a ring equivalence commuting with all stage projections
is the canonical model equivalence. -/
theorem modelEquiv_unique (M : CompletedGroupAlgebraModel.{u, v, w} R G)
    (N : CompletedGroupAlgebraModel.{u, v, z} R G)
    (e : M.carrier ≃+* N.carrier)
    (hstage : ∀ U : CompletedGroupAlgebraIndex G,
      (N.stageProjection U).comp e.toRingHom = M.stageProjection U) :
    e = M.modelEquiv N :=
  M.certificate.modelToModelRingEquiv_unique N.certificate e hstage

end CompletedGroupAlgebraModel

/-- The concrete inverse-limit carrier as a profinite ring object. -/
noncomputable def completedGroupAlgebraProfiniteRing
    (R : ProfiniteCommRing.{u}) (G : ProfiniteGrp.{v}) : ProfiniteRing := by
  letI : CompactSpace (CompletedGroupAlgebraCarrier R G) :=
    completedGroupAlgebra_compactSpace (R := R) (G := G)
  letI : T2Space (CompletedGroupAlgebraCarrier R G) :=
    completedGroupAlgebra_t2Space (R := R) (G := G)
  letI : TotallyDisconnectedSpace (CompletedGroupAlgebraCarrier R G) :=
    completedGroupAlgebra_totallyDisconnectedSpace (R := R) (G := G)
  exact
    { toProfinite := Profinite.of (CompletedGroupAlgebraCarrier R G)
      ring := inferInstance
      isTopologicalRing := inferInstance }

/-- The inverse-limit carrier with its canonical dense map is the canonical model. -/
noncomputable def completedGroupAlgebraCanonicalModel
    (R : ProfiniteCommRing.{u}) (G : ProfiniteGrp.{v}) :
    CanonicalCompletedGroupAlgebraModel R G (completedGroupAlgebraProfiniteRing R G)
      (toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G)) where
  stageProjection := completedGroupAlgebraProjection R G
  stageProjection_comp_algebraicMap := by
    intro U
    apply RingHom.ext
    intro x
    change completedGroupAlgebraProjection R G U
        (toCompletedGroupAlgebraNaturalSourceRingHom (R := R) (G := G) x) =
      completedGroupAlgebraNaturalSourceStageMap R G U x
    rw [completedGroupAlgebraNaturalSourceStageMap_apply]
    change completedGroupAlgebraProjection R G U
        (toCompletedGroupAlgebra R G x.toMonoidAlgebra) =
      completedGroupAlgebraStageMap R G U x.toMonoidAlgebra
    exact completedGroupAlgebraProjection_toCompletedGroupAlgebra
      (R := R) (G := G) U x.toMonoidAlgebra
  isInverseLimit := by
    change
      (completedGroupAlgebraSystem R G).IsInverseLimit
        (fun U x => (completedGroupAlgebraSystem R G).projection U x)
    exact (completedGroupAlgebraSystem R G).isInverseLimit_projection

/-- The concrete inverse limit packaged as the canonical bundled completed-group-algebra model.

This is the object-level source of truth: the coefficient ring and group enter as standard
profinite bundles, so their compactness and separation witnesses are not repeated in the API. -/
noncomputable def completedGroupAlgebraModel
    (Λ : ProfiniteCommRing.{u}) (P : ProfiniteGrp.{v}) :
    CompletedGroupAlgebraModel Λ P :=
  CompletedGroupAlgebraModel.ofCertificate
    (completedGroupAlgebraProfiniteRing Λ P)
    (toCompletedGroupAlgebraNaturalSourceRingHom (R := Λ) (G := P))
    (completedGroupAlgebraCanonicalModel Λ P)

namespace CompletedGroupAlgebraModel

variable {R : ProfiniteCommRing.{u}} {G : ProfiniteGrp.{v}}

/-- The model comparison sends its group-like map to the canonical completed group element. -/
@[simp]
theorem comparisonRingEquiv_groupMap (M : CompletedGroupAlgebraModel R G) (g : G) :
    M.comparisonRingEquiv (M.groupMap g) = completedGroupAlgebraOf R G g := by
  change M.comparisonRingEquiv (M.groupMap g) =
    toCompletedGroupAlgebra R G (MonoidAlgebra.of R G g)
  exact (M.comparisonRingEquiv_groupMap_source g).trans
    (toCompletedGroupAlgebraNaturalSourceRingHom_group (R := R) (G := G) g)

end CompletedGroupAlgebraModel

/-- The dense abstract group-algebra map lands in the span of the completed group-like elements. -/
theorem toCompletedGroupAlgebraRingHom_mem_span_completedGroupAlgebraOf
    (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraRingHom R G x ∈
      Submodule.span R (Set.range (completedGroupAlgebraOf R G)) := by
  classical
  let P := fun y : MonoidAlgebra R G =>
    toCompletedGroupAlgebraRingHom R G y ∈
      Submodule.span R (Set.range (completedGroupAlgebraOf R G))
  change P x
  refine MonoidAlgebra.induction_on (motive := P) x ?_ ?_ ?_
  · intro g
    dsimp [P]
    change completedGroupAlgebraOf R G g ∈
      Submodule.span R (Set.range (completedGroupAlgebraOf R G))
    exact Submodule.subset_span ⟨g, rfl⟩
  · intro a b ha hb
    dsimp [P] at ha hb ⊢
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  · intro r y hy
    dsimp [P] at hy ⊢
    change toCompletedGroupAlgebra R G (r • y) ∈
      Submodule.span R (Set.range (completedGroupAlgebraOf R G))
    rw [toCompletedGroupAlgebra_smul]
    exact Submodule.smul_mem _ r hy

/-- The completed group-like elements have dense linear span in the completed group algebra. -/
theorem completedGroupAlgebraOf_dense_span :
    closure (Submodule.span R (Set.range (completedGroupAlgebraOf R G)) :
      Set (CompletedGroupAlgebraCarrier R G)) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro y
  have hy :
      y ∈ closure (Set.range (toCompletedGroupAlgebraRingHom R G)) := by
    rw [(denseRange_toCompletedGroupAlgebraRingHom (R := R) (G := G)).closure_range]
    exact Set.mem_univ y
  exact closure_mono (by
    intro z hz
    rcases hz with ⟨x, rfl⟩
    exact toCompletedGroupAlgebraRingHom_mem_span_completedGroupAlgebraOf
      (R := R) (G := G) x) hy

/--
The uniqueness half of the universal property in Lemma 5.3.5(d): a continuous linear map out of
\(\widehat{R[G]}\) is determined by its values on the completed group-like elements.
-/
theorem completedGroupAlgebraContinuousLinearMap_ext_of_basis
    {N : Type w} [AddCommGroup N] [TopologicalSpace N] [Module R N] [T2Space N]
    {F K : CompletedGroupAlgebraCarrier R G →L[R] N}
    (hbasis : ∀ g : G, F (completedGroupAlgebraOf R G g) =
      K (completedGroupAlgebraOf R G g)) :
    F = K := by
  apply ContinuousLinearMap.ext
  intro x
  have hclosed : IsClosed {x : CompletedGroupAlgebraCarrier R G | F x = K x} :=
    isClosed_eq F.continuous K.continuous
  have hspan :
      (Submodule.span R (Set.range (completedGroupAlgebraOf R G)) :
        Set (CompletedGroupAlgebraCarrier R G)) ⊆
        {x : CompletedGroupAlgebraCarrier R G | F x = K x} := by
    intro y hy
    exact Submodule.span_induction
      (fun z hz => by
        rcases hz with ⟨g, rfl⟩
        exact hbasis g)
      (by simp only [Set.mem_ofPred_eq, map_zero])
      (fun z w _ _ hz hw => by
        change F (z + w) = K (z + w)
        rw [map_add, map_add, hz, hw])
      (fun r z _ hz => by
        change F (r • z) = K (r • z)
        rw [map_smul, map_smul, hz])
      hy
  have hx :
      x ∈ closure (Submodule.span R (Set.range (completedGroupAlgebraOf R G)) :
        Set (CompletedGroupAlgebraCarrier R G)) := by
    rw [completedGroupAlgebraOf_dense_span (R := R) (G := G)]
    exact Set.mem_univ x
  exact hclosed.closure_subset_iff.2 hspan hx
end

end CompletedGroupAlgebra
