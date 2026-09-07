import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.IdeleClassPGroupH1
import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

set_option autoImplicit false
/-!
# The principal-idele sequence in degree two

The actual principal ideles, relative ideles, and relative idele classes form
a short exact sequence of Galois representations.  Its long exact sequence
is the source of the global degree-two diagonal injection.
-/

open CategoryTheory NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open RelativeIdeleGroup.Cohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [Algebra K L]

local instance : MulDistribMulAction (Gal(L/K)) (RelativeIdeleGroup K L) :=
  relativeIdeleMulDistribMulAction K L

local instance : MulDistribMulAction (Gal(L/K))
    (RelativeIdeleGroup.principalSubgroup K L) :=
  principalIdeleMulDistribMulAction K L

local instance : MulDistribMulAction (Gal(L/K)) (RelativeIdeleGroup.ClassGroup K L) :=
  ideleClassMulDistribMulAction K L

/-- The concrete principal-idele sequence, regarded as Galois representations. -/
def finiteIdeleShortComplex : ShortComplex (Rep ℤ (Gal(L/K))) :=
  equivariantShortComplex
    (G := Gal(L/K)) (A := RelativeIdeleGroup.principalSubgroup K L)
    (B := RelativeIdeleGroup K L) (C := RelativeIdeleGroup.ClassGroup K L)
    (RelativeIdeleGroup.principalSubgroup K L).subtype
    (QuotientGroup.mk' (RelativeIdeleGroup.principalSubgroup K L))
    (principalIdeleSubtype_equivariant K L)
    (ideleClassQuotientMap_equivariant K L)
    (principalIdele_ideleClass_exact K L)

/-- Short exactness is supplied by the actual principal subgroup and quotient. -/
theorem finiteIdeleShortComplex_shortExact : (finiteIdeleShortComplex K L).ShortExact :=
  equivariantShortComplex_shortExact _ _
    (G := Gal(L/K)) (A := RelativeIdeleGroup.principalSubgroup K L)
    (B := RelativeIdeleGroup K L) (C := RelativeIdeleGroup.ClassGroup K L)
    (principalIdeleSubtype_equivariant K L)
    (ideleClassQuotientMap_equivariant K L)
    (principalIdele_ideleClass_exact K L)
    (RelativeIdeleGroup.principalSubgroup K L).subtype_injective
    (QuotientGroup.mk'_surjective (RelativeIdeleGroup.principalSubgroup K L))

/-- The degree-two map induced by the actual inclusion of principal ideles. -/
def finitePrincipalIdeleH2Map :
    groupCohomology (finiteIdeleShortComplex K L).X₁ 2 →ₗ[ℤ]
      groupCohomology (finiteIdeleShortComplex K L).X₂ 2 :=
  ((groupCohomology.functor ℤ (Gal(L/K)) 2).map (finiteIdeleShortComplex K L).f).hom

/-- For a finite Galois `p`-extension, the actual inclusion of principal ideles
is injective on `H²`.  Vanishing of idele-class `H¹` is supplied by the
class-field axiom, rather than assumed as an additional exactness input. -/
theorem finitePrincipalIdeleH2Map_injective_of_isPGroup
    [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p (Gal(L/K))) :
    Function.Injective (finitePrincipalIdeleH2Map K L) := by
  have hS := finiteIdeleShortComplex_shortExact K L
  let T := groupCohomology.mapShortComplex₁ hS (i := 1) (j := 2) rfl
  have hT : T.Exact := groupCohomology.mapShortComplex₁_exact hS rfl
  have hzero : Subsingleton T.X₁ := ideleClassH1_subsingleton_of_isPGroup K L hP
  have hf : T.f = 0 := by
    apply ModuleCat.hom_ext
    ext x
    rw [@Subsingleton.elim _ hzero x 0, map_zero]
    rfl
  have hm : Mono T.g := hT.mono_g hf
  exact (ModuleCat.mono_iff_injective T.g).mp hm

end ClassFieldTower.Martinet.Shafarevich

end
