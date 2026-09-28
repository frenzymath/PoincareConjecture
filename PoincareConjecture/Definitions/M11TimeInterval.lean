import PoincareConjecture.Definitions.M11AdaptedAtlas
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture


structure SmoothSpacetimeInterval (I : SpacetimeInterval) where
  chartedSpace : ChartedSpace (EuclideanHalfSpace 1) I.domain
  isManifold : IsManifold (𝓡∂ 1) ∞ I.domain
  inclusion_smooth : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (Subtype.val : I.domain → ℝ)
  boundary_eq : (𝓡∂ 1).boundary I.domain =
    {t : I.domain | (t : ℝ) ∈ frontier I.domain}
  inclusionDerivative : ∀ t : I.domain, TangentSpace (𝓡∂ 1) t ≃L[ℝ] ℝ
  inclusionDerivative_eq : ∀ t,
    (inclusionDerivative t).toContinuousLinearMap =
      mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : I.domain → ℝ) t
  positive_tangent_smooth : ContMDiff (𝓡∂ 1)
    ((𝓡∂ 1).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) ∞
    (fun t : I.domain ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin 1))
      (E := (TangentSpace (𝓡∂ 1) : I.domain → Type _))
      t ((inclusionDerivative t).symm 1))

namespace SmoothSpacetimeInterval

variable {I : SpacetimeInterval}


abbrev Point (_D : SmoothSpacetimeInterval I) := I.domain

instance (D : SmoothSpacetimeInterval I) :
    ChartedSpace (EuclideanHalfSpace 1) D.Point := D.chartedSpace

instance (D : SmoothSpacetimeInterval I) : IsManifold (𝓡∂ 1) ∞ D.Point :=
  D.isManifold


noncomputable def positiveTangent (D : SmoothSpacetimeInterval I) (t : D.Point) :
    TangentSpace (𝓡∂ 1) t := (D.inclusionDerivative t).symm 1

end SmoothSpacetimeInterval


def spacetimeIntervalInclusion {I J : SpacetimeInterval}
    (D : SmoothSpacetimeInterval I) (E : SmoothSpacetimeInterval J)
    (h : I.domain ⊆ J.domain) : D.Point → E.Point :=
  fun t ↦ ⟨t.val, h t.property⟩



structure SpacetimeIntervalSystem where
  interval : ∀ I : SpacetimeInterval, SmoothSpacetimeInterval I
  inclusion_smooth : ∀ I J (h : I.domain ⊆ J.domain),
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ (spacetimeIntervalInclusion (interval I) (interval J) h)
  inclusion_derivative : ∀ I J (h : I.domain ⊆ J.domain) (t : (interval I).Point),
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (spacetimeIntervalInclusion (interval I) (interval J) h) t
      ((interval I).positiveTangent t) =
      (interval J).positiveTangent (spacetimeIntervalInclusion (interval I) (interval J) h t)

end PoincareConjecture
