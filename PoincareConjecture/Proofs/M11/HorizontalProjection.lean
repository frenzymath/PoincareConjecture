import PoincareConjecture.Proofs.M11.HorizontalCoordinates
import PoincareConjecture.Proofs.M11.FiberOperations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem adaptedHorizontalProjection_smooth (A : AdaptedMetricAtlas n X) :
    letI := adaptedChartedSpace A
    letI : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
    letI := adaptedHorizontalTopology A
    letI := adaptedHorizontalFiberBundle A
    letI := adaptedHorizontalVectorBundle A
    letI := adaptedHorizontalSmoothBundle A
    ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n))
      ((spacetimeModel n).prod (𝓡 n)) ∞
      (fun v : TangentBundle (spacetimeModel n) X ↦
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := fun p ↦ adaptedHorizontal A p) v.proj
          (adaptedHorizontalProjection A v.proj v.2)) := by
  let := adaptedChartedSpace A
  let : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
  let := adaptedHorizontalTopology A
  let := adaptedHorizontalFiberBundle A
  let := adaptedHorizontalVectorBundle A
  let := adaptedHorizontalSmoothBundle A
  apply (contMDiff_horizontal_iff A _).mpr
  have hid : ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n))
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun v : TangentBundle (spacetimeModel n) X ↦
        TotalSpace.mk' (SpacetimeModelVector n) v.proj v.2) := contMDiff_id
  have hdt : ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) 𝓘(ℝ) ∞
      (fun v : TangentBundle (spacetimeModel n) X ↦
        mfderiv (spacetimeModel n) 𝓘(ℝ) A.time v.proj v.2) :=
    (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ)).comp
      ((adapted_time_smooth A).contMDiff_tangentMap (m := ∞) (by simp))
  have hvector : ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n))
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun v : TangentBundle (spacetimeModel n) X ↦
        TotalSpace.mk' (SpacetimeModelVector n) v.proj (adaptedTimeVector A v.proj)) :=
    (adaptedTimeVector_smooth A).comp
      (contMDiff_proj (TangentSpace (spacetimeModel n) : X → Type _))
  exact contMDiff_fiber_sub hid (contMDiff_fiber_smul hdt hvector)

end PoincareConjecture.Proofs.M11
