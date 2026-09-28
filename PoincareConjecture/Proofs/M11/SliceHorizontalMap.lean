import PoincareConjecture.Proofs.M11.SliceTangent
import PoincareConjecture.Proofs.M11.HorizontalCoordinates





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def sliceHorizontalTangentMap (A : AdaptedMetricAtlas n X) (t : ℝ) :
    letI := adaptedSliceChartedSpace A t
    TangentBundle (𝓡 n) (spacetimeSlice A.time t) →
      TotalSpace (EuclideanSpace ℝ (Fin n)) (fun p ↦ adaptedHorizontal A p) :=
  letI := adaptedSliceChartedSpace A t
  fun v ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) v.proj.val
    (sliceHorizontalEquiv A t v.proj v.2)

theorem sliceHorizontalTangentMap_smooth (A : AdaptedMetricAtlas n X) (t : ℝ) :
    letI := adaptedChartedSpace A
    letI : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
    letI := adaptedSliceChartedSpace A t
    letI : IsManifold (𝓡 n) ∞ (spacetimeSlice A.time t) := adaptedSlice_isManifold A t
    letI := adaptedHorizontalTopology A
    letI := adaptedHorizontalFiberBundle A
    letI := adaptedHorizontalVectorBundle A
    letI := adaptedHorizontalSmoothBundle A
    ContMDiff ((𝓡 n).prod (𝓡 n)) ((spacetimeModel n).prod (𝓡 n)) ∞
      (sliceHorizontalTangentMap A t) := by
  let := adaptedChartedSpace A
  let : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
  let := adaptedSliceChartedSpace A t
  let : IsManifold (𝓡 n) ∞ (spacetimeSlice A.time t) := adaptedSlice_isManifold A t
  let := adaptedHorizontalTopology A
  let := adaptedHorizontalFiberBundle A
  let := adaptedHorizontalVectorBundle A
  let := adaptedHorizontalSmoothBundle A
  apply (contMDiff_horizontal_iff A _).mpr
  have h := (slice_inclusion_smooth A t).contMDiff_tangentMap (m := ∞) (by simp)
  apply h.congr
  intro v
  apply TotalSpace.ext
  · rfl
  · exact heq_of_eq (sliceHorizontalEquiv_eq A t v.proj v.2)

theorem slice_inclusion_differential_injective (A : AdaptedMetricAtlas n X) (t : ℝ)
    (p : spacetimeSlice A.time t) :
    letI := adaptedChartedSpace A
    letI := adaptedSliceChartedSpace A t
    Function.Injective
      (mfderiv (𝓡 n) (spacetimeModel n) (Subtype.val : spacetimeSlice A.time t → X) p) := by
  let := adaptedChartedSpace A
  let := adaptedSliceChartedSpace A t
  intro v w h
  apply (sliceHorizontalEquiv A t p).injective
  apply Subtype.ext
  simpa only [sliceHorizontalEquiv_eq] using h

end PoincareConjecture.Proofs.M11
