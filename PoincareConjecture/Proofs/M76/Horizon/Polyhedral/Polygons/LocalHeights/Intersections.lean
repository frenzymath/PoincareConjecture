import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.Segments
import PoincareConjecture.Proofs.M76.Mathlib.SimplexExtremeFaces
import PoincareConjecture.Proofs.M76.Mathlib.ExtremeSegmentIntersections

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem triangleSliceGraph_segment_inter (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    {a b c d : K.TriangleSliceLabel A}
    (hab : (K.triangleSliceGraph A).Adj a b) (hcd : (K.triangleSliceGraph A).Adj c d) :
    segment ℝ (K.triangleSlicePoint A a) (K.triangleSlicePoint A b) ∩
      segment ℝ (K.triangleSlicePoint A c) (K.triangleSlicePoint A d) ⊆
        convexHull ℝ (({K.triangleSlicePoint A a, K.triangleSlicePoint A b} : Set E) ∩
          {K.triangleSlicePoint A c, K.triangleSlicePoint A d}) := by
  apply segment_inter_subset_convexHull_of_isExtreme
  · rw [K.triangleSliceGraph_segment hA hab, K.triangleSliceGraph_segment hA hcd]
    exact K.isExtreme_convexHull_section_inter hab.1 hcd.1 (K.triangleZeroSet A)
  · rw [K.triangleSliceGraph_segment hA hab, K.triangleSliceGraph_segment hA hcd,
      inter_comm (convexHull ℝ (↑(K.triangleSliceOriginalVertices A a ∪
        K.triangleSliceOriginalVertices A b) : Set E) ∩ _)]
    exact K.isExtreme_convexHull_section_inter hcd.1 hab.1 (K.triangleZeroSet A)

end Geometry.SimplicialComplex
