import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.CompressionCylinderRectangles
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.FourConvexPiecesEulerCount

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.CompressionCylinder

theorem surfaceEulerCount_eq_zero
    (K : SimplicialComplex ℝ Ambient) (hK : K.faces.Finite)
    (hspace : K.space = sphere (0 : Plane) 1 ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) :
    K.surfaceEulerCount = 0 := by
  choose C hC hCs using exists_side_complex
  apply K.surfaceEulerCount_eq_zero_of_four_convex_cover hK C hC
    (by simp only [hCs]; exact hspace.trans iUnion_side.symm)
    (fun i => hCs i ▸ side_convex i) (fun i => hCs i ▸ side_nonempty i)
    sidePlane (fun i => hCs i ▸ side_subset_plane i) sidePlane_dim
  · simpa only [hCs] using adjacent_intersections_nonempty
  · simpa only [hCs] using opposite_disjoint

end PoincareConjecture.M76.CompressionCylinder
