import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.PolygonFinitePLDiskModel
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.TriangleDiskRegions
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Arcs.FinitePLMarkedInterval
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.RadialConeBoundary

/-!
# The full triangular cone on a marked interval

The target of the actual boundary-edge dual cone has a level-one
base and its entire three-edge frontier. These are affine coordinates
for the target triangle in PrimeReduction derivation010, section3.
See Hudson1969, pp.15--19,58--63.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76.PrimeReduction.IntervalCone

/-- The entire level-one base of the target cone. See derivation010. -/
def base : Set (ℝ × ℝ) := segment ℝ (1, 0) (0, 1)

/-- The actual cone carrier is the standard nondegenerate triangle.
See derivation010, section3. -/
theorem cone_eq_triangle : convexJoin ℝ {(0 : ℝ × ℝ)} base =
    convexHull ℝ (range TriangleDiskModel.rightTriangle) := by
  rw [base, convexJoin_singleton_segment]
  congr 1
  ext x
  simp [TriangleDiskModel.rightTriangle, Prod.zero_eq_mk, or_comm, or_left_comm]

/-- The whole planar frontier consists of the base and both endpoint
rays, including the apex. See derivation010, section3. -/
theorem frontier_cone : frontier (convexJoin ℝ {(0 : ℝ × ℝ)} base) =
    base ∪ convexJoin ℝ {0} {(1, 0), (0, 1)} := by
  rw [cone_eq_triangle,
    TriangleDiskModel.rightTriangle.frontier_convexHull_triangle
      TriangleDiskModel.independent_rightTriangle]
  have hp : ({(1, 0), (0, 1)} : Set (ℝ × ℝ)) = {(1, 0)} ∪ {(0, 1)} := by
    ext x
    simp [or_comm]
  rw [hp, convexJoin_union_right, convexJoin_singletons, convexJoin_singletons]
  ext x
  simp only [Polygon.boundary, Polygon.edgeSet, mem_iUnion, mem_union]
  simp [TriangleDiskModel.rightTriangle, Fin.exists_fin_succ,
    affineSegment_eq_segment, base, Prod.zero_eq_mk, segment_symm,
    or_comm, or_left_comm, or_assoc]

/-- The full target cone, with its complete marked rim, is a finite
PL disk. See derivation010, section3. -/
theorem isFinitePLBallPair_cone :
    IsFinitePLBallPair (ℝ × ℝ) (convexJoin ℝ {(0 : ℝ × ℝ)} base)
      (base ∪ convexJoin ℝ {0} {(1, 0), (0, 1)}) := by
  rw [← frontier_cone, cone_eq_triangle]
  exact TriangleDiskModel.rightTriangle.isFinitePLBallPair_convexHull_triangle
    TriangleDiskModel.independent_rightTriangle

/-- The same base carries its two specified endpoints as a finite
PL interval pair. See derivation010, section3. -/
theorem isFinitePLBallPair_base :
    IsFinitePLBallPair ℝ base ({(1, 0), (0, 1)} : Set (ℝ × ℝ)) := by
  let f : ℝ →ᴬ[ℝ] (ℝ × ℝ) := ContinuousAffineMap.lineMap (1, 0) (0, 1)
  have hf : InjOn f (Icc (0 : ℝ) 1) :=
    (AffineMap.lineMap_injective ℝ (by norm_num : ((1, 0) : ℝ × ℝ) ≠ (0, 1))).injOn
  have h := isFinitePLBallPair_affine_interval zero_lt_one f hf
  change IsFinitePLBallPair ℝ ((AffineMap.lineMap (1, 0) (0, 1)) '' Icc 0 1)
    {AffineMap.lineMap (1, 0) (0, 1) (0 : ℝ),
      AffineMap.lineMap (1, 0) (0, 1) (1 : ℝ)} at h
  simpa only [segment_eq_image_lineMap, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, base] using h

/-- Every base point has the same nonzero linear level, so its rays
are distinct and its faces cone linearly. See derivation010, section3. -/
theorem level_base {x : ℝ × ℝ} (hx : x ∈ base) :
    (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ) x = 1 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  simpa using hab

end PoincareMT.M76.PrimeReduction.IntervalCone
