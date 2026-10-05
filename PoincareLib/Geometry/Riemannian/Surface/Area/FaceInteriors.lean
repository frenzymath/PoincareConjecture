import PoincareLib.Geometry.Riemannian.Surface.Area.Triangulation
import PoincareLib.Geometry.Riemannian.Heat.Energy.VolumeSupport

/-!
# Disjoint interiors of smooth triangulation faces

The actual overlap law gives zero intrinsic area. Full support of the metric
volume upgrades this to disjoint topological face interiors.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareMT.Topology.Surface.FiniteSmoothTriangulation

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [T3Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  [IsManifold (𝓡 2) ∞ S]

/-- Distinct smooth triangulation faces have disjoint interiors, derived from
the actual edge-or-vertex overlap and intrinsic Riemannian volume. -/
theorem disjoint_face_interiors (T : FiniteSmoothTriangulation (M := S))
    (g : RiemannianMetric 2 S) :
    Pairwise (fun f h => Disjoint (interior (T.face f).carrier) (interior (T.face h).carrier)) := by
  intro f h hfh
  apply disjoint_iff_inter_eq_empty.mpr
  rw [← interior_inter]
  exact g.volumeMeasure.interior_eq_empty_of_null (T.aedisjoint_faces g hfh)

end PoincareMT.Topology.Surface.FiniteSmoothTriangulation
