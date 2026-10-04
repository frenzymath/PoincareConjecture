import PoincareLib.Geometry.Riemannian.Soul.Point.Radial
import PoincareLib.Geometry.Riemannian.Soul.Point.DistanceLevels
import PoincareLib.Geometry.Riemannian.Soul.Point.Geodesic

/-!
# Point souls in positive curvature

This is the public composition theorem for the point-soul, Euclidean, and
radial producers.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [NoncompactSpace M]

/-- Complete noncompact three-manifolds with positive sectional curvature have
a point soul, a global Euclidean diffeomorphism, and distance-parametrized
radial coordinates on the punctured manifold. -/
theorem exists_pointSoulData_of_strictlyPositiveSectionalCurvature
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hpos : D.StrictlyPositiveSectionalCurvature) :
    Nonempty (PointSoulData g) := by
  obtain ⟨p, o, c, hlevel, hp⟩ :=
    g.exists_singleton_horoball_of_strictlyPositiveSectionalCurvature D hcomplete hpos
  obtain ⟨e, he⟩ := g.exists_euclidean_diffeomorph_of_singleton_horoball D hcomplete
    (hpos.nonnegative D) hlevel
  obtain ⟨H⟩ := g.exists_radialHomeomorph_of_singleton_horoball D hcomplete
    (hpos.nonnegative D) hlevel
  exact ⟨⟨p, hp, e, he, H⟩⟩

/-- The point-soul package unpacked in the form used by geometric consumers. -/
theorem exists_point_soul_euclidean_radial_of_strictlyPositiveSectionalCurvature
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hpos : D.StrictlyPositiveSectionalCurvature) :
    ∃ p : M, TotallyConvexSet g ({p} : Set M) ∧
      ∃ e : Diffeomorph (𝓡 3) (𝓡 3)
        (EuclideanSpace ℝ (Fin 3)) M ∞,
        e 0 = p ∧ Nonempty (RadialHomeomorph g p) := by
  obtain ⟨P⟩ :=
    exists_pointSoulData_of_strictlyPositiveSectionalCurvature g D hcomplete hpos
  exact ⟨P.center, P.totallyConvex_singleton, P.euclidean,
    P.euclidean_zero, ⟨P.radial⟩⟩

end PoincareMT.RiemannianMetric
