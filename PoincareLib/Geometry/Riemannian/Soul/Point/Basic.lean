import PoincareLib.Geometry.Riemannian.Soul.Exhaustion
import PoincareLib.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareLib.Geometry.Riemannian.SpaceForm.RoundSphere
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Point souls and radial data

This file fixes the interfaces used by the positive-curvature soul theorem.
Total convexity uses the geodesic equation of the selected metric and includes
nonminimizing segments, as in Morgan--Tian, Section 2.2, p. 25.

The terminal-set, global smooth-flow, and radial-flow producers are kept in
separate files.  This mirrors the proof of Morgan--Tian, Theorem 2.7 and the
radial discussion following Corollary 2.10 (pp. 25--27).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [NoncompactSpace M]

/-- Every geodesic segment with endpoints in the set stays in the set.
No minimizing hypothesis is imposed. -/
def TotallyConvexSet (g : RiemannianMetric 3 M) (S : Set M) : Prop :=
  ∀ (curve : ℝ → M) (a b : ℝ),
    g.IsGeodesicOn curve (Icc a b) →
    curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S

end PoincareMT.RiemannianMetric

namespace PoincareMT.LeviCivitaData

open PoincareMT.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [NoncompactSpace M]
  {g : RiemannianMetric 3 M}

/-- Strict positivity of sectional curvature on every orthonormal two-plane. -/
def StrictlyPositiveSectionalCurvature (D : LeviCivitaData g) : Prop :=
  ∀ (x : M) (u v : TangentSpace (𝓡 3) x),
    g.inner x u u = 1 → g.inner x v v = 1 → g.inner x u v = 0 →
      0 < D.sectionalCurvature x u v

/-- Strict positivity supplies the nonnegative curvature input of the
convex exhaustion.  The curvature-tensor version also covers dependent pairs,
where the totalized sectional curvature is zero. -/
theorem StrictlyPositiveSectionalCurvature.nonnegative
    (D : LeviCivitaData g)
    (hpos : D.StrictlyPositiveSectionalCurvature) :
    D.NonnegativeSectionalCurvature := by
  intro x u v
  exact D.curvatureTensor_diagonal_nonneg_of_orthonormal x
    (fun u v hu hv huv => (hpos x u v hu hv huv).le) u v

end LeviCivitaData
end PoincareMT

namespace PoincareMT.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [NoncompactSpace M]

abbrev UnitTwoSphere := Poincare.Geometry.Riemannian.SpaceForm.UnitSphere 2

/-- The intrinsic distance sphere about a point. -/
def distanceSphere (g : RiemannianMetric 3 M) (p : M) (r : ℝ) : Set M :=
  {x | (g.edist p x).toReal = r}

/-- The intrinsic closed distance annulus about a point. -/
def distanceAnnulus (g : RiemannianMetric 3 M) (p : M) (a b : ℝ) : Set M :=
  {x | a ≤ (g.edist p x).toReal ∧ (g.edist p x).toReal ≤ b}

/-- A distance-parametrized radial homeomorphism away from a point soul. -/
structure RadialHomeomorph (g : RiemannianMetric 3 M) (p : M) where
  toHomeomorph :
    (UnitTwoSphere × {r : ℝ // r ∈ Ioi (0 : ℝ)}) ≃ₜ {x : M // x ≠ p}
  distance_eq : ∀ z,
    (g.edist p ((toHomeomorph z : {x : M // x ≠ p}) : M)).toReal = z.2

namespace RadialHomeomorph

variable {g : RiemannianMetric 3 M} {p : M}

@[simp] theorem coe_toHomeomorph (H : RadialHomeomorph g p) (z) :
    ((H.toHomeomorph z : {x : M // x ≠ p}) : M) = H.toHomeomorph z := rfl

theorem map_mem_distanceSphere (H : RadialHomeomorph g p)
    (z : UnitTwoSphere × {r : ℝ // r ∈ Ioi (0 : ℝ)}) :
    ((H.toHomeomorph z : {x : M // x ≠ p}) : M) ∈ distanceSphere g p z.2 := by
  exact H.distance_eq z

end RadialHomeomorph

/-- The complete point-soul package used by neck consumers. -/
structure PointSoulData (g : RiemannianMetric 3 M) where
  center : M
  totallyConvex_singleton : TotallyConvexSet g {center}
  euclidean : Diffeomorph (𝓡 3) (𝓡 3)
    (EuclideanSpace ℝ (Fin 3)) M ∞
  euclidean_zero : euclidean 0 = center
  radial : RadialHomeomorph g center

end PoincareMT.RiemannianMetric
