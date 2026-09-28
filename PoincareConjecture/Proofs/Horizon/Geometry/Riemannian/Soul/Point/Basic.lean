import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.RoundSphere
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [NoncompactSpace M]

def TotallyConvexSet (g : RiemannianMetric 3 M) (S : Set M) : Prop :=
  ∀ (curve : ℝ → M) (a b : ℝ),
    g.IsGeodesicOn curve (Icc a b) →
    curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.LeviCivitaData

open PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [NoncompactSpace M]
  {g : RiemannianMetric 3 M}

def StrictlyPositiveSectionalCurvature (D : LeviCivitaData g) : Prop :=
  ∀ (x : M) (u v : TangentSpace (𝓡 3) x),
    g.inner x u u = 1 → g.inner x v v = 1 → g.inner x u v = 0 →
      0 < D.sectionalCurvature x u v

theorem StrictlyPositiveSectionalCurvature.nonnegative
    (D : LeviCivitaData g)
    (hpos : D.StrictlyPositiveSectionalCurvature) :
    D.NonnegativeSectionalCurvature := by
  intro x u v
  exact D.curvatureTensor_diagonal_nonneg_of_orthonormal x
    (fun u v hu hv huv => (hpos x u v hu hv huv).le) u v

end LeviCivitaData
end PoincareConjecture

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [NoncompactSpace M]

abbrev UnitTwoSphere := Poincare.Geometry.Riemannian.SpaceForm.UnitSphere 2

def distanceSphere (g : RiemannianMetric 3 M) (p : M) (r : ℝ) : Set M :=
  {x | (g.edist p x).toReal = r}

def distanceAnnulus (g : RiemannianMetric 3 M) (p : M) (a b : ℝ) : Set M :=
  {x | a ≤ (g.edist p x).toReal ∧ (g.edist p x).toReal ≤ b}

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

structure PointSoulData (g : RiemannianMetric 3 M) where
  center : M
  totallyConvex_singleton : TotallyConvexSet g {center}
  euclidean : Diffeomorph (𝓡 3) (𝓡 3)
    (EuclideanSpace ℝ (Fin 3)) M ∞
  euclidean_zero : euclidean 0 = center
  radial : RadialHomeomorph g center

end PoincareConjecture.RiemannianMetric
