import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Orientation.Cover.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometrySectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Equivalence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Basic








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Poincare.Topology.OrientationDoubleCover

variable (M : Type u) [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]


noncomputable def pullbackMetric (g : PoincareConjecture.RiemannianMetric 3 M) :
    letI := chartedSpace M
    letI := isManifold M
    PoincareConjecture.RiemannianMetric 3 (TotalSpace M) := by
  let := chartedSpace M
  let := isManifold M
  exact g.pullbackOfLocalDiffeomorph (proj M) (isLocalDiffeomorph M)

theorem pullbackMetric_inner (g : PoincareConjecture.RiemannianMetric 3 M) :
    letI := chartedSpace M
    letI := isManifold M
    ∀ (p : TotalSpace M) (u v : TangentSpace (𝓡 3) p),
      (pullbackMetric M g).inner p u v = g.inner (proj M p) u v := by
  let := chartedSpace M
  let := isManifold M
  intro p u v
  change g.inner (proj M p) (mfderiv (𝓡 3) (𝓡 3) (proj M) p u)
    (mfderiv (𝓡 3) (𝓡 3) (proj M) p v) = _
  rw [mfderiv_proj_eq_id]
  rfl

theorem sectionalCurvature_pullbackMetric (g : PoincareConjecture.RiemannianMetric 3 M)
    (D : PoincareConjecture.LeviCivitaData g) :
    letI := chartedSpace M
    letI := isManifold M
    ∀ (p : TotalSpace M) (u v : TangentSpace (𝓡 3) p),
      (pullbackMetric M g).leviCivitaData.sectionalCurvature p u v =
        D.sectionalCurvature (proj M p) u v := by
  let := chartedSpace M
  let := isManifold M
  intro p u v
  have h := (pullbackMetric M g).leviCivitaData.sectionalCurvature_eq_of_local_isometry D
    (f := proj M) isOpen_univ (isLocalDiffeomorph M).contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ p) u v
  rw [mfderiv_proj_eq_id] at h
  exact h



theorem strictlyPositiveSectionalCurvature_pullbackMetric
    (g : PoincareConjecture.RiemannianMetric 3 M) (D : PoincareConjecture.LeviCivitaData g)
    (hsec : D.StrictlyPositiveSectionalCurvature) :
    letI := chartedSpace M
    letI := isManifold M
    (pullbackMetric M g).leviCivitaData.StrictlyPositiveSectionalCurvature := by
  let := chartedSpace M
  let := isManifold M
  intro p u v hu hv huv
  rw [pullbackMetric_inner] at hu hv huv
  rw [sectionalCurvature_pullbackMetric M g D]
  exact hsec (proj M p) u v hu hv huv


theorem flip_edist (g : PoincareConjecture.RiemannianMetric 3 M) :
    letI := chartedSpace M
    letI := isManifold M
    ∀ p q : TotalSpace M,
      (pullbackMetric M g).edist (flip M p) (flip M q) = (pullbackMetric M g).edist p q := by
  let := chartedSpace M
  let := isManifold M
  intro p q
  exact (pullbackMetric M g).edist_eq_of_diffeomorph_metric_pullback
    (pullbackMetric M g) (flipDiffeomorph M)
    (fun x u v => (flip_preserves_pullback_metric M g x u v).symm) p q

end Poincare.Topology.OrientationDoubleCover
