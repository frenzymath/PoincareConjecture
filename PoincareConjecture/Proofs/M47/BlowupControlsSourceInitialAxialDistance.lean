import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialAxialPath
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {g0 : StandardInitialMetric}
  {K : MetricSurgeryConstants} {I : MetricSurgeryInput K g}

theorem source_initial_old_height_le_tip_distance
    (R : MetricSurgeryResult g0 I) {y : M}
    (hy : y ∈ I.neck.region (-I.neck.epsilon⁻¹) 0) :
    ENNReal.ofReal (I.neck.scale / 2 * |(I.neck.coordinate_inverse y).2|) ≤
      R.metric.edist R.tip (R.collapse y) := by
  by_contra hnot
  have hd := lt_of_not_ge hnot
  have hball : R.tip ∈ R.metric.ball (R.collapse y)
      (I.neck.scale / 2 * |(I.neck.coordinate_inverse y).2|) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : R.output.carrier → Type _) :=
      ⟨R.metric.toRiemannianMetric⟩
    change R.metric.edist (R.collapse y) R.tip < _
    change Manifold.riemannianEDist (𝓡 3) (R.collapse y) R.tip < _
    rw [Manifold.riemannianEDist_comm]
    exact hd
  obtain ⟨p, hp0, hp1, hp, hlength, _⟩ :=
    R.metric.exists_short_path_in_ball (R.collapse y) R.tip hball
  exact not_lt_of_ge (source_initial_old_height_le_path_length R hy p hp hp0 hp1) hlength

end PoincareConjecture.M47
