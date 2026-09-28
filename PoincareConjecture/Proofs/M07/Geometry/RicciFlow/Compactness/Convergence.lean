import PoincareConjecture.Statements.Ch05.Compactness
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Pointed

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

namespace PointedRicciFlowCompactnessHypotheses

theorem all_time_curvature_control_on_zero_ball
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ k : ℕ in Filter.atTop,
        let C := H.sequence.carrier k
        let F := H.sequence.flow k
        letI : TopologicalSpace C.carrier := C.topologicalSpace
        letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
        letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
        ∀ t ∈ Set.Ioo T' T, ∀ x ∈ F.zeroBall A,
          (F.flow.connection t).curvatureTensorNorm x ≤ K := by
  obtain ⟨K, hK, hbound⟩ := H.all_time_curvature_control A hA
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with k hk
  dsimp
  intro t ht x hx
  simpa [BasedFlow.zeroBall, BasedFlow.ballAt] using
    hk 0 ⟨H.time_bounds.1, H.time_bounds.2⟩ t ht x hx

end PointedRicciFlowCompactnessHypotheses

end PoincareConjecture
