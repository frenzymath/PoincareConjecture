import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Connected
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Small


noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric



theorem scalar_integral_le_of_small_connected_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    (C : ℝ)
    (hbound : ∀ (N : Type) [TopologicalSpace N] [T3Space N]
      [MeasurableSpace N] [BorelSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
      [PreconnectedSpace N] (h : RiemannianMetric n N) (E : LeviCivitaData h),
      MetricComplete h →
      (∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ E.sectionalCurvature x v w) →
      ∀ q, (∫ x in h.ball q 1, E.scalarCurvature x ∂h.volumeMeasure) ≤ C)
    (p : M) :
    (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤ C := by
  apply g.scalar_integral_le_of_connected_bound D hcomplete hsec C ?_ p
  intro N _ _ _ _ _ _ _ h E hcompleteN hsecN q
  let : SecondCountableTopology N := h.secondCountableTopology
  let : Small.{0} N := Poincare.Topology.SecondCountable.small N
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Shrink.{0} N) :=
    Poincare.Manifold.shrinkChartedSpace _ N
  let : IsManifold (𝓡 n) ∞ (Shrink.{0} N) :=
    Poincare.Manifold.shrinkIsManifold (𝓡 n) N
  let : T3Space (Shrink.{0} N) :=
    (Poincare.Topology.SecondCountable.homeomorphShrink N).t3Space
  let : MeasurableSpace (Shrink.{0} N) := borel (Shrink.{0} N)
  let : BorelSpace (Shrink.{0} N) := ⟨rfl⟩
  let : PreconnectedSpace (Shrink.{0} N) := shrink_preconnectedSpace
  have hb := hbound (Shrink.{0} N) h.shrink h.shrink.leviCivitaData
    (h.shrink_metricComplete_iff.mpr hcompleteN)
    (h.shrink_sectionalCurvature_lower_bound E hsecN) ((equivShrink N) q)
  simpa only [h.shrink_integral_scalarCurvature_ball E, Equiv.symm_apply_apply] using hb

end PoincareConjecture.RiemannianMetric
