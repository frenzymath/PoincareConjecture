import PoincareConjecture.Proofs.M08.WeightedJacobiCoefficients
import PoincareConjecture.Proofs.M09.CoordinateConnectionBilinear










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)




theorem chartActionMetric_pos_of_target {z : ℝ × EuclideanSpace ℝ (Fin n)}
    (hz : z.2 ∈ (extChartAt (𝓡 n) x).target)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < M08.chartActionMetric F T x z v v := by
  apply M08.metricInChart_pos _ _ v hv
  simpa only [extChartAt_source] using (extChartAt (𝓡 n) x).map_target hz




theorem chartActionMetric_symm_of_target {z : ℝ × EuclideanSpace ℝ (Fin n)}
    (hz : z.2 ∈ (extChartAt (𝓡 n) x).target) (v w : EuclideanSpace ℝ (Fin n)) :
    M08.chartActionMetric F T x z v w = M08.chartActionMetric F T x z w v := by
  apply M08.metricInChart_symm _ _ v w
  simpa only [extChartAt_source] using (extChartAt (𝓡 n) x).map_target hz




theorem closedChartConnection_eq_open {C : Set ℝ} {s : ℝ}
    (hC : C ∈ 𝓝 s) {q : EuclideanSpace ℝ (Fin n)}
    (hq : q ∈ (extChartAt (𝓡 n) x).target) :
    M08.closedChartConnection F T x C (s, q) =
      Proofs.M09.coordinateConnectionBilinear (M08.chartActionMetric F T x) (s, q) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have heq : M08.chartActionMetric F T x (s, q)
      (M08.closedChartConnection F T x C (s, q) v w) =
      M08.chartActionMetric F T x (s, q)
        (Proofs.M09.coordinateConnectionBilinear (M08.chartActionMetric F T x) (s, q) v w) := by
    ext u
    rw [M08.closedChartConnection_apply, M08.closedChartChristoffel_pair F T x C hq,
      M08.chartChristoffelCovector_apply,
      M08.spatialWithinFDeriv_eq_spatialFDeriv
        (isOpen_extChartAt_target (I := 𝓡 n) x) _ hC hq,
      Proofs.M09.coordinateConnectionBilinear_apply,
      Proofs.M09.coordinateConnection_pairing _ _ (chartActionMetric_pos_of_target F T x hq)]
    simp only [M08.spatialFDeriv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply]
    ring
  calc
    _ = M08.chartMetricDualInverse F T x (s, q)
        (M08.chartActionMetric F T x (s, q)
          (M08.closedChartConnection F T x C (s, q) v w)) :=
      (M08.chartMetricDualInverse_left F T x hq _).symm
    _ = _ := by rw [heq, M08.chartMetricDualInverse_left F T x hq]




theorem closedChartConnection_eventuallyEq_open {C : Set ℝ} {s : ℝ}
    (hC : C ∈ 𝓝 s) {q : EuclideanSpace ℝ (Fin n)}
    (hq : q ∈ (extChartAt (𝓡 n) x).target) :
    M08.closedChartConnection F T x C =ᶠ[𝓝 (s, q)]
      Proofs.M09.coordinateConnectionBilinear (M08.chartActionMetric F T x) := by
  have hs : s ∈ interior C := mem_interior_iff_mem_nhds.mpr hC
  filter_upwards [(isOpen_interior.prod (isOpen_extChartAt_target (I := 𝓡 n) x)).mem_nhds
    (show (s, q) ∈ interior C ×ˢ (extChartAt (𝓡 n) x).target from ⟨hs, hq⟩)] with z hz
  exact closedChartConnection_eq_open F T x (mem_interior_iff_mem_nhds.mp hz.1) hz.2




theorem closedChartConnection_fderivWithin_eq_open {C : Set ℝ} {s : ℝ}
    (hC : C ∈ 𝓝 s) {q : EuclideanSpace ℝ (Fin n)}
    (hq : q ∈ (extChartAt (𝓡 n) x).target) :
    fderivWithin ℝ (M08.closedChartConnection F T x C)
      (C ×ˢ (extChartAt (𝓡 n) x).target) (s, q) =
      fderiv ℝ (Proofs.M09.coordinateConnectionBilinear (M08.chartActionMetric F T x))
        (s, q) := by
  rw [fderivWithin_of_mem_nhds (prod_mem_nhds hC
    ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds hq))]
  exact (closedChartConnection_eventuallyEq_open F T x hC hq).fderiv_eq

end PoincareConjecture.M14
