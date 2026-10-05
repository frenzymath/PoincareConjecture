import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedLength
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Jacobi.Index.WeightedJacobiCoefficients
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Tensor.CoordinateConnectionBilinear

/-!
# Agreement of actual closed and open coordinate connections

Morgan-Tian Lemmas 6.10 and 6.19, pp. 109-110, 114. On a strict
time interior, the closed within metric derivative is unrestricted.
The two actual Koszul constructions then have equal pairings with
every vector, so metric duality identifies their values and germs.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)

/-- The actual chart metric is positive on its spatial chart target,
independently of an ambient open time window, as used in the local
Jacobi calculation of Lemma 6.10, pp. 109-110. -/
theorem chartActionMetric_pos_of_target {z : ℝ × EuclideanSpace ℝ (Fin n)}
    (hz : z.2 ∈ (extChartAt (𝓡 n) x).target)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < M08.chartActionMetric F T x z v v := by
  apply M08.metricInChart_pos _ _ v hv
  simpa only [extChartAt_source] using (extChartAt (𝓡 n) x).map_target hz

/-- The actual chart metric is symmetric on its spatial chart target,
the metric hypothesis in the coordinate linearization of Lemma 6.10,
pp. 109-110. -/
theorem chartActionMetric_symm_of_target {z : ℝ × EuclideanSpace ℝ (Fin n)}
    (hz : z.2 ∈ (extChartAt (𝓡 n) x).target) (v w : EuclideanSpace ℝ (Fin n)) :
    M08.chartActionMetric F T x z v w = M08.chartActionMetric F T x z w v := by
  apply M08.metricInChart_symm _ _ v w
  simpa only [extChartAt_source] using (extChartAt (𝓡 n) x).map_target hz

/-- On a time neighborhood, M08's actual closed connection equals
M09's actual unrestricted Koszul connection, with the same metric
and spatial chart. This is the local bridge for Lemma 6.19, p. 114. -/
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

/-- The two actual connections have equal germs at every interior
time-chart point, allowing their actual derivatives to be compared
in Lemma 6.19, p. 114. -/
theorem closedChartConnection_eventuallyEq_open {C : Set ℝ} {s : ℝ}
    (hC : C ∈ 𝓝 s) {q : EuclideanSpace ℝ (Fin n)}
    (hq : q ∈ (extChartAt (𝓡 n) x).target) :
    M08.closedChartConnection F T x C =ᶠ[𝓝 (s, q)]
      Proofs.M09.coordinateConnectionBilinear (M08.chartActionMetric F T x) := by
  have hs : s ∈ interior C := mem_interior_iff_mem_nhds.mpr hC
  filter_upwards [(isOpen_interior.prod (isOpen_extChartAt_target (I := 𝓡 n) x)).mem_nhds
    (show (s, q) ∈ interior C ×ˢ (extChartAt (𝓡 n) x).target from ⟨hs, hq⟩)] with z hz
  exact closedChartConnection_eq_open F T x (mem_interior_iff_mem_nhds.mp hz.1) hz.2

/-- The actual within derivative of the closed connection is the
actual derivative of the open Koszul connection on every interior
time neighborhood, the derivative bridge in Lemma 6.19, p. 114. -/
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

end PoincareMT.M14
