import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.Metric
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Rescaling
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Distance
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Curvature.TerminalCurvatureCapLocalization
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Component.ComponentEstimateGeometry
import PoincareLib.Geometry.Riemannian.Normalization.Metric.Construction

/-!
# Exact physical scalar radii under the actual source normalization

Positive metric scaling cancels the physical scalar radius. The same
physical carrier and its literal cap or component witness are retained.
Source: derivations/terminal-curvature-physical-normalization.md, K8a.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareMT.M47

/-- The two verified normalization constructions have the same actual
metric; their different proof terms do not alter the bilinear form. -/
theorem terminalCurvature_rescaledMetric_eq_m01
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (Q : ℝ) (hQ : 0 < Q) :
    rescaledMetric g Q hQ = m01RescaledMetric g Q hQ := by
  rfl

/-- The positive square-root length scaling cancels exactly with the
physical scalar factor; no index-dependent radius buffer remains. -/
theorem terminalCurvature_scaled_scalar_radius {Q H : ℝ} (hQ : 0 < Q) (hH : 0 < H) :
    Real.sqrt Q * (Q * H) ^ (-1 / 2 : ℝ) = H ^ (-1 / 2 : ℝ) := by
  rw [Real.mul_rpow hQ.le hH.le, Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hQ]
  norm_num

/-- The physical scalar-radius ball is the same actual normalized
scalar-radius ball after the exact positive radius cancellation. -/
theorem terminalCurvature_scaled_ball_contains
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {Q H C : ℝ} (hQ : 0 < Q) (hH : 0 < H)
    (x : M) : g.ball x (C * (Q * H) ^ (-1 / 2 : ℝ)) ⊆
      (rescaledMetric g Q hQ).ball x (C * H ^ (-1 / 2 : ℝ)) := by
  intro y hy
  change (rescaledMetric g Q hQ).edist x y < _
  rw [rescaledMetric_edist]
  have hm := ENNReal.mul_lt_mul_left
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ)).ne' ENNReal.ofReal_ne_top hy
  rw [mul_comm (g.edist x y), mul_comm (ENNReal.ofReal (C * (Q * H) ^ (-1 / 2 : ℝ)))] at hm
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg Q)] at hm
  have hr : Real.sqrt Q * (C * (Q * H) ^ (-1 / 2 : ℝ)) = C * H ^ (-1 / 2 : ℝ) := by
    rw [mul_left_comm, terminalCurvature_scaled_scalar_radius hQ hH]
  rwa [hr] at hm

/-- A normalized scalar floor captures the original physical cap in a
fixed ball for the actual normalized metric. -/
theorem terminalCurvature_scaled_cap_carrier_subset_ball
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g)
    {Q C H : ℝ} (hQ : 0 < Q) (hC : N.cap_constant ≤ C) (hH : 0 < H)
    {x : M} (hx : x ∈ N.core)
    (hscalar : H ≤ (rescaledMetric_connection g N.connection Q hQ).scalarCurvature x) :
    N.carrier ⊆ (rescaledMetric g Q hQ).ball x (C * H ^ (-1 / 2 : ℝ)) := by
  rw [rescaledMetric_scalarCurvature] at hscalar
  have hphysical : Q * H ≤ N.connection.scalarCurvature x := by
    have hh := (le_div_iff₀ hQ).mp (show H ≤ N.connection.scalarCurvature x / Q by
      simpa only [div_eq_mul_inv, mul_comm] using hscalar)
    simpa only [mul_comm] using hh
  exact (terminalCurvature_cap_carrier_subset_ball N hC (mul_pos hQ hH) hx hphysical).trans
    (terminalCurvature_scaled_ball_contains g hQ hH x)

/-- The unchanged whole physical C-component has the same fixed
normalized radius at every point with positive normalized scalar. -/
theorem terminalCurvature_scaled_component_subset_ball
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g} {C : ℝ}
    (N : SingularCComponent g D C) {Q H : ℝ} (hQ : 0 < Q) (hH : 0 < H)
    {x : M} (hx : x ∈ N.carrier)
    (hscalar : H ≤ (rescaledMetric_connection g D Q hQ).scalarCurvature x) :
    N.carrier ⊆ (rescaledMetric g Q hQ).ball x (C * H ^ (-1 / 2 : ℝ)) := by
  rw [rescaledMetric_scalarCurvature] at hscalar
  have hphysical : Q * H ≤ D.scalarCurvature x := by
    have hh := (le_div_iff₀ hQ).mp (show H ≤ D.scalarCurvature x / Q by
      simpa only [div_eq_mul_inv, mul_comm] using hscalar)
    simpa only [mul_comm] using hh
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hQ hH) hphysical
    (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  have hc : N.carrier ⊆ g.ball x (C * (Q * H) ^ (-1 / 2 : ℝ)) := by
    intro y hy
    exact (component_subset_ball N hx hy).trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hp N.constant_pos.le))
  exact hc.trans (terminalCurvature_scaled_ball_contains g hQ hH x)

end PoincareMT.M47
