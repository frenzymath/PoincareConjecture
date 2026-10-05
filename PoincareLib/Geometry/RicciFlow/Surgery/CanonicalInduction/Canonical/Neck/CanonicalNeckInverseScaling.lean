import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CapMetricScalingNeck

/-!
# Inverse scaling of the scalar-one recent neck

MT Lemma 17.7; section 7 of blowup-source-initial-two-carrier-producer.md.
The monitor's pass-11 helper is adopted with its exact normalization proof.
The actual scaled neck retains its source and both coordinate maps used
by the subsequent physical cylinder construction.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M47

theorem epsilonNeck_scaleMetric_inv_normalization {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    (hR : N.connection.scalarCurvature N.center = 1) {Q : ℝ} (hQ : 0 < Q) :
    (N.scaleMetric Q⁻¹ (inv_pos.mpr hQ)).epsilon = N.epsilon ∧
      (N.scaleMetric Q⁻¹ (inv_pos.mpr hQ)).scale⁻¹ ^ 2 = Q ∧
      (N.scaleMetric Q⁻¹ (inv_pos.mpr hQ)).connection.scalarCurvature
        (N.scaleMetric Q⁻¹ (inv_pos.mpr hQ)).center = Q ∧
      (N.scaleMetric Q⁻¹ (inv_pos.mpr hQ)).center = N.center ∧
      (N.scaleMetric Q⁻¹ (inv_pos.mpr hQ)).carrier = N.carrier ∧
      (N.scaleMetric Q⁻¹ (inv_pos.mpr hQ)).coordinate_map = N.coordinate_map := by
  have hscale : N.scale = 1 := by
    rw [N.scale_eq_scalar, hR, Real.one_rpow]
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl⟩
  · change (Real.sqrt Q⁻¹ * N.scale)⁻¹ ^ 2 = Q
    rw [hscale, mul_one, inv_pow, Real.sq_sqrt (inv_nonneg.mpr hQ.le), inv_inv]
  · change (M13.scaleLeviCivitaData N.connection Q⁻¹ (inv_pos.mpr hQ)).scalarCurvature N.center = Q
    rw [M13.scaleLeviCivitaData_scalarCurvature, hR, one_div, inv_inv]

end PoincareMT.M47
