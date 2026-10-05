import PoincareLib.Geometry.Riemannian.Normalization.Conclusion
import PoincareLib.Geometry.Riemannian.Normalization.Bridges
import PoincareLib.Geometry.Riemannian.Normalization.Metric.Construction
import PoincareLib.Geometry.Riemannian.Normalization.Volume.Finite
import PoincareLib.Geometry.Riemannian.Normalization.Curvature.Norm
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Distance
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.CurvatureBound
import PoincareLib.Geometry.Riemannian.Normalization.Volume.SmallBalls
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.SmallBalls
import PoincareLib.Geometry.Riemannian.Normalization.Connection.Existence
/-!
# Normalized initial metric existence proof assembly

The compact-manifold scaling, compatible-connection construction, calibrated
volume transport, and time-zero pinching bridge give the all-radius
normalization of Morgan--Tian Definition 4.10, printed p. 67.

Adapted from Mapher's reviewed `Proofs/M01.lean` at
`4a6b36794e04c3fac86663910a73a924fed43f23`. See
`references/ricci-flow/mapher/reviewed-normalized-metric.md` for source
provenance and the local representation bridges.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

universe u

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M]

/-- Every compact Hausdorff second-countable smooth three-manifold with
its Borel measurable structure admits a complete normalized metric, compatible
connection and calibrated volume. The curvature norm is at most one, the
half-Euclidean volume bound holds for every radius 0 < r <= 1, and the initial
Hamilton-Ivey pinching inequalities hold at time zero.

Sources: Morgan-Tian Definition 4.10, p. 67; Chapter 15, Section 0.6, p. 353;
Corollary 15.10 proof, p. 363. The bound holds at every radius in `(0, 1]`. -/
theorem existsNormalizedInitialMetric
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] :
    Nonempty (NormalizedInitialMetricConclusion (M := M)) := by
  obtain ⟨g⟩ : Nonempty (RiemannianMetric 3 M) :=
    existsRiemannianMetricOfCompact (n := 3) (M := M)
  obtain ⟨D⟩ : Nonempty (LeviCivitaData g) := normalization_exists_leviCivitaData g
  obtain ⟨B, _hB, hcurv⟩ := normalization_riemannEvaluation_uniform_bound D
  obtain ⟨r₀, hr₀, hball⟩ := normalization_normalizedMetricVolume_uniform_lower_bound g
  let c := max (9 * B) ((1 / r₀) ^ 2) + 1
  have hc : 0 < c := by
    have h := le_max_right (9 * B) ((1 / r₀) ^ 2)
    dsimp [c]
    nlinarith [sq_nonneg (1 / r₀)]
  have hcB : 9 * B ≤ c := by
    have h := le_max_left (9 * B) ((1 / r₀) ^ 2)
    dsimp [c]
    linarith
  have hscale : 1 ≤ Real.sqrt c * r₀ := by
    have hs : 1 / r₀ ≤ Real.sqrt c := by
      apply Real.le_sqrt_of_sq_le
      have h := le_max_right (9 * B) ((1 / r₀) ^ 2)
      dsimp [c]
      linarith
    exact (div_le_iff₀ hr₀).mp hs
  let g' := rescaledMetric g c hc
  let D' := rescaledMetric_connection g D c hc
  suffices hdata : Nonempty (NormalizedInitialMetric (M := M)) by
    obtain ⟨data⟩ := hdata
    exact ⟨{ data := data
             initial_pinching := hamiltonIveyPinchedAt_zero_of_norm_le data.connection
               data.full_curvature_bound }⟩
  refine ⟨NormalizedInitialMetric.mk g' D' (normalizedMetricVolume g') rfl
    (rescaledMetric_curvatureTensorNorm_le D B hcurv c hc hcB)
    (normalization_rescaledMetric_smallBall_lower_bound g r₀ hr₀ hball c hc hscale)
    (normalization_normalizedMetricVolume_finite g') ?_⟩
  · unfold normalizedMetricComplete
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g'.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨⟨g'.inner, g'.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
    exact complete_of_compact

end PoincareMT
