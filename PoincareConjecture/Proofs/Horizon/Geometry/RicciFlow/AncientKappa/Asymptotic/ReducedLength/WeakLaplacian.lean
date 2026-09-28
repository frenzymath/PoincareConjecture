import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.SpatialBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.CompactSupport









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

theorem ae_reducedLength_gradient_bound (P : AncientAsymptoticSolitonPredecessors K)
    (p : M) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᵐ q ∂calibratedMetricVolume (K.flow.metric (0 - τ)),
      reducedLengthGradientNormSq K.flow 0 (fun z ↦ reducedLength K.flow 0 p z.1 z.2) τ q +
        (K.flow.connection (0 - τ)).scalarCurvature q ≤
          3 * reducedLength K.flow 0 p q τ / τ := by
  obtain ⟨V⟩ := P.reduced_volume (τ + 1) (by linarith)
  obtain ⟨D⟩ := V.measure_regularity p
  have hreg : ∀ᵐ q ∂calibratedMetricVolume (K.flow.metric (0 - τ)),
      (q, τ) ∈ D.regularDomain := ae_iff.mpr (D.slice_complement_null τ hτ (by linarith))
  filter_upwards [hreg] with q hq
  obtain ⟨r⟩ := D.regular_points (q, τ) hq
  have hg := P.regular_reducedLength_gradient_bound r
  have heq := regular_reducedLength_spatial_eventuallyEq r
  convert hg using 1
  unfold reducedLengthGradientNormSq
  simp only [mvfderiv, heq.mfderiv_eq]
  rfl

theorem reducedLength_weak_laplacian_le (P : AncientAsymptoticSolitonPredecessors K)
    (p : M) {τ : ℝ} (hτ : 0 < τ) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ q, 0 ≤ φ q) :
    (∫ q, reducedLength K.flow 0 p q τ * (K.flow.connection (0 - τ)).laplacian φ q
      ∂calibratedMetricVolume (K.flow.metric (0 - τ))) ≤
      ∫ q, φ q * ((reducedLength K.flow 0 p q τ + (n : ℝ) / 2) / τ)
        ∂calibratedMetricVolume (K.flow.metric (0 - τ)) := by
  let μ := calibratedMetricVolume (K.flow.metric (0 - τ))
  let A := fun q ↦ reducedLength K.flow 0 p q τ * (K.flow.connection (0 - τ)).laplacian φ q
  let B := fun q ↦ φ q * ((reducedLength K.flow 0 p q τ + (n : ℝ) / 2) / τ)
  have hl := P.continuous_reducedLength p τ hτ
  have hA : Integrable A μ := by
    rw [show μ = (K.flow.metric (0 - τ)).volumeMeasure from
      calibratedMetricVolume_eq_volumeMeasure _]
    exact (K.flow.connection (0 - τ)).integrable_mul_laplacian_of_hasCompactSupport_right
      hl hφ hφc
  have hB : Integrable B μ := by
    rw [show μ = (K.flow.metric (0 - τ)).volumeMeasure from
      calibratedMetricVolume_eq_volumeMeasure _]
    exact (hφ.continuous.mul ((hl.add continuous_const).div_const τ)).integrable_of_hasCompactSupport
      hφc.mul_right
  obtain ⟨V⟩ := P.reduced_volume (τ + 1) (by linarith)
  have hw := V.weak_inequalities p τ hτ (by linarith) φ hφ hφc hφ0
  have hpoint : ∀ᵐ q ∂μ,
      2 * (A q - B q) ≤ reducedLengthSecondWeakIntegrand K.flow 0 p τ φ q := by
    filter_upwards [P.ae_reducedLength_gradient_bound p hτ] with q hq
    have hR := ((Classical.choice P.structural).structural M K).scalar_pos (0 - τ)
      (by linarith) q
    have hscalar : -2 * ((reducedLength K.flow 0 p q τ + (n : ℝ) / 2) / τ) ≤
        -reducedLengthGradientNormSq K.flow 0
          (fun z ↦ reducedLength K.flow 0 p z.1 z.2) τ q +
          (K.flow.connection (0 - τ)).scalarCurvature q +
          (reducedLength K.flow 0 p q τ - (n : ℝ)) / τ := by
      field_simp at hq ⊢
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hscalar (hφ0 q)
    dsimp only [A, B, reducedLengthSecondWeakIntegrand]
    nlinarith
  have hi := (integral_mono_ae ((hA.sub hB).const_mul 2) hw.2.1 hpoint).trans hw.2.2.2
  simp only [Pi.sub_apply] at hi
  rw [integral_const_mul, integral_sub hA hB] at hi
  change (∫ q, A q ∂μ) ≤ ∫ q, B q ∂μ
  linarith

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
