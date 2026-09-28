import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.WeakGradient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.HamiltonJacobi









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



theorem reducedLength_second_weak_gradient_inequality
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ q, 0 ≤ φ q) :
    let μ := calibratedMetricVolume (K.flow.metric (0 - τ))
    let B := fun q => φ q * (-reducedLengthGradientNormSq K.flow 0
      (fun z => reducedLength K.flow 0 p z.1 z.2) τ q +
      (K.flow.connection (0 - τ)).scalarCurvature q +
      (reducedLength K.flow 0 p q τ - (n : ℝ)) / τ)
    let D := fun q => mvfderiv (𝓡 n) (fun x => reducedLength K.flow 0 p x τ) q
      ((K.flow.connection (0 - τ)).gradient φ q)
    Integrable B μ ∧ Integrable D μ ∧ (∫ q, B q ∂μ) - 2 * (∫ q, D q ∂μ) ≤ 0 := by
  dsimp only
  let μ := calibratedMetricVolume (K.flow.metric (0 - τ))
  let A := fun q => reducedLength K.flow 0 p q τ *
    (K.flow.connection (0 - τ)).laplacian φ q
  let B := fun q => φ q * (-reducedLengthGradientNormSq K.flow 0
    (fun z => reducedLength K.flow 0 p z.1 z.2) τ q +
    (K.flow.connection (0 - τ)).scalarCurvature q +
    (reducedLength K.flow 0 p q τ - (n : ℝ)) / τ)
  let D := fun q => mvfderiv (𝓡 n) (fun x => reducedLength K.flow 0 p x τ) q
    ((K.flow.connection (0 - τ)).gradient φ q)
  obtain ⟨X⟩ := (K.flow.metric 0).nonempty_compactExhaustion
  let : SigmaCompactSpace M :=
    SigmaCompactSpace_iff_exists_compact_covering.mpr ⟨X, X.isCompact, X.iUnion_eq⟩
  have hgreen := (K.flow.connection (0 - τ)).integral_mul_laplacian_of_locally_lipschitz
    (P.continuous_reducedLength p τ hτ)
    (P.reducedLength_lipschitz_coordinate_neighborhoods p hτ) hφ hφc
  have hA : Integrable A μ := by
    rw [show μ = (K.flow.metric (0 - τ)).volumeMeasure from
      calibratedMetricVolume_eq_volumeMeasure _]
    exact (K.flow.connection (0 - τ)).integrable_mul_laplacian_of_hasCompactSupport_right
      (P.continuous_reducedLength p τ hτ) hφ hφc
  obtain ⟨V⟩ := P.reduced_volume (τ + 1) (by linarith)
  have hw := V.weak_inequalities p τ hτ (by linarith) φ hφ hφc hφ0
  have hB : Integrable B μ := by
    convert hw.2.1.sub (hA.const_mul 2) using 1
    funext q
    dsimp only [B, A, reducedLengthSecondWeakIntegrand, Pi.sub_apply]
    ring
  have hD : Integrable D μ := by
    simpa only [μ, D, calibratedMetricVolume_eq_volumeMeasure] using hgreen.1
  refine ⟨hB, hD, ?_⟩
  have heq : reducedLengthSecondWeakIntegrand K.flow 0 p τ φ =
      fun q => B q + 2 * A q := by
    funext q
    dsimp only [B, A, reducedLengthSecondWeakIntegrand]
    ring
  have hi := hw.2.2.2
  rw [heq, integral_add hB (hA.const_mul 2), integral_const_mul] at hi
  have hAD : (∫ q, A q ∂μ) = -(∫ q, D q ∂μ) := by
    simpa only [A, D, μ, calibratedMetricVolume_eq_volumeMeasure] using hgreen.2
  rw [hAD] at hi
  change (∫ q, B q ∂μ) - 2 * (∫ q, D q ∂μ) ≤ 0
  linarith

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
