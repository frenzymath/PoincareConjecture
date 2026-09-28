import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Comparison.Jets.ComparisonCovariantJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.LocalTransport



noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.SingularRegularLimit.RoundComparison

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ



theorem exists_intrinsic_metric_error_bound
    {g₀ : RiemannianMetric 3 E} (D₀ : LeviCivitaData g₀) (p : E) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
        {g h₁ h₂ : RiemannianMetric 3 X} (D : LeviCivitaData g)
        {f : E → X} {U : Set E}, IsOpen U → p ∈ U →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
        (∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible) →
        (∀ y ∈ U, ∀ v w : E, g₀.inner y v w = g.inner (f y)
          (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w)) →
        ∀ ρ : ℝ, 0 ≤ ρ →
        (∀ j ≤ m, ‖iteratedFDeriv ℝ j
          (h₁.pullbackCoefficients f - h₂.pullbackCoefficients f) p‖ ≤ ρ) →
        (∑ j ∈ Finset.range (m + 1),
          (g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
            (fun y v => h₁.inner y (v 0) (v 1) - h₂.inner y (v 0) (v 1)) j) (f p)) ^ 2) ≤
          C * ρ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := MetricSurgery.exists_comparison_covariant_jet_bound
    g₀ D₀ (K := {p}) isCompact_singleton m
  refine ⟨C, hC, ?_⟩
  intro X _ _ _ g h₁ h₂ D f U hU hp hf hinv hmetric ρ hρ hjets
  let B : E → Bilin := fun y => g₀.euclideanCoefficients y +
    (h₁.pullbackCoefficients f y - h₂.pullbackCoefficients f y)
  have hB : ContDiffOn ℝ ∞ B U := by
    intro y hy
    have hfy := hf.contMDiffAt (hU.mem_nhds hy)
    exact ((g₀.contDiffAt_euclideanCoefficients y).add
      ((h₁.contDiffAt_pullbackCoefficients hfy).sub
        (h₂.contDiffAt_pullbackCoefficients hfy))).contDiffWithinAt
  obtain ⟨A, hAsmooth, heq⟩ := MetricSurgery.exists_comparison_smooth_germ hU hB hp
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp (inter_mem heq (hU.mem_nhds hp))
  have hdiff : (A - g₀.euclideanCoefficients) =ᶠ[𝓝 p]
      (h₁.pullbackCoefficients f - h₂.pullbackCoefficients f) := by
    filter_upwards [heq] with y hy
    change A y - g₀.euclideanCoefficients y = _
    rw [hy]
    dsimp [B]
    abel
  have hb := hbound univ isOpen_univ (subset_univ _) A hAsmooth.contDiffOn ρ hρ p
    (mem_singleton p) (fun j hj => by
      rw [(hdiff.iteratedFDeriv ℝ j).eq_of_nhds]
      exact hjets j hj)
  have hnorm (j : ℕ) : g₀.tensorNorm (D₀.iteratedCovariantTensorDerivative (k := 2)
      (fun y v => A y (v 0) (v 1) - g₀.inner y (v 0) (v 1)) j) p =
      g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
        (fun y v => h₁.inner y (v 0) (v 1) - h₂.inner y (v 0) (v 1)) j) (f p) := by
    apply tensorNorm_iteratedCovariantDerivative_pullback D₀ D hV
      (hf.mono (fun y hy => (hVsub hy).2))
      (fun y hy => hinv y (hVsub hy).2) (fun y hy => hmetric y (hVsub hy).2)
      ((MetricSurgery.comparison_bilinear_isSmooth hAsmooth).sub
        (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor g₀))
      ((Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor h₁).sub
        (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor h₂))
      (fun y hy v => ?_) j hpV
    rw [(hVsub hy).1]
    change (g₀.inner y (v 0) (v 1) +
      (h₁.inner (f y) _ _ - h₂.inner (f y) _ _)) - g₀.inner y (v 0) (v 1) = _
    abel
  change (∑ j ∈ Finset.range (m + 1),
    (g₀.tensorNorm (D₀.iteratedCovariantTensorDerivative (k := 2)
      (fun y v => A y (v 0) (v 1) - g₀.inner y (v 0) (v 1)) j) p) ^ 2) ≤ _ at hb
  simpa only [hnorm] using hb

end PoincareConjecture.SingularRegularLimit.RoundComparison
