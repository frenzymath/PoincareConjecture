import PoincareConjecture.Proofs.M30.Thm11_1.TerminalNormalCovers
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.StaticNormalCoverLimit
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.UniformNormalCover
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.SourceMetric










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable




theorem exists_complete_terminal_static_limit
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (hbound : GeneralizedBlowupBoundedDistance S) :
    ∃ G : PartialPointedMetricConvergence (terminalComponentMetric S)
        (terminalComponentBase S) 1,
      G.limitCarrier.metricComplete G.limitMetric ∧
        ∀ A : ℝ, 0 < A → ∃ l : ℕ, ∀ᶠ k in atTop,
          (terminalComponentMetric S (G.subsequence k)).ball
            (terminalComponentBase S (G.subsequence k)) A ⊆
              G.embedding k '' G.exhaustion l := by
  classical
  have hNormal : UniformNormalCoverService.{u} :=
    M28.exists_uniform_normalCover_of_local_noncollapse
  obtain ⟨sigma, hsigma, R, rho, N, hsize, hcovers, hcurv⟩ :=
    exists_terminalComponent_normal_covers hNormal hC H hbound
  let : ∀ k, MetricSpace (terminalComponentCarrier S (sigma k)).carrier :=
    fun k => (terminalComponentCarrier S (sigma k)).metricSpaceOf
      (terminalComponentMetric S (sigma k))
  let cover := fun k j (hjk : j ≤ k) => Classical.choice (hcovers k j hjk)
  obtain ⟨G, hcomplete, hcoverage⟩ := exists_complete_static_limit_of_normal_covers
    (fun k => terminalComponentMetric S (sigma k))
    (fun k => terminalComponentBase S (sigma k))
    (fun k => (terminalComponentMetric S (sigma k)).leviCivitaData)
    hsize cover (fun _ _ _ => rfl) hcurv
  exact ⟨G.reindex hsigma, hcomplete, hcoverage⟩

end PoincareConjecture.M30
