import PoincareLib.Geometry.RicciFlow.Blowup.Construction.PartialLimits.PartialScalarConvergence
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.StaticLimit.StaticTerminalReadout
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.Terminal.TerminalSourceBounds

/-!
# Actual terminal scalar convergence and short-control readout

Morgan--Tian Claim 11.5 and the conclusion of Theorem 11.1, pp. 270--271.
The same static embeddings retain the original normalized scalar uniformly
on compact sets. A separately proved global limit bound then supplies the
radius-independent short controls, using all-radius compact capture.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

/-- The original normalized terminal scalars converge uniformly on every
compact set along the actual static embeddings (Theorem 11.1, p. 271). -/
theorem tendstoUniformlyOn_terminal_normalized_scalar
    (S : GeneralizedBlowupSequence.{u})
    (G : PartialPointedMetricConvergence (terminalComponentMetric S)
      (terminalComponentBase S) 1)
    (D : LeviCivitaData G.limitMetric) (K : Set G.limitCarrier.carrier)
    (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun k x => (S.flow (G.subsequence k)).scalar
        ⟨(S.base (G.subsequence k)).1, (G.embedding k x).val⟩ / S.scale (G.subsequence k))
      D.scalarCurvature atTop K := by
  simpa only [terminalComponentMetric_scalarCurvature] using
    G.tendstoUniformlyOn_scalarCurvature
      (fun k => (terminalComponentMetric S k).leviCivitaData) D K hK

/-- The actual limit connection has scalar one at the retained basepoint
(Claim 11.5, p. 270). -/
theorem terminal_static_limit_base_scalar
    (S : GeneralizedBlowupSequence.{u})
    (G : PartialPointedMetricConvergence (terminalComponentMetric S)
      (terminalComponentBase S) 1)
    (D : LeviCivitaData G.limitMetric) : D.scalarCurvature G.base = 1 := by
  have h := (G.tendstoUniformlyOn_scalarCurvature
    (fun k => (terminalComponentMetric S k).leviCivitaData) D
    {G.base} isCompact_singleton).tendsto_at (mem_singleton G.base)
  have hsource (k : ℕ) :
      (terminalComponentMetric S (G.subsequence k)).leviCivitaData.scalarCurvature
        (G.embedding k G.base) = 1 := by
    rw [G.base_preserving]
    exact terminalComponentMetric_base_scalar S (G.subsequence k) _
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (D.scalarCurvature G.base)) := by
    simpa only [hsource] using h
  exact tendsto_nhds_unique hconst tendsto_const_nhds

/-- All-radius coverage and a global bound on the actual static scalar
give common short controls on its original selected sequence
(Theorem 11.1 after Claim 11.7, p. 271). -/
theorem shortControls_of_static_terminal_limit_bound
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (G : PartialPointedMetricConvergence (terminalComponentMetric S)
      (terminalComponentBase S) 1)
    (D : LeviCivitaData G.limitMetric)
    (hcoverage : ∀ A : ℝ, 0 < A → ∃ l : ℕ, ∀ᶠ k in atTop,
      (terminalComponentMetric S (G.subsequence k)).ball
        (terminalComponentBase S (G.subsequence k)) A ⊆
          G.embedding k '' G.exhaustion l)
    {B : ℝ} (hbound : ∀ x : G.limitCarrier.carrier, D.scalarCurvature x ≤ B) :
    Nonempty (ShortControlledBlowupHypotheses
      (reindexedBlowupSequence S G.subsequence G.subsequence_strictMono) kappa r₀) :=
  shortControls_of_terminal_scalar_convergence hC H G.subsequence G.subsequence_strictMono
    G.limitCarrier G.limitMetric D (fun k x => (G.embedding k x).val)
    (exists_eventually_terminal_source_compact_capture S G hcoverage)
    (tendstoUniformlyOn_terminal_normalized_scalar S G D) hbound

end PoincareMT.M30
