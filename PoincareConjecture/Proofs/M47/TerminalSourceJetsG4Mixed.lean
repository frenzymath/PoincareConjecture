import PoincareConjecture.Proofs.M47.TerminalSourceJetsG4
import PoincareConjecture.Proofs.M47.TerminalSourceJetsMixed











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

variable {α : Type v} (l : Filter α) (M : α → Type u)
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)]
  [∀ k, SecondCountableTopology (M k)]



theorem terminalSourceJetsG4_same_chart_mixed
    (P : RicciFlowCurvatureTheory.{u})
    {τ R H ρ : ℝ} (hτ : 0 < τ) (hH : 0 < H) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * ρ →
      (H * s ^ 2) * Real.exp (max 1 (H * s ^ 2)) ≤ 3)
    (F : ∀ k, RicciFlow 3 (M k) (Icc (-τ) 0))
    (C : ∀ k, TerminalSourceChart ((F k).metric 0) R)
    (hG4 : ∀ᶠ k in l, ∀ t ∈ Icc (-τ) 0,
      ∀ y ∈ (C k).chart '' Metric.ball 0 R,
        ((F k).connection t).curvatureTensorNorm y ≤ H)
    (fminus : α → ℝ × E → V)
    (hactual : ∀ᶠ k in l, EqOn (fminus k)
      (fun p : ℝ × E => ((F k).metric p.1).pullbackCoefficients (C k).chart p.2)
      (Ioo (-τ) 0 ×ˢ Metric.ball 0 R))
    {K : Set E} (hK : K ⊆ Metric.closedBall 0 ρ) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in l,
      ∀ t ∈ Ioo (-(τ / 2)) 0, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (fminus k) (t, x)‖ ≤ B := by
  exact terminalSourceJets_eventually_mixed_on_buffer l M P hτ hH hρ hρR
    hsmall F C hG4 fminus hactual hK m

end PoincareConjecture.M47
