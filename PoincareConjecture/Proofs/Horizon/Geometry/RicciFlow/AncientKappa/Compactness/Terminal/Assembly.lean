import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.Completeness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.CurvatureConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Inheritance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

namespace AncientKappaSequence

local instance assemblyCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

theorem closedLimit_metricComplete_of_source_bounds
    (C : ℕ → FlowCarrier.{0} 3)
    (K : ∀ k, AncientKappaSolution 3 (C k).carrier)
    (p : ∀ k, (C k).carrier)
    (L : FlowCarrier.{0} 3)
    (F : RicciFlow 3 L.carrier (Iic 0)) (q : L.carrier)
    {τ : ℝ} (hτ : τ ≤ 0)
    (hreference : L.metricComplete (F.metric τ))
    (σ : ℕ → ℕ) (e : ∀ k, L.carrier → (C (σ k)).carrier)
    (hbase : ∀ᶠ k in atTop, e k q = p (σ k))
    (hsmooth : ∀ A : Set L.carrier, IsCompact A → ∀ᶠ k in atTop,
      ∀ x ∈ A, ContMDiffAt (𝓡 3) (𝓡 3) 1 (e k) x)
    (hbound : ∀ A : Set L.carrier, IsCompact A → ∀ᶠ k in atTop,
      ∀ x ∈ A, ∀ v : L.tangent x,
        ((K (σ k)).flow.metric 0).tangentNorm (e k x)
            (mfderiv (𝓡 3) (𝓡 3) (e k) x v) ≤
          2 * (F.metric 0).tangentNorm x v)
    (hsource : ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 ≤ B ∧
      ∀ k t, t ≤ 0 → ∀ x ∈ ((K k).flow.metric 0).ball (p k) A,
        |((K k).flow.connection t).curvatureTensorNorm x| ≤ B)
    (hconverges : ∀ t : ℝ, t ≤ 0 → ∀ x : L.carrier,
      Tendsto (fun k => ((K (σ k)).flow.connection t).curvatureTensorNorm (e k x))
        atTop (𝓝 ((F.connection t).curvatureTensorNorm x))) :
    L.metricComplete (F.metric 0) := by
  have hball : ∀ A : ℝ, 0 < A → ∀ x ∈ (F.metric 0).ball q A,
      ∀ᶠ k in atTop, e k x ∈ ((K (σ k)).flow.metric 0).ball (p (σ k)) (2 * A) := by
    intro A hA x hx
    exact AncientCompactness.eventually_mem_source_ball_of_compact_pullback_bound
      L (fun k => C (σ k)) (F.metric 0) (fun k => (K (σ k)).flow.metric 0) q
      (fun k => p (σ k)) e hbase hsmooth hbound hx
  have hcurv : ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Icc τ 0, ∀ x ∈ (F.metric 0).ball q A,
        (F.connection t).curvatureTensorNorm x ≤ B := by
    intro A hA
    obtain ⟨B, hB, hbound'⟩ := terminal_curvature_bound_of_source_convergence
      C K p L F q σ e hsource hball hconverges A hA
    exact ⟨B, hB, fun t ht x hx => hbound' t ht.2 x hx⟩
  exact RicciFlow.metricComplete_terminal_of_local_curvature_bound L F q hτ hreference hcurv

end AncientKappaSequence

namespace NormalizedKappaSolutionSequence

local instance terminalAssemblySourceConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
  (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
    (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)

theorem closedLimit_complete_at_zero
    (F : RicciFlow 3 G.limitCarrier.carrier (Iic 0))
    (hF : ∀ t : ℝ, t < 0 → F.metric t = G.limitFlow.metric (t + 1))
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    G.limitCarrier.metricComplete (F.metric 0) := by
  have hreference : G.limitCarrier.metricComplete (F.metric (-1)) := by
    rw [hF (-1) (by norm_num), show (-1 : ℝ) + 1 = 0 by ring]
    exact hcomplete
  apply AncientKappaSequence.closedLimit_metricComplete_of_source_bounds
    (fun k => (S.term k).carrier) (fun k => (S.term k).flow) (fun k => (S.term k).base)
    G.limitCarrier F G.base (by norm_num : (-1 : ℝ) ≤ 0) hreference
    G.subsequence G.embedding (Eventually.of_forall G.base_preserving)
  · intro A hA
    exact (S.eventually_embedding_contMDiffAt_on_compact G hA).mono
      (fun k hk x hx => (hk x hx).of_le (by simp))
  · intro A hA
    exact S.eventually_terminal_pullback_tangentNorm_le_twice G F hF P hcontrol
      hcomplete hA (show (0 : ℝ) ≤ 0 from le_refl 0)
  · exact hcontrol
  · exact S.tendsto_terminal_curvatureTensorNorm G F hF P hcontrol hcomplete

theorem closedLimit_complete
    (F : RicciFlow 3 G.limitCarrier.carrier (Iic 0))
    (hF : ∀ t : ℝ, t < 0 → F.metric t = G.limitFlow.metric (t + 1))
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    ∀ t : ℝ, t ≤ 0 → G.limitCarrier.metricComplete (F.metric t) := by
  intro t ht
  rcases lt_or_eq_of_le ht with ht | rfl
  · rw [hF t ht]
    exact S.interiorLimit_complete G P hcontrol hcomplete (t + 1) (by linarith)
  · exact S.closedLimit_complete_at_zero G F hF P hcontrol hcomplete

end NormalizedKappaSolutionSequence
end PoincareConjecture
