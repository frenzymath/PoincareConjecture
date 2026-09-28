import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RescaledLimit
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RescaledLimitBirth












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace
local notation "V" => MetricCoefficient 3

noncomputable local instance rescaledLimitConstructionCoefficientNorm : NormedAddCommGroup V :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rescaledLimitConstructionCoefficientSpace : NormedSpace ℝ V :=
  ContinuousLinearMap.toNormedSpace







theorem exists_rescaled_partial_flow_from_sequence
    (g0 : StandardInitialMetric) {T : ℝ} (hT : 0 < T)
    (f : ℕ → ℝ × E → V)
    (hsmooth : ∀ R : ℝ, 0 < R → ∀ᶠ k in atTop,
      ContDiffOn ℝ ∞ (f k) (Ioo 0 T ×ˢ g0.metric.ball 0 R))
    (hbound : ∀ R : ℝ, 0 < R → ∀ K : Set (ℝ × E),
      IsCompact K → K ⊆ Ioo 0 T ×ˢ g0.metric.ball 0 R → ∀ m : ℕ,
        ∃ C : ℝ, ∀ᶠ k in atTop, ∀ p ∈ K, ‖iteratedFDeriv ℝ m (f k) p‖ ≤ C)
    (hsymm : ∀ p ∈ Ioo 0 T ×ˢ (univ : Set E),
      ∀ᶠ k in atTop, ∀ v w, f k p v w = f k p w v)
    (hell : ∀ p ∈ Ioo 0 T ×ˢ (univ : Set E), ∃ a : ℝ, 0 < a ∧
      ∀ᶠ k in atTop, ∀ v : E, a * ‖v‖ ^ 2 ≤ f k p v v)
    (hevol : ∀ p ∈ Ioo 0 T ×ˢ (univ : Set E), ∀ᶠ k in atTop,
      HasDerivAt (fun t => f k (t, p.2))
        (ricciFlowOperator 3 (metricTwoJet (fun x => f k (p.1, x)) p.2)) p.1)
    (hbirth : ∀ m : ℕ, ∀ x : E,
      Tendsto (fun k => iteratedFDeriv ℝ m (fun y => f k (0, y)) x) atTop
        (𝓝 (iteratedFDeriv ℝ m g0.metric.euclideanCoefficients x)))
    (hmodulus : ∀ m : ℕ, ∀ K : Set E, IsCompact K → ∃ L : ℝ, 0 ≤ L ∧
      ∀ t ∈ Ioo 0 T, ∀ x ∈ K, ∀ᶠ k in atTop,
        ‖iteratedFDeriv ℝ m (fun y => f k (t, y)) x -
          iteratedFDeriv ℝ m (fun y => f k (0, y)) x‖ ≤ L * t)
    (hcurv : ∀ T0 : ℝ, 0 ≤ T0 → T0 < T →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∀ᶠ k in atTop,
        ∀ t ∈ Icc 0 T0, ∀ x ∈ g0.metric.ball 0 R,
          standardJetCurvatureNorm (metricTwoJet (fun y => f k (t, y)) x) ≤ K) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∃ S : PartialStandardCapFlow g0,
      S.lifetime = T ∧ CompactSmoothConvergenceOn (fun k => f (sigma k))
        (fun p => (S.flow.metric p.1).euclideanCoefficients p.2) atTop
        (Ioo 0 T ×ˢ univ) := by
  obtain ⟨sigma, hsigma, b, hb⟩ :=
    exists_rescaled_limit_on_standard_space g0 isOpen_Ioo f hsmooth hbound
  obtain ⟨S, hS, hconv⟩ := exists_rescaled_partial_flow_of_compactSmooth g0 hT hb
    (fun p hp => hsigma.tendsto_atTop.eventually (hsymm p hp))
    (fun p hp => by
      obtain ⟨a, ha, he⟩ := hell p hp
      exact ⟨a, ha, hsigma.tendsto_atTop.eventually he⟩)
    (fun p hp => hsigma.tendsto_atTop.eventually (hevol p hp))
    (fun m x => (hbirth m x).comp hsigma.tendsto_atTop)
    (fun m K hK => by
      obtain ⟨L, hL, hmod⟩ := hmodulus m K hK
      exact ⟨L, hL, fun t ht x hx => hsigma.tendsto_atTop.eventually (hmod t ht x hx)⟩)
    (fun T0 hT0 hT0T => by
      obtain ⟨K, hK, hcurvK⟩ := hcurv T0 hT0 hT0T
      exact ⟨K, hK, fun R hR => hsigma.tendsto_atTop.eventually (hcurvK R hR)⟩)
  exact ⟨sigma, hsigma, S, hS, hconv⟩

end PoincareConjecture.M44
