import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.LimitRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.Exponential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

universe u
namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem limitReducedLength_slice_locally_lipschitz
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    {τ : ℝ} (hτ : 0 < τ) :
    ∀ a : G.limit.carrier.carrier, ∃ O : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen O ∧ (chartAt (EuclideanSpace ℝ (Fin n)) a) a ∈ O ∧
      O ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target ∧
      ∃ C : ℝ≥0, LipschitzOnWith C
        ((fun x => l (x, τ)) ∘ (chartAt (EuclideanSpace ℝ (Fin n)) a).symm) O := by
  intro a
  let e := chartAt (EuclideanSpace ℝ (Fin n)) a
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp e.open_target (e a)
    (mem_chart_target _ a)
  have hs : Metric.closedBall (e a) (2 * (δ / 4)) ⊆ e.target := by
    intro x hx
    apply hball
    change dist x (e a) < δ
    have hd : dist x (e a) ≤ 2 * (δ / 4) := hx
    linarith
  obtain ⟨C, hC⟩ := G.reducedLengthPullback_limit_lipschitz_on_chart_cylinder
    P hσ l hlim a (show 0 < δ / 4 by positivity) hτ (le_refl τ) hs
  refine ⟨Metric.ball (e a) (δ / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), ?_, C, ?_⟩
  · exact Metric.ball_subset_closedBall.trans
      ((Metric.closedBall_subset_closedBall (by linarith)).trans hs)
  · simpa only [Function.comp_def, mul_one] using hC.comp
      (LipschitzWith.prodMk_right τ).lipschitzOnWith
      (fun x hx => ⟨Metric.ball_subset_closedBall hx, le_refl τ, le_refl τ⟩)

theorem limitDensity_integral_laplacian_eq_gradient
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hl : ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)))
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    {τ : ℝ} (hτ : 0 < τ) {χ : G.limit.carrier.carrier → ℝ}
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (hc : HasCompactSupport χ) :
    (∫ x, τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) *
      (G.limit.flow.connection (-τ)).laplacian χ x
      ∂(G.limit.flow.metric (-τ)).volumeMeasure) =
    ∫ x, τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) *
      (G.limit.flow.metric (-τ)).inner x
        ((G.limit.flow.connection (-τ)).gradient (fun y => l (y, τ)) x)
        ((G.limit.flow.connection (-τ)).gradient χ x)
      ∂(G.limit.flow.metric (-τ)).volumeMeasure := by
  have hlc : Continuous (fun x => l (x, τ)) := hl.comp_continuous
    (continuous_id.prodMk continuous_const) (fun x => ⟨mem_univ x, hτ⟩)
  have heq := ((G.limit.flow.connection (-τ)).integral_exp_neg_mul_laplacian_of_locally_lipschitz
    hlc (G.limitReducedLength_slice_locally_lipschitz P hσ l hlim hτ) hχ hc).2
  simp only [mul_assoc, integral_const_mul]
  rw [heq]

theorem abs_limitDensity_integral_laplacian_le
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hl : ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)))
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    {τ : ℝ} (hτ : 0 < τ) {χ : G.limit.carrier.carrier → ℝ}
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (hc : HasCompactSupport χ)
    {B : ℝ} (hB : 0 ≤ B)
    (hflux : (∫⁻ x, ENNReal.ofReal
      (τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) *
        |(G.limit.flow.metric (-τ)).inner x
          ((G.limit.flow.connection (-τ)).gradient (fun y => l (y, τ)) x)
          ((G.limit.flow.connection (-τ)).gradient χ x)|)
      ∂(G.limit.flow.metric (-τ)).volumeMeasure) ≤ ENNReal.ofReal B) :
    |∫ x, τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) *
      (G.limit.flow.connection (-τ)).laplacian χ x
      ∂(G.limit.flow.metric (-τ)).volumeMeasure| ≤ B := by
  rw [G.limitDensity_integral_laplacian_eq_gradient P hσ l hl hlim hτ hχ hc]
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  have hn (x : G.limit.carrier.carrier) :
      0 ≤ τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) :=
    mul_nonneg (Real.rpow_nonneg hτ.le _) (Real.exp_nonneg _)
  have hb := enorm_integral_le_lintegral_enorm
    (μ := (G.limit.flow.metric (-τ)).volumeMeasure)
    (fun x => τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) *
      (G.limit.flow.metric (-τ)).inner x
        ((G.limit.flow.connection (-τ)).gradient (fun y => l (y, τ)) x)
        ((G.limit.flow.connection (-τ)).gradient χ x))
  simp only [Real.enorm_eq_ofReal_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hτ.le _), abs_of_nonneg (Real.exp_nonneg _)] at hb
  exact hb.trans hflux

end PoincareConjecture.AncientCompactTimeConvergence
