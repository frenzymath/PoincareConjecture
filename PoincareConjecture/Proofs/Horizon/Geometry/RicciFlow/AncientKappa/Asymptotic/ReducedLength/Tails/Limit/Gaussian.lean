import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Tails.Limit.Bounds
import PoincareConjecture.Proofs.Horizon.Analysis.Measure.GaussianTails.PolynomialVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.AncientCompactTimeConvergence

open Poincare.Analysis RiemannianMetric

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}
  (G : AncientCompactTimeConvergence S)

theorem exists_limitReducedLength_half_gaussian_bound_on_interval
    (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ τ ∈ Icc α β,
      ∀ x : G.limit.carrier.carrier,
        Real.exp (-l (x, τ) / 2) ≤ A * Real.exp
          (-a * ((G.limit.flow.metric (-τ)).edist G.limit.base x).toReal ^ 2) := by
  let D := 4 * (16 * (2 * (n : ℝ) + 604) ^ 2 * β)
  let B := (n : ℝ) / 2 * max (β ^ 2) (α ^ 2)⁻¹ + 1
  have hβ : 0 < β := hα.trans_le hαβ
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D⁻¹ / 2, Real.exp (B / 2), by positivity, Real.exp_pos _, ?_⟩
  intro τ hτ x
  have hτpos : 0 < τ := hα.trans_le hτ.1
  have hτ2 : τ ^ 2 ≤ β ^ 2 := (sq_le_sq₀ hτpos.le hβ.le).mpr hτ.2
  have hα2 : α ^ 2 ≤ τ ^ 2 := (sq_le_sq₀ hα.le hτpos.le).mpr hτ.1
  have hinv : (τ ^ 2)⁻¹ ≤ (α ^ 2)⁻¹ := inv_anti₀ (sq_pos_of_pos hα) hα2
  have hmax : max (τ ^ 2) (τ ^ 2)⁻¹ ≤ max (β ^ 2) (α ^ 2)⁻¹ :=
    max_le_max hτ2 hinv
  have hB := mul_le_mul_of_nonneg_left hmax (show 0 ≤ (n : ℝ) / 2 by positivity)
  have hden : 4 * (16 * (2 * (n : ℝ) + 604) ^ 2 * τ) ≤ D := by
    dsimp [D]
    gcongr
    exact hτ.2
  have hdenpos : 0 < 4 * (16 * (2 * (n : ℝ) + 604) ^ 2 * τ) := by positivity
  have hd := div_le_div_of_nonneg_left
    (sq_nonneg (((G.limit.flow.metric (-τ)).edist G.limit.base x).toReal)) hdenpos hden
  have hlower := G.reducedLengthPullback_limit_lower_bound P hlim hτpos x
  have hl : ((G.limit.flow.metric (-τ)).edist G.limit.base x).toReal ^ 2 / D - B ≤
      l (x, τ) := by dsimp [B]; linarith
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [div_eq_mul_inv] at hl ⊢
  nlinarith

theorem exists_limitReducedLength_half_gaussian_tail_on_interval
    (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ τ ∈ Icc α β, ∀ R : ℝ, 0 ≤ R →
      (∫⁻ x in ((G.limit.flow.metric (-τ)).ball G.limit.base R)ᶜ,
        ENNReal.ofReal (Real.exp (-l (x, τ) / 2))
          ∂calibratedMetricVolume (G.limit.flow.metric (-τ))) ≤
        ENNReal.ofReal (C * Real.exp (-a * R ^ 2)) := by
  obtain ⟨a, A, ha, hA, hgauss⟩ :=
    G.exists_limitReducedLength_half_gaussian_bound_on_interval P hlim hα hαβ
  let C := A * (euclideanUnitBallVolume n * gaussianShellSum n (a / 2))
  have hC : 0 ≤ C := mul_nonneg hA.le (mul_nonneg
    (euclideanUnitBallVolume_nonneg n) (gaussianShellSum_nonneg n (a / 2)))
  refine ⟨a / 2, C, by positivity, hC, ?_⟩
  intro τ hτ R hR
  have hτpos : 0 < τ := hα.trans_le hτ.1
  let g := G.limit.flow.metric (-τ)
  let : PreconnectedSpace G.limit.carrier.carrier :=
    ⟨G.limit.carrier.connected.isPreconnected⟩
  let := g.toMetricSpace
  let d := fun x => (g.edist G.limit.base x).toReal
  have hd : Measurable d := (continuous_const.dist continuous_id).measurable
  have hvol (m : ℕ) : calibratedMetricVolume g {x | d x < (m : ℝ) + 1} ≤
      ENNReal.ofReal (euclideanUnitBallVolume n * ((m : ℝ) + 1) ^ n) := by
    have heq : {x | d x < (m : ℝ) + 1} = g.ball G.limit.base ((m : ℝ) + 1) := by
      ext x
      exact (ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top G.limit.base x)).symm
    rw [heq]
    exact G.limit_ball_volume_le_euclidean P hτpos G.limit.base (by positivity)
  have hcomp : (g.ball G.limit.base R)ᶜ = {x | R ≤ d x} := by
    ext x
    change ¬ g.edist G.limit.base x < ENNReal.ofReal R ↔ R ≤ d x
    rw [ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top G.limit.base x), not_lt]
  have htail := lintegral_gaussian_tail_le_of_sublevel_volume hd
    (fun x => ENNReal.toReal_nonneg) ha (euclideanUnitBallVolume_nonneg n) hR hvol
  change (∫⁻ x in (g.ball G.limit.base R)ᶜ,
    ENNReal.ofReal (Real.exp (-l (x, τ) / 2)) ∂calibratedMetricVolume g) ≤ _
  rw [hcomp]
  calc
    (∫⁻ x in {x | R ≤ d x}, ENNReal.ofReal (Real.exp (-l (x, τ) / 2))
        ∂calibratedMetricVolume g) ≤
        ∫⁻ x in {x | R ≤ d x}, ENNReal.ofReal A *
          ENNReal.ofReal (Real.exp (-a * (d x) ^ 2)) ∂calibratedMetricVolume g := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul hA.le]
      exact ENNReal.ofReal_le_ofReal (hgauss τ hτ x)
    _ = ENNReal.ofReal A * (∫⁻ x in {x | R ≤ d x},
        ENNReal.ofReal (Real.exp (-a * (d x) ^ 2)) ∂calibratedMetricVolume g) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal
        (Real.exp (-a / 2 * R ^ 2) *
          (euclideanUnitBallVolume n * gaussianShellSum n (a / 2))) := by gcongr
    _ = ENNReal.ofReal (C * Real.exp (-(a / 2) * R ^ 2)) := by
      rw [← ENNReal.ofReal_mul hA.le]
      simp only [neg_div]
      congr 1
      dsimp [C]
      ring

end PoincareConjecture.AncientCompactTimeConvergence
