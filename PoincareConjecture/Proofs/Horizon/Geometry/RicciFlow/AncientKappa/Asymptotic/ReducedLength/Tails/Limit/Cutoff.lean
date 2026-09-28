import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Tails.Limit.Moments
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitGradient.Norm
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Cutoff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

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
  (G : AncientCompactTimeConvergence S)

theorem exists_limitReducedLength_cutoff_flux_bound_on_interval
    (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hl : ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)))
    (hl0 : ∀ z ∈ univ ×ˢ Ioi (0 : ℝ), 0 ≤ l z)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ η : G.limit.carrier.carrier → ℝ,
        ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η ∧ HasCompactSupport η ∧
        (∀ x, η x ∈ Icc 0 1) ∧
        (∀ x, ((G.limit.flow.metric (-α)).edist G.limit.base x).toReal ≤ R → η x = 1) ∧
        (tsupport η ⊆ {x |
          ((G.limit.flow.metric (-α)).edist G.limit.base x).toReal ≤ 5 * R}) ∧
        ∀ τ ∈ Icc α β,
          (∫⁻ x, ENNReal.ofReal
            (τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) *
              |(G.limit.flow.metric (-τ)).inner x
                ((G.limit.flow.connection (-τ)).gradient (fun y => l (y, τ)) x)
                ((G.limit.flow.connection (-τ)).gradient η x)|)
              ∂calibratedMetricVolume (G.limit.flow.metric (-τ))) ≤ ENNReal.ofReal (C / R) := by
  let : PreconnectedSpace G.limit.carrier.carrier :=
    ⟨G.limit.carrier.connected.isPreconnected⟩
  obtain ⟨B, hB, hmoment⟩ :=
    G.exists_limitReducedLength_sqrt_moment_bound_on_interval P hl hl0 hlim hα hαβ
  let H := α ^ (-(n : ℝ) / 2) * Real.sqrt (3 / α) * heatCutoffConstant
  have hH : 0 ≤ H := mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hα.le _) (Real.sqrt_nonneg _)) heatCutoffConstant_pos.le
  refine ⟨H * B, mul_nonneg hH hB, fun R hR => ?_⟩
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hRic : ∀ t < 0, ∀ x : G.limit.carrier.carrier,
      ∀ v : TangentSpace (𝓡 n) x, 0 ≤ (G.limit.flow.connection t).ricci x v v := by
    intro t ht x v
    exact ((G.limit.flow.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (G.limit.flow.connection t).intrinsicCurvatureTensorCalculus x
      (G.limit.nonnegative_curvature_operator t ht x) v).1
  obtain ⟨η, hη, hc, hrange, hone, hsupp, hcut⟩ :=
    G.limit.flow.exists_backward_intrinsic_ball_cutoff hRic G.limit.base hα
      (G.limit.complete (-α) (neg_neg_of_pos hα)) hR
  refine ⟨η, hη, hc, hrange, hone, hsupp, fun τ hτ => ?_⟩
  have hτpos : 0 < τ := hα.trans_le hτ.1
  let g := G.limit.flow.metric (-τ)
  let D := G.limit.flow.connection (-τ)
  have hgrad : ∀ᵐ x ∂calibratedMetricVolume g,
      g.tangentNorm x (D.gradient (fun y => l (y, τ)) x) ≤
        Real.sqrt (3 / τ) * Real.sqrt (l (x, τ)) := by
    rw [calibratedMetricVolume_eq_volumeMeasure]
    exact G.reducedLengthPullback_limit_gradient_norm_bound_ae P
      (σ := id) strictMono_id l hlim hτpos
  have hpow : τ ^ (-(n : ℝ) / 2) ≤ α ^ (-(n : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hα hτ.1
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num))
  have hsqrt : Real.sqrt (3 / τ) ≤ Real.sqrt (3 / α) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) hα hτ.1)
  have hpoint : ∀ᵐ x ∂calibratedMetricVolume g,
      τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) *
          |g.inner x (D.gradient (fun y => l (y, τ)) x) (D.gradient η x)| ≤
        (H / R) * (Real.sqrt (l (x, τ)) * Real.exp (-l (x, τ))) := by
    filter_upwards [hgrad] with x hx
    have hg := hx.trans (mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _))
    have hi : |g.inner x (D.gradient (fun y => l (y, τ)) x) (D.gradient η x)| ≤
        g.tangentNorm x (D.gradient (fun y => l (y, τ)) x) *
          g.tangentNorm x (D.gradient η x) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : G.limit.carrier.carrier → Type _) :=
        ⟨g.toRiemannianMetric⟩
      exact abs_real_inner_le_norm
        (D.gradient (fun y => l (y, τ)) x : TangentSpace (𝓡 n) x)
        (D.gradient η x : TangentSpace (𝓡 n) x)
    have hi' := hi.trans (mul_le_mul hg (hcut τ hτ.1 x) (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    calc
      _ ≤ (α ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ))) *
          ((Real.sqrt (3 / α) * Real.sqrt (l (x, τ))) * (heatCutoffConstant / R)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)) hi'
          (abs_nonneg _) (mul_nonneg (Real.rpow_nonneg hα.le _) (Real.exp_nonneg _))
      _ = _ := by dsimp [H]; ring
  have hBτ : (∫⁻ x, ENNReal.ofReal (Real.sqrt (l (x, τ)) * Real.exp (-l (x, τ)))
      ∂calibratedMetricVolume g) ≤ ENNReal.ofReal B := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hmoment τ hτ).1
      (ae_of_all _ (fun x => mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)))]
    exact ENNReal.ofReal_le_ofReal (hmoment τ hτ).2
  calc
    (∫⁻ x, ENNReal.ofReal (τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) *
        |g.inner x (D.gradient (fun y => l (y, τ)) x) (D.gradient η x)|)
        ∂calibratedMetricVolume g) ≤
      ∫⁻ x, ENNReal.ofReal ((H / R) *
        (Real.sqrt (l (x, τ)) * Real.exp (-l (x, τ)))) ∂calibratedMetricVolume g :=
      lintegral_mono_ae (hpoint.mono (fun x hx => ENNReal.ofReal_le_ofReal hx))
    _ = ENNReal.ofReal (H / R) * (∫⁻ x,
        ENNReal.ofReal (Real.sqrt (l (x, τ)) * Real.exp (-l (x, τ)))
          ∂calibratedMetricVolume g) := by
      simp_rw [ENNReal.ofReal_mul (div_nonneg hH hRpos.le)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (H / R) * ENNReal.ofReal B := by gcongr
    _ = ENNReal.ofReal ((H * B) / R) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hH hRpos.le)]
      congr 1
      ring

end PoincareConjecture.AncientCompactTimeConvergence
