import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Mass.Limit


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

theorem exists_integrable_constant_limitDensity_mass
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hl : ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)))
    (hlim : TendstoLocallyUniformlyOn (fun k z => G.reducedLengthPullback k z.1 z.2)
      l atTop (univ ×ˢ Ioi (0 : ℝ))) :
    ∃ V : ℝ, 0 ≤ V ∧ V < euclideanReducedVolume n ∧ ∀ τ : ℝ, 0 < τ →
      Integrable (fun x => τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)))
        (calibratedMetricVolume (G.limit.flow.metric (-τ))) ∧
      (∫ x, τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ))
        ∂calibratedMetricVolume (G.limit.flow.metric (-τ))) = V := by
  obtain ⟨V, hV0, hVE, hmass⟩ := G.exists_constant_limitDensity_mass P hlim
  refine ⟨V, hV0, hVE, fun τ hτ => ?_⟩
  have hslice : Continuous (fun x => l (x, τ)) :=
    hl.comp_continuous (continuous_id.prodMk continuous_const) (fun x => ⟨mem_univ x, hτ⟩)
  have hc : Continuous (fun x => τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ))) :=
    continuous_const.mul hslice.neg.rexp
  have hnonneg (x : G.limit.carrier.carrier) :
      0 ≤ τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) :=
    mul_nonneg (Real.rpow_nonneg hτ.le _) (Real.exp_nonneg _)
  have hi : Integrable (fun x => τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)))
      (calibratedMetricVolume (G.limit.flow.metric (-τ))) := by
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnonneg), hmass τ hτ]
    exact ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  have h := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hnonneg)
  rw [hmass τ hτ] at h
  have hh := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hnonneg),
    ENNReal.toReal_ofReal hV0] using hh

end PoincareConjecture.AncientCompactTimeConvergence
