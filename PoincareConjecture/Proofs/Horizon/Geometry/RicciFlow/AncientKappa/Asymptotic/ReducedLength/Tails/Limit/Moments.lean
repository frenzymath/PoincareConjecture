import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Tails.Limit.Gaussian







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

private theorem sqrt_mul_exp_neg_le_exp_neg_half {y : ℝ} (hy : 0 ≤ y) :
    Real.sqrt y * Real.exp (-y) ≤ Real.exp (-y / 2) := by
  have hs : Real.sqrt y ≤ Real.exp (y / 2) := by
    have h := Real.add_one_le_exp (y / 2)
    nlinarith [Real.sq_sqrt hy, sq_nonneg (Real.sqrt y - 1)]
  calc
    Real.sqrt y * Real.exp (-y) ≤ Real.exp (y / 2) * Real.exp (-y) :=
      mul_le_mul_of_nonneg_right hs (Real.exp_nonneg _)
    _ = Real.exp (-y / 2) := by rw [← Real.exp_add]; congr 1; ring

theorem exists_limitReducedLength_sqrt_gaussian_tail_on_interval
    (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hl0 : ∀ z ∈ univ ×ˢ Ioi (0 : ℝ), 0 ≤ l z)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ τ ∈ Icc α β, ∀ R : ℝ, 0 ≤ R →
      (∫⁻ x in ((G.limit.flow.metric (-τ)).ball G.limit.base R)ᶜ,
        ENNReal.ofReal (Real.sqrt (l (x, τ)) * Real.exp (-l (x, τ)))
          ∂calibratedMetricVolume (G.limit.flow.metric (-τ))) ≤
        ENNReal.ofReal (C * Real.exp (-a * R ^ 2)) := by
  obtain ⟨a, C, ha, hC, hbound⟩ :=
    G.exists_limitReducedLength_half_gaussian_tail_on_interval P hlim hα hαβ
  refine ⟨a, C, ha, hC, fun τ hτ R hR => ?_⟩
  apply le_trans _ (hbound τ hτ R hR)
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal
    (sqrt_mul_exp_neg_le_exp_neg_half (hl0 (x, τ) ⟨mem_univ x, hα.trans_le hτ.1⟩))

theorem exists_limitReducedLength_sqrt_moment_bound_on_interval
    (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hl : ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)))
    (hl0 : ∀ z ∈ univ ×ˢ Ioi (0 : ℝ), 0 ≤ l z)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Icc α β,
      Integrable (fun x => Real.sqrt (l (x, τ)) * Real.exp (-l (x, τ)))
        (calibratedMetricVolume (G.limit.flow.metric (-τ))) ∧
      (∫ x, Real.sqrt (l (x, τ)) * Real.exp (-l (x, τ))
        ∂calibratedMetricVolume (G.limit.flow.metric (-τ))) ≤ C := by
  obtain ⟨a, C, -, hC, hbound⟩ :=
    G.exists_limitReducedLength_sqrt_gaussian_tail_on_interval P hl0 hlim hα hαβ
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have hτpos : 0 < τ := hα.trans_le hτ.1
  let g := G.limit.flow.metric (-τ)
  have hslice : Continuous (fun x => l (x, τ)) :=
    hl.comp_continuous (continuous_id.prodMk continuous_const)
      (fun x => ⟨mem_univ x, hτpos⟩)
  have hc : Continuous (fun x => Real.sqrt (l (x, τ)) * Real.exp (-l (x, τ))) :=
    hslice.sqrt.mul hslice.neg.rexp
  have hnonneg (x : G.limit.carrier.carrier) :
      0 ≤ Real.sqrt (l (x, τ)) * Real.exp (-l (x, τ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
  have hempty : g.ball G.limit.base 0 = ∅ := by
    ext x
    simp [RiemannianMetric.ball]
  have hb := hbound τ hτ 0 le_rfl
  change (∫⁻ x in (g.ball G.limit.base 0)ᶜ,
    ENNReal.ofReal (Real.sqrt (l (x, τ)) * Real.exp (-l (x, τ)))
      ∂calibratedMetricVolume g) ≤ _ at hb
  rw [hempty, compl_empty, setLIntegral_univ] at hb
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
    Real.exp_zero, mul_one] at hb
  have hi : Integrable (fun x => Real.sqrt (l (x, τ)) * Real.exp (-l (x, τ)))
      (calibratedMetricVolume g) := by
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnonneg)]
    exact hb.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hnonneg),
    ENNReal.toReal_ofReal (integral_nonneg hnonneg), ENNReal.toReal_ofReal hC] at h
  exact h

end PoincareConjecture.AncientCompactTimeConvergence
