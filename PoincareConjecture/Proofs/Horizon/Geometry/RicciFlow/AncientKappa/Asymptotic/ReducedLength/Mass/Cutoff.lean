import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Mass.Integrable
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Tails.Limit.Cutoff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

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

theorem exists_limitDensity_mass_cutoffs
    (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hl : ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)))
    (hl0 : ∀ z ∈ univ ×ˢ Ioi (0 : ℝ), 0 ≤ l z)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ V C : ℝ, 0 ≤ V ∧ V < euclideanReducedVolume n ∧ 0 ≤ C ∧
      ∃ χ : ℕ → G.limit.carrier.carrier → ℝ,
        (∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (χ j) ∧ HasCompactSupport (χ j) ∧
          ∀ x, χ j x ∈ Icc 0 1) ∧
        (∀ x, ∀ᶠ j in atTop, χ j x = 1) ∧
        (∀ A : Set G.limit.carrier.carrier, IsCompact A →
          ∀ᶠ j in atTop, ∀ x ∈ A, χ j x = 1) ∧
        (∀ τ ∈ Icc α β,
          Integrable (fun x => τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)))
            (calibratedMetricVolume (G.limit.flow.metric (-τ))) ∧
          (∫ x, τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ))
            ∂calibratedMetricVolume (G.limit.flow.metric (-τ))) = V) ∧
        (∀ τ ∈ Icc α β, ∀ j,
          Integrable (fun x => τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) * χ j x)
            (calibratedMetricVolume (G.limit.flow.metric (-τ))) ∧
          (∫ x, τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) * χ j x
            ∂calibratedMetricVolume (G.limit.flow.metric (-τ))) ∈ Icc 0 V) ∧
        (∀ τ ∈ Icc α β,
          Tendsto (fun j => ∫ x, τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) * χ j x
            ∂calibratedMetricVolume (G.limit.flow.metric (-τ))) atTop (𝓝 V)) ∧
        ∀ j τ, τ ∈ Icc α β →
          (∫⁻ x, ENNReal.ofReal
            (τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) *
              |(G.limit.flow.metric (-τ)).inner x
                ((G.limit.flow.connection (-τ)).gradient (fun y => l (y, τ)) x)
                ((G.limit.flow.connection (-τ)).gradient (χ j) x)|)
            ∂calibratedMetricVolume (G.limit.flow.metric (-τ))) ≤
              ENNReal.ofReal (C / ((j : ℝ) + 1)) := by
  classical
  let : PreconnectedSpace G.limit.carrier.carrier :=
    ⟨G.limit.carrier.connected.isPreconnected⟩
  obtain ⟨V, hV, hVE, hmass⟩ := G.exists_integrable_constant_limitDensity_mass P hl hlim
  obtain ⟨C, hC, hcut⟩ :=
    G.exists_limitReducedLength_cutoff_flux_bound_on_interval P hl hl0 hlim hα hαβ
  have hj (j : ℕ) : 1 ≤ (j : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  choose χ hχs hχc hχr hχone hχsupp hχflux using fun j : ℕ => hcut ((j : ℝ) + 1) (hj j)
  have hex (x : G.limit.carrier.carrier) : ∀ᶠ j in atTop, χ j x = 1 := by
    obtain ⟨N, hN⟩ := exists_nat_ge
      (((G.limit.flow.metric (-α)).edist G.limit.base x).toReal)
    filter_upwards [eventually_ge_atTop N] with j hjN
    exact hχone j x (hN.trans ((Nat.cast_le.mpr hjN).trans (by linarith)))
  have hexK (A : Set G.limit.carrier.carrier) (hA : IsCompact A) :
      ∀ᶠ j in atTop, ∀ x ∈ A, χ j x = 1 := by
    obtain ⟨B, hB⟩ := hA.bddAbove_image
      ((G.limit.flow.metric (-α)).continuous_toReal_edist G.limit.base).continuousOn
    obtain ⟨N, hN⟩ := exists_nat_ge B
    filter_upwards [eventually_ge_atTop N] with j hjN
    intro x hx
    exact hχone j x ((hB (mem_image_of_mem _ hx)).trans
      (hN.trans ((Nat.cast_le.mpr hjN).trans (by linarith))))
  have hc (τ : ℝ) (hτ : τ ∈ Icc α β) :
      Continuous (fun x => τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ))) :=
    continuous_const.mul (hl.comp_continuous
      (continuous_id.prodMk continuous_const)
      (fun x => ⟨mem_univ x, hα.trans_le hτ.1⟩)).neg.rexp
  have hn (τ : ℝ) (hτ : τ ∈ Icc α β) (x : G.limit.carrier.carrier) :
      0 ≤ τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) :=
    mul_nonneg (Real.rpow_nonneg (hα.trans_le hτ.1).le _) (Real.exp_nonneg _)
  have hb (τ : ℝ) (hτ : τ ∈ Icc α β) (j : ℕ) (x : G.limit.carrier.carrier) :
      ‖τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) * χ j x‖ ≤
        τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) := by
    rw [Real.norm_of_nonneg (mul_nonneg (hn τ hτ x) (hχr j x).1)]
    exact mul_le_of_le_one_right (hn τ hτ x) (hχr j x).2
  have hi (τ : ℝ) (hτ : τ ∈ Icc α β) (j : ℕ) :
      Integrable (fun x => τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)) * χ j x)
        (calibratedMetricVolume (G.limit.flow.metric (-τ))) :=
    ((hmass τ (hα.trans_le hτ.1)).1).mono'
      ((hc τ hτ).mul (hχs j).continuous).aestronglyMeasurable
      (ae_of_all _ (hb τ hτ j))
  refine ⟨V, C, hV, hVE, hC, χ, (fun j => ⟨hχs j, hχc j, hχr j⟩),
    hex, hexK, (fun τ hτ => hmass τ (hα.trans_le hτ.1)), ?_, ?_, hχflux⟩
  · intro τ hτ j
    refine ⟨hi τ hτ j, integral_nonneg (fun x =>
      mul_nonneg (hn τ hτ x) (hχr j x).1), ?_⟩
    rw [← (hmass τ (hα.trans_le hτ.1)).2]
    exact integral_mono (hi τ hτ j) (hmass τ (hα.trans_le hτ.1)).1
      (fun x => mul_le_of_le_one_right (hn τ hτ x) (hχr j x).2)
  · intro τ hτ
    rw [← (hmass τ (hα.trans_le hτ.1)).2]
    apply tendsto_integral_of_dominated_convergence
      (fun x => τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)))
    · exact fun j => (hi τ hτ j).aestronglyMeasurable
    · exact (hmass τ (hα.trans_le hτ.1)).1
    · exact fun j => ae_of_all _ (hb τ hτ j)
    · exact ae_of_all _ (fun x =>
        tendsto_const_nhds.congr' ((hex x).mono (fun j hj => by simp only [hj, mul_one])))

end PoincareConjecture.AncientCompactTimeConvergence
