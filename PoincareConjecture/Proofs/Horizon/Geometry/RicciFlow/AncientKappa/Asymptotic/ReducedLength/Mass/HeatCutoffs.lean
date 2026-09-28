import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Mass.Cutoff
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Mass.Laplacian
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.CutoffPairing


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

theorem exists_limitDensity_vanishing_heat_cutoffs
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hl : ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)))
    (hl0 : ∀ z ∈ univ ×ˢ Ioi (0 : ℝ), 0 ≤ l z)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ χ : ℕ → G.limit.carrier.carrier → ℝ,
      (∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (χ j) ∧ HasCompactSupport (χ j) ∧
        ∀ x, χ j x ∈ Icc 0 1) ∧
      (∀ A : Set G.limit.carrier.carrier, IsCompact A →
        ∀ᶠ j in atTop, ∀ x ∈ A, χ j x = 1) ∧
      ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo α β →
        Tendsto (fun j => RicciFlow.ConjugateHeat.weakPairing G.limit.flow
          (fun z => z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z))
          (fun z => χ j z.1 * η z.2)) atTop (𝓝 0) := by
  obtain ⟨V, C, hV, _, hC, χ, hχ, hex, hexK, hmass, _, _, hflux⟩ :=
    G.exists_limitDensity_mass_cutoffs P hl hl0 hlim hα hαβ
  refine ⟨χ, hχ, hexK, ?_⟩
  intro η hη hηc hηs
  have hu : ContinuousOn (fun z : G.limit.carrier.carrier × ℝ =>
      z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)) (univ ×ˢ Icc α β) :=
    (continuousOn_snd.rpow_const (fun z hz => Or.inl (hα.trans_le hz.2.1).ne')).mul
      ((hl.mono (prod_mono Subset.rfl (fun τ hτ => hα.trans_le hτ.1))).neg.rexp)
  have hBlim : Tendsto (fun j : ℕ => C / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  apply RicciFlow.ConjugateHeat.tendsto_weakPairing_productTests
    G.limit.flow hαβ hV (fun τ hτ => by
      simpa only [interior_Iio, mem_Iio] using neg_neg_of_pos (hα.trans_le hτ.1))
    hu (fun τ hτ x => mul_nonneg (Real.rpow_nonneg (hα.trans_le hτ.1).le _)
      (Real.exp_nonneg _))
    (by simpa only [calibratedMetricVolume_eq_volumeMeasure] using hmass)
    χ (fun j => (hχ j).1) (fun j => (hχ j).2.1)
    (fun j => (hχ j).2.2) (fun x => tendsto_const_nhds.congr' (by
      filter_upwards [hex x] with j hj
      exact hj.symm))
    (B := fun j => C / ((j : ℝ) + 1)) (fun j => div_nonneg hC (by positivity))
    hBlim ?_ hη hηc hηs
  intro j τ hτ
  exact G.abs_limitDensity_integral_laplacian_le P strictMono_id l hl hlim
    (hα.trans_le hτ.1) (hχ j).1 (hχ j).2.1
    (div_nonneg hC (by positivity))
    (by simpa only [calibratedMetricVolume_eq_volumeMeasure] using hflux j τ hτ)

end PoincareConjecture.AncientCompactTimeConvergence
