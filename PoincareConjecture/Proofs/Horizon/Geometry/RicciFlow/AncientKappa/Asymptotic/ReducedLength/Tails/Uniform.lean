import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Tails.Gaussian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.AncientRescalingSequence

open Poincare.Analysis RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem exp_neg_reducedLength_integrable
    (S : AncientRescalingSequence K) (P : AncientAsymptoticSolitonPredecessors K)
    (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun q => Real.exp (-reducedLength K.flow 0 S.reference q (S.scale k * τ)))
      (calibratedMetricVolume ((S.rescaling k).flow.metric (-τ))) := by
  have hc := (P.continuous_reducedLength S.reference (S.scale k * τ)
    (mul_pos (S.scale_pos k) hτ)).neg.rexp
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun q => Real.exp_nonneg _))]
  have h := S.exp_neg_reducedLength_gaussian_tail P k hτ (le_refl (0 : ℝ))
  have hempty : ((S.rescaling k).flow.metric (-τ)).ball (S.base k) 0 = ∅ := by
    ext q
    simp [RiemannianMetric.ball]
  rw [hempty, compl_empty, setLIntegral_univ] at h
  exact h.trans_lt ENNReal.ofReal_lt_top

theorem normalized_reducedLength_integrable
    (S : AncientRescalingSequence K) (P : AncientAsymptoticSolitonPredecessors K)
    (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun q => τ ^ (-(n : ℝ) / 2) *
      Real.exp (-reducedLength K.flow 0 S.reference q (S.scale k * τ)))
      (calibratedMetricVolume ((S.rescaling k).flow.metric (-τ))) :=
  (S.exp_neg_reducedLength_integrable P k hτ).const_mul _

theorem normalized_reducedLength_tails_small
    (S : AncientRescalingSequence K) (P : AncientAsymptoticSolitonPredecessors K)
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ k : ℕ,
      ∫⁻ q in (((S.rescaling k).flow.metric (-τ)).ball (S.base k) R)ᶜ,
        ENNReal.ofReal (τ ^ (-(n : ℝ) / 2) *
          Real.exp (-reducedLength K.flow 0 S.reference q (S.scale k * τ)))
            ∂calibratedMetricVolume ((S.rescaling k).flow.metric (-τ)) ≤ ENNReal.ofReal ε := by
  let a := (16 * (2 * (n : ℝ) + 604) ^ 2 * τ)⁻¹ / 2
  let c := τ ^ (-(n : ℝ) / 2)
  let A := Real.exp ((n : ℝ) / 2 * max (τ ^ 2) (τ ^ 2)⁻¹ + 1)
  let C := euclideanUnitBallVolume n * gaussianShellSum n a
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 ≤ c := Real.rpow_nonneg hτ.le _
  have hlim : Tendsto (fun R : ℝ => c * (A * (Real.exp (-a * R ^ 2) * C)))
      atTop (𝓝 0) := by
    have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop ha)
    simpa only [Function.comp_def, neg_mul, zero_mul, mul_zero] using
      ((hexp.mul_const C).const_mul A).const_mul c
  obtain ⟨R, hR, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hlim.eventually (gt_mem_nhds hε))).exists
  refine ⟨R, hR, ?_⟩
  intro k
  simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg hτ.le (-(n : ℝ) / 2))]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply le_trans _ (ENNReal.ofReal_le_ofReal hsmall.le)
  rw [ENNReal.ofReal_mul hc]
  gcongr
  convert! S.exp_neg_reducedLength_gaussian_tail P k hτ hR.le using 1
  dsimp [a, A, C]
  congr 4
  ring

end PoincareConjecture.AncientRescalingSequence
