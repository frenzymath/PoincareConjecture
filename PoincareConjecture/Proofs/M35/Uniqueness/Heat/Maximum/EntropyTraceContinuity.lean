import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.GradientTimeContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2V" => Lp V 2 (volume : Measure V)

theorem metricEntropyPotential_slab_bound {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {η : V → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∀ x z,
      ‖metricEntropyPotential (F.metric t) η Q (x, z)‖ ≤ C * ‖z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_raw_entropy_slab_coefficient_bound F hI hIJ hη hc
  refine ⟨C ^ 2, sq_nonneg _, fun t ht x z => ?_⟩
  by_cases hx : x ∈ tsupport η
  · exact metricEntropyPotential_pointwise_bound (F.metric t) η hQ hC.le x z
      (hb t ht x hx).1 (hb t ht x hx).2.2.1
  · simp only [metricEntropyPotential, image_eq_zero_of_notMem_tsupport hx,
      zero_mul, norm_zero]
    positivity

theorem metricEntropyPotential_field_time_continuousOn {J I : Set ℝ}
    (F : RicciFlow n V J) (hI : IsCompact I) (hIJ : I ⊆ J)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    {Q : ℝ} (hQ : 0 ≤ Q) (u : L2V) :
    ContinuousOn (fun t => fieldIntegral (metricEntropyPotential (F.metric t) η Q) u) I := by
  obtain ⟨C, _, hb⟩ := metricEntropyPotential_slab_bound F hI hIJ hη.continuous hc hQ
  intro t ht
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => C * ‖u x‖ ^ 2)
  · exact Eventually.of_forall fun s =>
      (metricEntropyPotential_integrable (F.metric s) hη hc hQ u).1
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact Eventually.of_forall fun x => hb s hs x (u x)
  · exact ((Lp.memLp u).norm.integrable_sq).const_mul C
  · exact Eventually.of_forall fun x =>
      ((metricEntropyPotential_hasDerivWithinAt F η Q (hIJ ht) x (u x)).continuousWithinAt.mono
        hIJ).tendsto

theorem metricEntropy_field_slab_difference {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {η : V → ℝ} (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∀ u v : L2V,
      ‖fieldIntegral (metricEntropyPotential (F.metric t) η Q) v -
        fieldIntegral (metricEntropyPotential (F.metric t) η Q) u‖ ≤
        C * (‖v‖ + ‖u‖) * ‖v - u‖ := by
  obtain ⟨C, hC, hb⟩ := metricEntropyGradient_slab_bound F hI hIJ hη.continuous hc Q
  refine ⟨C, hC, fun t ht u v => ?_⟩
  apply fieldIntegral_difference_le _ (metricEntropyPotential_integrable (F.metric t) hη hc hQ) hC
  intro x z w
  apply quadratic_lipschitz_of_derivative_growth _ _
    (fun y => (metricEntropyPotential_value_hasFDerivAt
      (F.metric t) η Q x y).differentiableAt.hasFDerivAt) hC
  intro y
  rw [← metricEntropyGradient_norm]
  exact hb t ht x y

theorem metricEntropy_trace_continuousOn {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {η : V → ℝ} (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) {Q : ℝ} (hQ : 0 ≤ Q)
    (U : ℝ → L2V) (hU : ContinuousOn U I) :
    ContinuousOn (fun t => fieldIntegral (metricEntropyPotential (F.metric t) η Q) (U t)) I := by
  obtain ⟨C, _, hb⟩ := metricEntropy_field_slab_difference F hI hIJ hη hc hQ
  intro t ht
  have hUt := (hU t ht).tendsto
  have hbound : Tendsto (fun s => C * (‖U s‖ + ‖U t‖) * ‖U s - U t‖) (𝓝[I] t) (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      (tendsto_const_nhds.mul (hUt.norm.add_const ‖U t‖)).mul (hUt.sub_const (U t)).norm
  have hdiff : Tendsto (fun s =>
      fieldIntegral (metricEntropyPotential (F.metric s) η Q) (U s) -
        fieldIntegral (metricEntropyPotential (F.metric s) η Q) (U t)) (𝓝[I] t) (𝓝 0) := by
    apply squeeze_zero_norm' _ hbound
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hb s hs (U t) (U s)
  have hfixed :=
    (metricEntropyPotential_field_time_continuousOn F hI hIJ hη hc hQ (U t) t ht).tendsto
  change Tendsto _ _ _
  simpa only [sub_add_cancel, zero_add] using hdiff.add hfixed

end PoincareConjecture.M35.Uniqueness.Heat
