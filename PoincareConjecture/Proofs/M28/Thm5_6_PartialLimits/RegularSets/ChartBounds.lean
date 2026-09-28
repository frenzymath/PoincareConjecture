import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.MetricConvergence
import PoincareConjecture.Proofs.M28.Mathlib.WithinConvergenceBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.RegularPointedMetricConvergence

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}

theorem tendstoUniformlyOn_chart_coefficients
    (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : G.limitCarrier.carrier) (K : Set (EuclideanSpace ℝ (Fin n))),
      IsCompact K → K ⊆ (extChartAt (𝓡 n) q).target →
      TendstoUniformlyOn
        (fun k => (g (G.subsequence k)).pullbackCoefficients
          (G.embedding k ∘ (extChartAt (𝓡 n) q).symm))
        (G.limitMetric.pullbackCoefficients (extChartAt (𝓡 n) q).symm) atTop K := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q K hK htarget
  exact (ContinuousMultilinearMap.uniformContinuous_eval_const
    (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
      (G.metric_jets q 0 K hK htarget)

theorem exists_eventual_chart_jet_bound
    (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : G.limitCarrier.carrier) (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))),
      IsCompact K → K ⊆ (extChartAt (𝓡 n) q).target →
      ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m ((g (G.subsequence k)).pullbackCoefficients
          (G.embedding k ∘ (extChartAt (𝓡 n) q).symm)) x‖ ≤ B := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q m K hK htarget
  apply (G.metric_jets q m K hK htarget).exists_eventual_norm_bound hK
  intro x hx
  exact ((G.limitMetric.contDiffOn_chartCoefficients q).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds (htarget hx))).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top) |>.continuousWithinAt

theorem exists_eventual_chart_ellipticity
    (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : G.limitCarrier.carrier) (K : Set (EuclideanSpace ℝ (Fin n))),
      IsCompact K → K ⊆ (extChartAt (𝓡 n) q).target →
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᶠ k in atTop, ∀ x ∈ K,
        ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ (g (G.subsequence k)).pullbackCoefficients
            (G.embedding k ∘ (extChartAt (𝓡 n) q).symm) x v v ∧
          (g (G.subsequence k)).pullbackCoefficients
            (G.embedding k ∘ (extChartAt (𝓡 n) q).symm) x v v ≤ b * ‖v‖ ^ 2 := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q K hK htarget
  let B₀ := G.limitMetric.pullbackCoefficients (extChartAt (𝓡 n) q).symm
  let B := fun k => (g (G.subsequence k)).pullbackCoefficients
    (G.embedding k ∘ (extChartAt (𝓡 n) q).symm)
  have hcontinuous : ContinuousOn B₀ K :=
    (G.limitMetric.contDiffOn_chartCoefficients q).continuousOn.mono htarget
  have hpos : ∀ x ∈ K, ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → 0 < B₀ x v v := by
    intro x hx v hv
    have hAv : mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm x v ≠ 0 := by
      intro hzero
      obtain ⟨e, he⟩ := G.limitMetric.isInvertible_chartCoefficients q (htarget hx)
      apply hv
      apply e.injective
      change (e : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) v = e 0
      rw [map_zero, he]
      ext w
      change G.limitMetric.inner ((extChartAt (𝓡 n) q).symm x)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm x v)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm x w) = 0
      rw [hzero]
      simp +instances only [map_zero, zero_apply]
    exact G.limitMetric.pos _ _ hAv
  obtain ⟨c, hc, hlow⟩ := exists_uniform_bilinear_lower_bound hK hcontinuous hpos
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (f := B₀) hcontinuous
  let b := max M₀ 0 + 1
  have hb : 0 < b := by dsimp only [b]; positivity
  refine ⟨c / 2, b, half_pos hc, hb, ?_⟩
  have hnear := Metric.tendstoUniformlyOn_iff.mp
    (G.tendstoUniformlyOn_chart_coefficients q K hK htarget)
    (min (c / 2) 1) (lt_min (half_pos hc) zero_lt_one)
  filter_upwards [hnear] with k hk
  intro x hx v
  have herror : ‖B k x - B₀ x‖ ≤ min (c / 2) 1 := by
    exact le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hk x hx)
  have hnorm : ‖B k x‖ ≤ b := by
    have htriangle := norm_add_le (B k x - B₀ x) (B₀ x)
    rw [sub_add_cancel] at htriangle
    have herr := herror.trans (min_le_right _ _)
    dsimp only [b]
    linarith [hM₀ x hx, le_max_left M₀ 0]
  have hdiff : B₀ x v v - B k x v v ≤ c / 2 * ‖v‖ ^ 2 := by
    have hnormdiff := (B k x - B₀ x).le_opNorm₂ v v
    have herr := mul_le_mul_of_nonneg_right
      (herror.trans (min_le_left _ _)) (sq_nonneg ‖v‖)
    have hval : B₀ x v v - B k x v v ≤ ‖(B k x - B₀ x) v v‖ := by
      simpa only [sub_apply, Real.norm_eq_abs, abs_sub_comm] using
        le_abs_self (B₀ x v v - B k x v v)
    exact hval.trans (hnormdiff.trans (by nlinarith only [herr]))
  constructor
  · change c / 2 * ‖v‖ ^ 2 ≤ B k x v v
    linarith only [hdiff, hlow x hx v]
  · change B k x v v ≤ b * ‖v‖ ^ 2
    have hval : B k x v v ≤ ‖B k x v v‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (B k x v v)
    calc
      B k x v v ≤ ‖B k x v v‖ := hval
      _ ≤ ‖B k x‖ * ‖v‖ * ‖v‖ := (B k x).le_opNorm₂ v v
      _ = ‖B k x‖ * ‖v‖ ^ 2 := by ring
      _ ≤ b * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hnorm (sq_nonneg ‖v‖)

end PoincareConjecture.M28.RegularPointedMetricConvergence
