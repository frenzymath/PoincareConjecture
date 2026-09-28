import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.DistanceHarnack
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.ZeroRatioDecay

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

theorem curvatureTensorNorm_le_later_scalar_of_bounded_ancient_distance_le
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {a b D : ℝ} (hab : a < b) (hb : b ≤ 0) (x y : M)
    (hD : ((F.metric a).edist x y).toReal ≤ D) :
    (F.connection a).curvatureTensorNorm x ≤ (n : ℝ) ^ 2 *
      ((F.connection b).scalarCurvature y * Real.exp (D ^ 2 / (2 * (b - a)))) := by
  by_cases hnonflat : ∃ p : M, 0 < (F.connection 0).scalarCurvature p
  · exact F.curvatureTensorNorm_le_exp_of_bounded_ancient_distance_le
      hC hcomplete hoperator hK hbound hnonflat hab hb x y hD
  have hterminal : ∀ z ∈ (univ : Set M), (F.connection 0).scalarCurvature z ≤ 0 := by
    intro z _
    exact le_of_not_gt (fun hz => hnonflat ⟨z, hz⟩)
  have hflat := F.curvatureTensorNorm_le_of_bounded_ancient_terminal_scalar
    hC hcomplete hoperator hK hbound (le_refl 0) hterminal
    a (hab.le.trans hb) x (mem_univ x)
  have hscalar : 0 ≤ (F.connection b).scalarCurvature y :=
    ((F.connection b).curvatureOperatorBound_scalarCurvature
      (hC.tensor_calculus n M (F.metric b) (F.connection b)) y (hoperator b hb y)).1
  exact (by simpa using hflat : (F.connection a).curvatureTensorNorm x ≤ 0).trans
    (by positivity)

theorem eventually_curvatureTensorNorm_lt_on_of_later_scalar_tendsto_zero
    {n : ℕ} {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, T3Space (M i)]
    [∀ i, SecondCountableTopology (M i)] [∀ i, ConnectedSpace (M i)]
    [∀ i, NoncompactSpace (M i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M i)]
    [∀ i, IsManifold (𝓡 n) ∞ (M i)]
    (hC : RicciFlowCurvatureTheory.{u}) (F : ∀ i, RicciFlow n (M i) (Iic 0))
    (hcomplete : ∀ i t, t ≤ 0 → MetricComplete ((F i).metric t))
    (hoperator : ∀ i t, t ≤ 0 → ∀ x, ((F i).connection t).NonnegativeCurvatureOperator x)
    (hbounded : ∀ i, ∃ K : ℝ, 0 ≤ K ∧
      ∀ t ≤ 0, ∀ x, ((F i).connection t).curvatureTensorNorm x ≤ K)
    {a b D : ℝ} (hab : a < b) (hb : b ≤ 0)
    (y : ∀ i, M i) (B : ∀ i, Set (M i))
    (hscalar : Tendsto (fun i => ((F i).connection b).scalarCurvature (y i)) atTop (𝓝 0))
    (hdistance : ∀ᶠ i in atTop, ∀ x ∈ B i, (((F i).metric a).edist x (y i)).toReal ≤ D) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      ∀ x ∈ B i, ((F i).connection a).curvatureTensorNorm x < ε := by
  have hlimit : Tendsto (fun i => (n : ℝ) ^ 2 *
      (((F i).connection b).scalarCurvature (y i) * Real.exp (D ^ 2 / (2 * (b - a)))))
      atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero] using
      (hscalar.mul_const (Real.exp (D ^ 2 / (2 * (b - a))))).const_mul ((n : ℝ) ^ 2)
  intro ε hε
  filter_upwards [hdistance, hlimit.eventually_lt_const hε] with i hi hsmall
  intro x hx
  obtain ⟨K, hK, hbound⟩ := hbounded i
  exact ((F i).curvatureTensorNorm_le_later_scalar_of_bounded_ancient_distance_le
    hC (hcomplete i) (hoperator i) hK hbound hab hb x (y i) (hi x hx)).trans_lt hsmall

theorem ancientRescaleAt_scalarCurvature_tendsto_zero_of_zero_ratio
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (hQzero : Tendsto Q atTop (𝓝 0))
    (q : ℕ → M)
    (hcenter : Tendsto (fun i => Real.sqrt (Q i) *
      ((F.metric t₀).edist p (q i)).toReal) atTop (𝓝 1)) :
    Tendsto (fun i => ((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).connection 0).scalarCurvature
      (q i)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨L, hdecay⟩ := hzero (ε / 8) (by positivity)
  have hsmall : Tendsto (fun i => Real.sqrt (Q i) * L) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, zero_mul] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hQzero).mul_const L
  filter_upwards [hsmall.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    hcenter.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1)] with i hscale hradial
  have hnonneg : 0 ≤ ((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).connection 0).scalarCurvature
      (q i) := by
    rw [ancientRescaleAt_scalarCurvature, zero_div, add_zero]
    exact mul_nonneg (inv_nonneg.mpr (hQ i).le)
      (((F.connection t₀).curvatureOperatorBound_scalarCurvature
        (hC.tensor_calculus n M (F.metric t₀) (F.connection t₀))
        (q i) (hoperator t₀ ht₀ (q i))).1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  have hcurv := F.ancientRescaleAt_scalarCurvature_le_of_quadratic_decay
    hC hcomplete hoperator hK hbound (Q i) (hQ i) t₀ ht₀ p
    (by norm_num : (0 : ℝ) < 1 / 2) hdecay hscale.le 0 (le_refl 0) (q i)
    (by simpa only [ancientRescaleAt_edist_toReal_zero] using hradial.le)
  apply hcurv.trans_lt
  norm_num
  linarith

theorem eventually_ancientRescaleAt_filled_domain_curvature_lt_of_zero_ratio
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (hQzero : Tendsto Q atTop (𝓝 0))
    (q : ℕ → M)
    (hcenter : Tendsto (fun i => Real.sqrt (Q i) *
      ((F.metric t₀).edist p (q i)).toReal) atTop (𝓝 1))
    (B : ℕ → Set M) {D : ℝ}
    (hdistance : ∀ᶠ i in atTop, ∀ x ∈ B i,
      (((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric (-1)).edist x (q i)).toReal ≤ D) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ B i,
      ((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).connection (-1)).curvatureTensorNorm x < ε := by
  let G (i : ℕ) := F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀
  have htime (i : ℕ) (t : ℝ) (ht : t ≤ 0) : t₀ + t / Q i ≤ 0 :=
    (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg ht (hQ i).le)).trans ht₀
  have hcompleteG : ∀ i t, t ≤ 0 → MetricComplete ((G i).metric t) := by
    intro i t ht
    apply F.parabolicRescale_metricComplete
    exact hcomplete _ (htime i t ht)
  have hoperatorG : ∀ i t, t ≤ 0 → ∀ x,
      ((G i).connection t).NonnegativeCurvatureOperator x := by
    intro i t ht x
    apply F.parabolicRescale_nonnegativeCurvatureOperator
    exact hoperator _ (htime i t ht) x
  have hboundedG : ∀ i, ∃ K' : ℝ, 0 ≤ K' ∧
      ∀ t ≤ 0, ∀ x, ((G i).connection t).curvatureTensorNorm x ≤ K' := by
    intro i
    have hQi := hQ i
    refine ⟨(n : ℝ) ^ 2 * ((Q i)⁻¹ * ((n : ℝ) ^ 2 * K)), by positivity, ?_⟩
    intro t ht x
    calc
      ((G i).connection t).curvatureTensorNorm x ≤
          (n : ℝ) ^ 2 * ((G i).connection t).scalarCurvature x :=
        ((G i).connection t).curvatureTensorNorm_le_scalarCurvature
          (hC.tensor_calculus n M ((G i).metric t) ((G i).connection t))
          x (hoperatorG i t ht x)
      _ = (n : ℝ) ^ 2 * ((Q i)⁻¹ *
          (F.connection (t₀ + t / Q i)).scalarCurvature x) := by
        rw [show ((G i).connection t).scalarCurvature x = _ from
          F.ancientRescaleAt_scalarCurvature (Q i) (hQ i) t₀ ht₀ t x]
      _ ≤ (n : ℝ) ^ 2 * ((Q i)⁻¹ * ((n : ℝ) ^ 2 * K)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hQ i).le)
        exact (le_abs_self _).trans
          (((F.connection (t₀ + t / Q i)).abs_scalarCurvature_le_curvatureTensorNorm x).trans
            (mul_le_mul_of_nonneg_left (hbound _ (htime i t ht) x) (sq_nonneg _)))
  exact eventually_curvatureTensorNorm_lt_on_of_later_scalar_tendsto_zero
    hC G hcompleteG hoperatorG hboundedG (by norm_num : (-1 : ℝ) < 0) (le_refl 0)
    q B (F.ancientRescaleAt_scalarCurvature_tendsto_zero_of_zero_ratio
      hC hcomplete hoperator hK hbound t₀ ht₀ p hzero Q hQ hQzero q hcenter) hdistance

end PoincareConjecture.RicciFlow
