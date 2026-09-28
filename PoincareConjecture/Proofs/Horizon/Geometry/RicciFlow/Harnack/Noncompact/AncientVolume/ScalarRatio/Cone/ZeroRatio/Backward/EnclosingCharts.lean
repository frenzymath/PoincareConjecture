import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Backward.BallControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Backward.NormalCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Backward.EuclideanCoefficients











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.RicciFlow



theorem exists_backward_enclosing_euclidean_charts
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (hn : 1 ≤ n) (t₀ : ℝ) (ht₀ : t₀ ≤ 0)
    (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k) (q : ℕ → M) (Ω : ℕ → Set M)
    (hscalar : Tendsto (fun k =>
      ((F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀).connection 0).scalarCurvature (q k))
      atTop (𝓝 0))
    {D : ℝ} (hdistance : ∀ᶠ k in atTop, ∀ x ∈ Ω k,
      (((F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀).metric (-1)).edist x (q k)).toReal ≤ D) :
    let ρ := RiemannianMetric.localInjectivityRadius n 1 1 κ
    ∃ c : ℝ, ∃ hc : 0 < c, Real.sqrt c * D < ρ / 8 ∧
      let H := fun k => F.ancientRescaleAt (c * Q k) (mul_pos hc (hQ k))
        (t₀ - 1 / Q k) (sub_nonpos.mpr (ht₀.trans (one_div_nonneg.mpr (hQ k).le)))
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ L : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
        (∀ k, (Φ k).source = Metric.ball 0 ρ ∧
          (Φ k).target = ((H (σ k)).metric 0).ball (q (σ k)) ρ ∧
          Φ k 0 = q (σ k) ∧
          Ω (σ k) ⊆ ((H (σ k)).metric 0).ball (q (σ k)) (ρ / 8) ∧
          (∀ v w, ((H (σ k)).metric 0).pullbackCoefficients
            (extChartAt (𝓡 n) (q (σ k))).symm
            (extChartAt (𝓡 n) (q (σ k)) (q (σ k))) (L k v) (L k w) = inner ℝ v w) ∧
          HasFDerivAt (fun w => extChartAt (𝓡 n) (q (σ k)) (Φ k w))
            (L k).toContinuousLinearMap 0 ∧
          (∀ w ∈ Metric.ball 0 ρ, ((H (σ k)).metric 0).IsGeodesicOn
            (fun t => Φ k (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 ρ}) ∧
          (∀ w ∈ Metric.ball 0 ρ,
            ((H (σ k)).metric 0).edist (q (σ k)) (Φ k w) = ENNReal.ofReal ‖w‖) ∧
          ∀ t ≤ 0, ∀ x ∈ ((H (σ k)).metric 0).ball (q (σ k)) (2 * ρ),
            ((H (σ k)).connection t).curvatureTensorNorm x ≤ 1) ∧
        ∀ m C, IsCompact C → C ⊆ Metric.ball 0 (ρ / 4) → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((H (σ k)).metric 0).pullbackCoefficients (Φ k)))
          (iteratedFDeriv ℝ m (fun _ : EuclideanSpace ℝ (Fin n) => innerSL ℝ)) atTop C := by
  classical
  let ρ := RiemannianMetric.localInjectivityRadius n 1 1 κ
  have hρ : 0 < ρ := RiemannianMetric.localInjectivityRadius_pos n 1 (by norm_num) κ
  have hρ1 : ρ < 1 := RiemannianMetric.localInjectivityRadius_lt n 1 (by norm_num) κ
  let a : ℝ := ρ / (16 * (|D| + 1))
  have ha : 0 < a := div_pos hρ (by positivity)
  let c := a ^ 2
  have hc : 0 < c := sq_pos_of_pos ha
  have hsc : Real.sqrt c = a := Real.sqrt_sq ha.le
  have hsD : Real.sqrt c * D < ρ / 8 := by
    rw [hsc]
    have hadd : 0 < |D| + 1 := by positivity
    have haeq : a * (|D| + 1) = ρ / 16 := by dsimp [a]; field_simp
    have hless := mul_lt_mul_of_pos_left ((le_abs_self D).trans_lt (lt_add_one _)) ha
    rw [haeq] at hless
    linarith
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  let G (k : ℕ) := F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀
  have htime (k : ℕ) (s : ℝ) (hs : s ≤ 0) : t₀ + s / Q k ≤ 0 :=
    (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs (hQ k).le)).trans ht₀
  have hcompleteG : ∀ k s, s ≤ 0 → MetricComplete ((G k).metric s) := by
    intro k s hs
    apply F.parabolicRescale_metricComplete
    exact hcomplete _ (htime k s hs)
  have hoperatorG : ∀ k s, s ≤ 0 → ∀ x,
      ((G k).connection s).NonnegativeCurvatureOperator x := by
    intro k s hs x
    apply F.parabolicRescale_nonnegativeCurvatureOperator
    exact hoperator _ (htime k s hs) x
  have hboundedG : ∀ k, ∃ B : ℝ, 0 ≤ B ∧
      ∀ s ≤ 0, ∀ x, ((G k).connection s).curvatureTensorNorm x ≤ B := by
    intro k
    have hQk := hQ k
    refine ⟨(n : ℝ) ^ 2 * ((Q k)⁻¹ * ((n : ℝ) ^ 2 * K)), by positivity, ?_⟩
    intro s hs x
    calc
      ((G k).connection s).curvatureTensorNorm x ≤
          (n : ℝ) ^ 2 * ((G k).connection s).scalarCurvature x :=
        ((G k).connection s).curvatureTensorNorm_le_scalarCurvature
          (hC.tensor_calculus n M ((G k).metric s) ((G k).connection s)) x
          (hoperatorG k s hs x)
      _ = (n : ℝ) ^ 2 * ((Q k)⁻¹ *
          (F.connection (t₀ + s / Q k)).scalarCurvature x) := by
        rw [show ((G k).connection s).scalarCurvature x = _ from
          F.ancientRescaleAt_scalarCurvature (Q k) (hQ k) t₀ ht₀ s x]
      _ ≤ (n : ℝ) ^ 2 * ((Q k)⁻¹ * ((n : ℝ) ^ 2 * K)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hQk.le)
        exact (le_abs_self _).trans
          (((F.connection (t₀ + s / Q k)).abs_scalarCurvature_le_curvatureTensorNorm x).trans
            (mul_le_mul_of_nonneg_left (hbound _ (htime k s hs) x) (sq_nonneg _)))
  have hpastG := eventually_past_ball_curvature_lt_of_later_scalar_tendsto_zero
    hC G hcompleteG hoperatorG hboundedG (by norm_num : (-1 : ℝ) < 0) (le_refl 0)
    q hscalar (2 / Real.sqrt c) (by positivity)
  have htcenter (k : ℕ) : t₀ - 1 / Q k ≤ 0 :=
    sub_nonpos.mpr (ht₀.trans (one_div_nonneg.mpr (hQ k).le))
  let H (k : ℕ) := F.ancientRescaleAt (c * Q k) (mul_pos hc (hQ k))
    (t₀ - 1 / Q k) (htcenter k)
  have htimeH (k : ℕ) (s : ℝ) (hs : s ≤ 0) : t₀ - 1 / Q k + s / (c * Q k) ≤ 0 :=
    (add_le_of_nonpos_right
      (div_nonpos_of_nonpos_of_nonneg hs (mul_pos hc (hQ k)).le)).trans (htcenter k)
  have hcompleteH : ∀ k s, s ≤ 0 → MetricComplete ((H k).metric s) := by
    intro k s hs
    apply F.parabolicRescale_metricComplete
    exact hcomplete _ (htimeH k s hs)
  have hoperatorH : ∀ k s, s ≤ 0 → ∀ x,
      ((H k).connection s).NonnegativeCurvatureOperator x := by
    intro k s hs x
    apply F.parabolicRescale_nonnegativeCurvatureOperator
    exact hoperator _ (htimeH k s hs) x
  have hscalarHG (k : ℕ) (s : ℝ) (x : M) :
      ((H k).connection s).scalarCurvature x =
        c⁻¹ * ((G k).connection (-1 + s / c)).scalarCurvature x := by
    have heq : t₀ - 1 / Q k + s / (c * Q k) = t₀ + (-1 + s / c) / Q k := by
      field_simp [hc.ne', (hQ k).ne'] <;> ring
    rw [show ((H k).connection s).scalarCurvature x = _ from
      F.ancientRescaleAt_scalarCurvature (c * Q k) (mul_pos hc (hQ k))
        (t₀ - 1 / Q k) (htcenter k) s x]
    rw [show ((G k).connection (-1 + s / c)).scalarCurvature x = _ from
      F.ancientRescaleAt_scalarCurvature (Q k) (hQ k) t₀ ht₀ (-1 + s / c) x]
    rw [heq]
    ring
  have hballHG (k : ℕ) (r : ℝ) :
      ((H k).metric 0).ball (q k) r =
        ((G k).metric (-1)).ball (q k) (r / Real.sqrt c) := by
    have htzero : t₀ - 1 / Q k = t₀ + (-1) / Q k := by ring
    simp only [H, G, ancientRescaleAt_metric, zero_div, add_zero,
      rescaledMetric_ball_allDimensions, Real.sqrt_mul hc.le, htzero, div_div]
  have hdistHG (k : ℕ) (x y : M) :
      (((H k).metric 0).edist x y).toReal =
        Real.sqrt c * (((G k).metric (-1)).edist x y).toReal := by
    have htzero : t₀ - 1 / Q k = t₀ + (-1) / Q k := by ring
    simp only [H, G, ancientRescaleAt_metric, zero_div, add_zero, htzero,
      rescaledMetric_edist, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sqrt_mul hc.le]
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    ring
  have hpastH : ∀ ε > 0, ∀ᶠ k in atTop,
      ∀ s ≤ 0, ∀ x ∈ ((H k).metric 0).ball (q k) 2,
        ((H k).connection s).curvatureTensorNorm x < ε := by
    intro ε hε
    let C : ℝ := (n : ℝ) ^ 2 * (n : ℝ) ^ 2
    have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
    let δ : ℝ := ε * c / (C + 1)
    have hδ : 0 < δ := div_pos (mul_pos hε hc) (by positivity)
    have hfactor : (n : ℝ) ^ 2 * (c⁻¹ * ((n : ℝ) ^ 2 * δ)) < ε := by
      calc
        _ = C * ε / (C + 1) := by dsimp [δ, C]; field_simp
        _ < ε := (div_lt_iff₀ (by positivity : 0 < C + 1)).mpr (by nlinarith)
    filter_upwards [hpastG δ hδ] with k hk
    intro s hs x hx
    have hst : -1 + s / c ≤ -1 := by
      have := div_nonpos_of_nonpos_of_nonneg hs hc.le
      linarith
    have hfull := hk (-1 + s / c) hst x ((hballHG k 2) ▸ hx)
    calc
      ((H k).connection s).curvatureTensorNorm x ≤
          (n : ℝ) ^ 2 * ((H k).connection s).scalarCurvature x :=
        ((H k).connection s).curvatureTensorNorm_le_scalarCurvature
          (hC.tensor_calculus n M ((H k).metric s) ((H k).connection s)) x
          (hoperatorH k s hs x)
      _ = (n : ℝ) ^ 2 * (c⁻¹ * ((G k).connection (-1 + s / c)).scalarCurvature x) := by
        rw [hscalarHG]
      _ ≤ (n : ℝ) ^ 2 * (c⁻¹ * ((n : ℝ) ^ 2 * δ)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
        exact (le_abs_self _).trans
          ((((G k).connection (-1 + s / c)).abs_scalarCurvature_le_curvatureTensorNorm x).trans
            (mul_le_mul_of_nonneg_left hfull.le (sq_nonneg _)))
      _ < ε := hfactor
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnreal
  have hnA : (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 2) = 1 := by field_simp
  have hcharts : ∀ᶠ k in atTop,
      ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
        Φ.source = Metric.ball 0 ρ ∧ Φ.target = ((H k).metric 0).ball (q k) ρ ∧
        Φ 0 = q k ∧ Ω k ⊆ ((H k).metric 0).ball (q k) (ρ / 8) ∧
        (∀ v w, ((H k).metric 0).pullbackCoefficients (extChartAt (𝓡 n) (q k)).symm
          (extChartAt (𝓡 n) (q k) (q k)) (L v) (L w) = inner ℝ v w) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) (q k) (Φ w)) L.toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 ρ, ((H k).metric 0).IsGeodesicOn (fun t => Φ (t • w))
          {t : ℝ | t • w ∈ Metric.ball 0 ρ}) ∧
        (∀ w ∈ Metric.ball 0 ρ,
          ((H k).metric 0).edist (q k) (Φ w) = ENNReal.ofReal ‖w‖) ∧
        ∀ s ≤ 0, ∀ x ∈ ((H k).metric 0).ball (q k) (2 * ρ),
          ((H k).connection s).curvatureTensorNorm x ≤ 1 := by
    filter_upwards [hdistance, hpastH ((1 / (n : ℝ) ^ 2) / (n : ℝ) ^ 2) (by positivity)]
      with k hk hsmall
    have hscalarH : ∀ x ∈ ((H k).metric 0).ball (q k) (2 * 1),
        ((H k).connection 0).scalarCurvature x ≤ 1 / (n : ℝ) ^ 2 := by
      intro x hx
      have hh := hsmall 0 le_rfl x (by simpa using hx)
      calc
        _ ≤ (n : ℝ) ^ 2 * (((1 / (n : ℝ) ^ 2) / (n : ℝ) ^ 2)) :=
          (le_abs_self _).trans
            ((((H k).connection 0).abs_scalarCurvature_le_curvatureTensorNorm x).trans
              (mul_le_mul_of_nonneg_left hh.le (sq_nonneg _)))
        _ = _ := by field_simp
    obtain ⟨_, _, hpast, L, Φ, hsource, htarget, hzero, horth, hderiv, hgeo, hdist⟩ :=
      F.ancientRescaleAt_uniform_exponential_chart_of_scalar_bound hC hcomplete hoperator
        hK hbound hκ hnoncollapse hn (c * Q k) (mul_pos hc (hQ k))
        (t₀ - 1 / Q k) (htcenter k) 0 le_rfl (q k)
        (by norm_num : (0 : ℝ) < 1) (by positivity : 0 ≤ 1 / (n : ℝ) ^ 2) hscalarH
        (by rw [hnA]; norm_num)
    simp only [hnA, one_pow, mul_one] at hsource htarget hpast hdist
    refine ⟨L, Φ, hsource, htarget, hzero, ?_, horth, hderiv, ?_, hdist, ?_⟩
    · intro x hx
      letI := ((H k).metric 0).toMetricSpace
      rw [← ((H k).metric 0).toMetricSpace_ball, Metric.mem_ball]
      change (((H k).metric 0).edist x (q k)).toReal < ρ / 8
      rw [hdistHG]
      exact (mul_le_mul_of_nonneg_left (hk x hx) hsq.le).trans_lt hsD
    · intro w hw t ht
      exact hgeo w (Metric.ball_subset_ball hρ1.le hw) t (Metric.ball_subset_ball hρ1.le ht)
    · intro s hs x hx
      exact hpast s hs x (hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith)))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hcharts
  let τ : ℕ → ℕ := fun k => k + N
  have hτ : StrictMono τ := fun _ _ hij => Nat.add_lt_add_right hij N
  choose L Φ hsource htarget hzero hΩ horth hderiv hgeo hdist hcurv using
    fun k => hN (τ k) (Nat.le_add_left N k)
  have hdecay : ∀ ε > 0, ∀ᶠ k in atTop,
      ∀ x ∈ ((H (τ k)).metric 0).ball (q (τ k)) (2 * ρ),
        ((H (τ k)).connection 0).curvatureTensorNorm x ≤ ε := by
    intro ε hε
    filter_upwards [hτ.tendsto_atTop.eventually (hpastH ε hε)] with k hk
    intro x hx
    exact (hk 0 le_rfl x (hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith)))).le
  obtain ⟨σ, hσ, hjets⟩ := exists_terminal_exponential_euclidean_coefficient_subsequence
    hC (by norm_num : (0 : ℝ) < 1) hρ (by positivity : 0 < ρ / 4)
    (by linarith : ρ / 4 < ρ / 2) (fun k => H (τ k))
    (fun k => hcompleteH (τ k)) (fun k => hoperatorH (τ k)) (fun k => q (τ k))
    hcurv hdecay L Φ hsource hzero horth hderiv hgeo hdist
  refine ⟨c, hc, hsD, τ ∘ σ, hτ.comp hσ, L ∘ σ, Φ ∘ σ, ?_, hjets⟩
  intro k
  exact ⟨hsource (σ k), htarget (σ k), hzero (σ k), hΩ (σ k), horth (σ k),
    hderiv (σ k), hgeo (σ k), hdist (σ k), hcurv (σ k)⟩

end PoincareConjecture.RicciFlow
