import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Backward.MetricJets

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Topology Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_common_backward_static_metric_jets_of_zero_ratio
    {n : ℕ} {M : Type u} {ι : Type*} [TopologicalSpace M] [T3Space M]
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
    (q : ι → ℕ → M)
    (hcenter : ∀ j i, 3 / 4 ≤
      (((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric 0).edist p (q j i)).toReal)
    {S : ℝ} (hS : 0 < S) (hSsmall : S < 1 / 8)
    (L₀ : ℕ → ι → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (Φ : ℕ → ι → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (hsource : ∀ i j, (Φ i j).source = Metric.ball 0 S)
    (hzeroΦ : ∀ i j, Φ i j 0 = q j i)
    (horth : ∀ i j v w,
      ((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric 0).pullbackCoefficients
        (extChartAt (𝓡 n) (q j i)).symm (extChartAt (𝓡 n) (q j i) (q j i))
        (L₀ i j v) (L₀ i j w) = inner ℝ v w)
    (hderiv : ∀ i j, HasFDerivAt (fun w => extChartAt (𝓡 n) (q j i) (Φ i j w))
      (L₀ i j).toContinuousLinearMap 0)
    (hgeo : ∀ i j w, w ∈ Metric.ball 0 S →
      ((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric 0).IsGeodesicOn
        (fun t => Φ i j (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 S})
    (hdist : ∀ i j w, w ∈ Metric.ball 0 S →
      ((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric 0).edist (q j i) (Φ i j w) =
        ENNReal.ofReal ‖w‖)
    (g : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n))) {R : ℝ} (hR : 0 < R)
    (hterminal : ∀ j x, x ∈ Metric.ball 0 R → Tendsto
      (fun i => ((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric 0).pullbackCoefficients
        (Φ i j) x) atTop (𝓝 ((g j).euclideanCoefficients x))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧ ρ < S / 2 ∧ ∀ j : ι, ∀ m : ℕ,
      TendstoUniformlyOn
        (fun i (z : ℝ × EuclideanSpace ℝ (Fin n)) => iteratedFDeriv ℝ m
          (((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric z.1).pullbackCoefficients
            (Φ i j)) z.2)
        (fun z => iteratedFDeriv ℝ m (g j).euclideanCoefficients z.2) atTop
        (Icc (-1) 0 ×ˢ Metric.closedBall 0 ρ) := by
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
  have hdecay (ε : ℝ) (hε : 0 < ε) : ∀ᶠ i in atTop, ∀ j : ι, ∀ t ≤ 0,
      ∀ x ∈ ((G i).metric 0).ball (q j i) (2 * S),
        ((G i).connection t).curvatureTensorNorm x < ε := by
    filter_upwards [F.eventually_ancientRescaleAt_annular_curvature_lt_of_zero_ratio
      hC hcomplete hoperator hK hbound t₀ ht₀ p hzero Q hQ hQzero
      (by norm_num : (0 : ℝ) < 1 / 2) hε] with i hi
    intro j t ht x hx
    have hmargin : 1 / 2 + 2 * S ≤ (((G i).metric 0).edist p (q j i)).toReal := by
      have hh := hcenter j i
      change 3 / 4 ≤ (((G i).metric 0).edist p (q j i)).toReal at hh
      linarith
    exact hi t ht x (((G i).metric 0).radial_lower_bound_on_ball p (q j i) hmargin x hx).le
  obtain ⟨r, hr, hrS, hspatial⟩ :=
    exists_ancient_exponential_spatial_jet_bounds hC n (by norm_num : (0 : ℝ) < 1) hS
  let r₀ : ℝ := min R r
  have hr₀ : 0 < r₀ := lt_min hR hr
  have hr₀R : r₀ ≤ R := min_le_left _ _
  have hr₀r : r₀ ≤ r := min_le_right _ _
  have hr₀S : r₀ < S := by linarith
  have hsub (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 r₀) :
      x ∈ Metric.closedBall 0 r :=
    (Metric.closedBall_subset_closedBall hr₀r) (Metric.ball_subset_closedBall hx)
  have hsubS : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r₀ ⊆ Metric.ball 0 S :=
    Metric.ball_subset_ball hr₀S.le
  have hmaps (i : ℕ) (j : ι) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ Metric.ball 0 r₀) :
      Φ i j x ∈ ((G i).metric 0).ball (q j i) (2 * S) := by
    change ((G i).metric 0).edist (q j i) (Φ i j x) < ENNReal.ofReal (2 * S)
    rw [hdist i j x (hsubS hx), ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg x)]
    have hxnorm : ‖x‖ < r₀ := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    linarith
  have he (i : ℕ) (j : ι) : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (Φ i j) (Metric.ball 0 S) := by
    simpa only [hsource i j] using (Φ i j).contMDiffOn
  have hjets (m : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ i in atTop, ∀ j : ι,
      ∀ t ∈ Icc (-1) 0, ∀ x ∈ Metric.ball 0 r₀,
        ‖iteratedFDeriv ℝ m (((G i).metric t).pullbackCoefficients (Φ i j)) x‖ ≤ B := by
    obtain ⟨B, hB, hjet⟩ := hspatial 1 (by norm_num) m
    refine ⟨B, hB, ?_⟩
    filter_upwards [hdecay 1 zero_lt_one] with i hi
    intro j t ht x hx
    exact hjet M (G i) (hcompleteG i) (hoperatorG i) (q j i)
      (fun s hs y hy => (hi j s hs y hy).le) (L₀ i j) (Φ i j) (hsource i j) (hzeroΦ i j)
      (horth i j) (hderiv i j) (hgeo i j) (hdist i j) t ht x (hsub x hx) m le_rfl
  refine ⟨r₀ / 2, by positivity, by linarith, by linarith, ?_⟩
  intro j m
  have hsmooth (i : ℕ) (t : ℝ) (_ht : t ∈ Icc (-1) 0) :
      ContDiffOn ℝ ∞ (((G i).metric t).pullbackCoefficients (Φ i j)) (Metric.ball 0 r₀) := by
    intro x hx
    exact (((G i).metric t).contDiffAt_pullbackCoefficients
      ((he i j).contMDiffAt (Metric.isOpen_ball.mem_nhds (hsubS hx)))).contDiffWithinAt
  have hpoint (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 r₀)
      (ε : ℝ) (hε : 0 < ε) : ∀ᶠ i in atTop, ∀ t ∈ Icc (-1) 0,
      dist (((G i).metric t).pullbackCoefficients (Φ i j) x)
        ((g j).euclideanCoefficients x) < ε := by
    obtain ⟨B, hB, hcoefficient⟩ := hjets 0
    let c : ℝ := 2 * (n : ℝ) ^ 3 * B
    have hc : 0 ≤ c := by dsimp [c]; positivity
    let δ : ℝ := ε / (2 * (c + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδsmall : c * δ < ε / 2 := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (by positivity : 0 < 2 * (c + 1))).mpr
      nlinarith
    have hterm := Metric.tendsto_nhds.mp
      (hterminal j x ((Metric.ball_subset_ball hr₀R) hx)) (ε / 2) (by positivity)
    filter_upwards [hcoefficient, hdecay δ hδ, hterm] with i hi hiδ hit
    intro t ht
    have hnorm : ∀ s ∈ Icc (-1) 0,
        ‖((G i).metric s).pullbackCoefficients (Φ i j) x‖ ≤ B := by
      intro s hs
      simpa only [norm_iteratedFDeriv_zero] using hi j s hs x hx
    have hmove := (G i).norm_pullbackCoefficients_sub_zero_le_of_curvature_bound
      Metric.isOpen_ball (he i j) (hsubS hx) (by norm_num : (0 : ℝ) ≤ 1) hδ.le hB
      (fun s hs => (hiδ j s hs.2 (Φ i j x) (hmaps i j x hx)).le) hnorm ht
    have hfirst : dist (((G i).metric t).pullbackCoefficients (Φ i j) x)
        (((G i).metric 0).pullbackCoefficients (Φ i j) x) < ε / 2 := by
      rw [dist_eq_norm]
      apply hmove.trans_lt
      simpa only [c, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using hδsmall
    exact (dist_triangle _ (((G i).metric 0).pullbackCoefficients (Φ i j) x) _).trans_lt
      (by linarith)
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  have hall := Poincare.Analysis.Calculus.eventually_uniform_spatial_jets_of_uniform_values
    Metric.isOpen_ball (Icc (-1 : ℝ) 0)
    (fun i t => ((G i).metric t).pullbackCoefficients (Φ i j)) (g j).euclideanCoefficients
    hsmooth hpoint (fun C _ hCsub m => by
      obtain ⟨B, _, hB⟩ := hjets m
      refine ⟨B, ?_⟩
      filter_upwards [hB] with i hi
      exact fun t ht x hx => hi j t ht x (hCsub hx))
    m (isCompact_closedBall 0 (r₀ / 2)) (Metric.closedBall_subset_ball (by linarith)) hε
  filter_upwards [hall] with i hi z hz
  simpa only [dist_comm] using hi z.1 hz.1 z.2 hz.2

end PoincareConjecture.RicciFlow
