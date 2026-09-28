import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.UniformCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Compactness











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.RicciFlow



theorem exists_common_annular_chart_coefficients_of_zero_ratio
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
    (hn : 1 ≤ n) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (hQzero : Tendsto Q atTop (𝓝 0))
    (q : ℕ → ℕ → M)
    (hcenter : ∀ j k, 3 / 4 ≤
      (((F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀).metric 0).edist p (q j k)).toReal) :
    ∃ S : ℝ, 0 < S ∧ S < 1 / 8 ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ L₀ : ℕ → ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : ℕ → ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      let G := fun k => F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀
      (∀ k j s, s ≤ 0 → ∀ x ∈ ((G k).metric 0).ball (q j (σ k)) (2 * S),
        ((G k).connection s).curvatureTensorNorm x ≤ 5) ∧
      (∀ k j, (Φ k j).source = Metric.ball 0 S ∧
        (Φ k j).target = ((G k).metric 0).ball (q j (σ k)) S ∧
        Φ k j 0 = q j (σ k) ∧
        (∀ v w, ((G k).metric 0).pullbackCoefficients
          (extChartAt (𝓡 n) (q j (σ k))).symm
          (extChartAt (𝓡 n) (q j (σ k)) (q j (σ k)))
            (L₀ k j v) (L₀ k j w) = inner ℝ v w) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) (q j (σ k)) (Φ k j w))
          (L₀ k j).toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 S, ((G k).metric 0).IsGeodesicOn
          (fun t => Φ k j (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 S}) ∧
        ∀ w ∈ Metric.ball 0 S,
          ((G k).metric 0).edist (q j (σ k)) (Φ k j w) = ENNReal.ofReal ‖w‖) ∧
      ∃ B : ℕ → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        (∀ j, ContDiffOn ℝ ∞ (B j) (Metric.ball 0 (S / 4))) ∧
        (∀ j m C, IsCompact C → C ⊆ Metric.ball 0 (S / 4) → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k j)))
          (iteratedFDeriv ℝ m (B j)) atTop C) ∧
        (∀ j v w, B j 0 v w = inner ℝ v w) ∧
        ∃ r : ℝ, 0 < r ∧ 2 * r < S / 4 ∧
          (∀ k j, ∀ x ∈ Metric.closedBall 0 (2 * r), ∀ v,
            (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ((G k).metric 0).pullbackCoefficients (Φ k j) x v v ∧
            ((G k).metric 0).pullbackCoefficients (Φ k j) x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) ∧
          ∀ j, ∀ x ∈ Metric.closedBall 0 (2 * r), ∀ v,
            (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ B j x v v ∧
            B j x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2 := by
  obtain ⟨S, hS, hSr, hevent⟩ := F.eventually_uniform_annular_charts_of_zero_ratio
    hC hcomplete hoperator hK hbound hκ hnoncollapse hn t₀ ht₀ p hzero Q hQ hQzero
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let H := fun k => F.ancientRescaleAt (Q (k + N)) (hQ (k + N)) t₀ ht₀
  have hgood (k j : ℕ) := hN (k + N) (by omega) (q j (k + N)) (hcenter j (k + N))
  choose L Φ hsource htarget hzeroΦ horth hderiv hgeo hdist using
    (fun k j => (hgood k j).2)
  have hcompleteH : ∀ k t, t ≤ 0 → MetricComplete ((H k).metric t) := by
    intro k t ht
    apply F.parabolicRescale_metricComplete
    exact hcomplete _ ((add_le_of_nonpos_right
      (div_nonpos_of_nonpos_of_nonneg ht (hQ (k + N)).le)).trans ht₀)
  have hoperatorH : ∀ k t, t ≤ 0 → ∀ x,
      ((H k).connection t).NonnegativeCurvatureOperator x := by
    intro k t ht x
    apply F.parabolicRescale_nonnegativeCurvatureOperator
    exact hoperator _ ((add_le_of_nonpos_right
      (div_nonpos_of_nonpos_of_nonneg ht (hQ (k + N)).le)).trans ht₀) x
  let f := fun j k => ((H k).metric 0).pullbackCoefficients (Φ k j)
  have he (k j : ℕ) : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (Φ k j) (Metric.ball 0 S) := by
    simpa only [hsource k j] using (Φ k j).contMDiffOn
  have hnorm (k j : ℕ) : ∀ v w, f j k 0 v w = inner ℝ v w :=
    ((H k).metric 0).pullbackCoefficients_zero_of_orthonormal (q j (k + N))
      ((he k j).contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hS)))
      (hzeroΦ k j) (hderiv k j) (horth k j)
  obtain ⟨r, hr, hrS, hsmall⟩ := RiemannianMetric.exists_uniform_radial_comparison_radius
    (by positivity : 0 < S / 4) (5 : ℝ)
  have hradial (k j : ℕ) (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ Metric.ball 0 S) :
      ((H k).metric 0).IsGeodesicOn (fun t : ℝ => Φ k j (t • v))
          {t : ℝ | t • v ∈ Metric.ball 0 S} ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          ((H k).metric 0).tangentNorm (Φ k j (t • v))
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => Φ k j (s • v)) t 1) = ‖v‖ ∧
          ((H k).metric 0).edist (q j (k + N)) (Φ k j (t • v)) ≤
            ENNReal.ofReal ‖v‖ * ENNReal.ofReal t := by
    refine ⟨hgeo k j v hv, ?_⟩
    intro t ht
    refine ⟨((H k).metric 0).tangentNorm_radial_of_normalized_exponential
      (q j (k + N)) (L k j) (hzeroΦ k j) (horth k j) (hderiv k j) (hgeo k j) hv ht, ?_⟩
    have htv : t • v ∈ Metric.ball 0 S := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt
        (by simpa only [one_mul, Metric.mem_ball, dist_zero_right] using hv)
    rw [hdist k j _ htv, norm_smul, Real.norm_of_nonneg ht.1,
      ENNReal.ofReal_mul ht.1, mul_comm]
  have helliptic (k j : ℕ) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ Metric.closedBall 0 (2 * r)) (v : EuclideanSpace ℝ (Fin n)) :
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ f j k x v v ∧
        f j k x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2 := by
    have hb := ((H k).metric 0).radial_exponential_uniform_bounds ((H k).connection 0)
      (by linarith : 2 * r < S) hsmall (he k j) (hnorm k j) (hradial k j)
      (fun y hy => (hgood k j).1 0 le_rfl y
        (hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith : S ≤ 2 * S))))
    exact ((hb x hx).2 v).2
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (S / 4) ⊆ Metric.ball 0 S :=
    Metric.ball_subset_ball (by linarith)
  have hf (j k : ℕ) : ContDiffOn ℝ ∞ (f j k) (Metric.ball 0 (S / 4)) := by
    intro x hx
    exact (((H k).metric 0).contDiffAt_pullbackCoefficients
      ((he k j).contMDiffAt (Metric.isOpen_ball.mem_nhds (hsub hx)))).contDiffWithinAt
  have hjbound : ∀ j (C : Set (EuclideanSpace ℝ (Fin n))), IsCompact C →
      C ⊆ Metric.ball 0 (S / 4) → ∀ m : ℕ,
      ∃ A : ℝ, ∀ᶠ k in atTop, ∀ x ∈ C, ‖iteratedFDeriv ℝ m (f j k) x‖ ≤ A := by
    intro j C _ hCball m
    obtain ⟨A, _, hA⟩ := exists_terminal_exponential_metric_jet_bound hC n m
      (by norm_num : (0 : ℝ) < 5) hS (by positivity : 0 < S / 4)
      (by linarith : S / 4 < S / 2)
    refine ⟨A, Eventually.of_forall ?_⟩
    intro k x hx
    exact hA M (H k) (hcompleteH k) (hoperatorH k) (q j (k + N))
      (hgood k j).1 (L k j) (Φ k j) (hsource k j) (hzeroΦ k j)
      (horth k j) (hderiv k j) (hgeo k j) (hdist k j) x
      (Metric.ball_subset_closedBall (hCball hx))
  obtain ⟨τ, hτ, B, hB, hjets⟩ :=
    Poincare.Analysis.Calculus.exists_common_smoothSubsequenceExtraction_finiteDimensional
      (E := fun _ : ℕ => EuclideanSpace ℝ (Fin n))
      (F := fun _ : ℕ =>
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (Ω := fun _ => Metric.ball 0 (S / 4)) (fun _ => Metric.isOpen_ball) f hf hjbound
  refine ⟨S, hS, hSr, fun k => τ k + N,
    (fun i j hij => Nat.add_lt_add_right (hτ hij) N),
    (fun k => L (τ k)), (fun k => Φ (τ k)), ?_, ?_, B, hB, hjets, ?_, r, hr, hrS,
    (fun k j => helliptic (τ k) j), ?_⟩
  · intro k j
    exact (hgood (τ k) j).1
  · intro k j
    exact ⟨hsource (τ k) j, htarget (τ k) j, hzeroΦ (τ k) j,
      horth (τ k) j, hderiv (τ k) j, hgeo (τ k) j, hdist (τ k) j⟩
  · intro j v w
    have hzeroS : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 (S / 4) :=
      Metric.mem_ball_self (by positivity)
    have hconv : Tendsto (fun k => f j (τ k) 0) atTop (𝓝 (B j 0)) := by
      have hjet := hjets j 0 {0} isCompact_singleton (singleton_subset_iff.mpr hzeroS)
      have hvalue := (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn hjet
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
        hvalue.tendsto_at (mem_singleton 0)
    have hvalue := ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto (B j 0 v)).comp
      (((ContinuousLinearMap.apply ℝ
        (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) v).continuous.tendsto (B j 0)).comp hconv)
    exact tendsto_nhds_unique hvalue
      (tendsto_const_nhds.congr (fun k => (hnorm (τ k) j v w).symm))
  · intro j x hx v
    have hxS : x ∈ Metric.ball 0 (S / 4) := Metric.closedBall_subset_ball hrS hx
    have hconv : Tendsto (fun k => f j (τ k) x) atTop (𝓝 (B j x)) := by
      have hjet := hjets j 0 {x} isCompact_singleton (singleton_subset_iff.mpr hxS)
      have hvalue := (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn hjet
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
        hvalue.tendsto_at (mem_singleton x)
    have hvalue := ((ContinuousLinearMap.apply ℝ ℝ v).continuous.tendsto (B j x v)).comp
      (((ContinuousLinearMap.apply ℝ
        (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) v).continuous.tendsto (B j x)).comp hconv)
    exact ⟨ge_of_tendsto hvalue (Eventually.of_forall (fun k => (helliptic (τ k) j x hx v).1)),
      le_of_tendsto' hvalue (fun k => (helliptic (τ k) j x hx v).2)⟩

end PoincareConjecture.RicciFlow
