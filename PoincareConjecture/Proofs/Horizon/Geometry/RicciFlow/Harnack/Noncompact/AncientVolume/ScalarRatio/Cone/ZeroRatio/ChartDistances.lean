import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.RadialModel
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.AnnularDistance

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

theorem exists_uniform_distance_limit_on_closedBall_of_normal_chart_coefficients
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : ℕ → RiemannianMetric n M)
    (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (q : ℕ → M)
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {S : ℝ} (hS : 0 < S)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (htarget : ∀ k, (Φ k).target = (g k).ball (q k) S)
    (hradial : ∀ k x, x ∈ Metric.ball 0 S →
      (g k).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V) (hzero : 0 ∈ V)
    (hconv : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ V →
      TendstoUniformlyOn (fun k => (g k).pullbackCoefficients (Φ k))
        h.euclideanCoefficients atTop K) :
    ∃ r : ℝ, 0 < r ∧ 2 * r < S ∧ Metric.closedBall 0 (2 * r) ⊆ V ∧
      TendstoUniformlyOn
        (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
          ((g k).edist (Φ k z.1) (Φ k z.2)).toReal)
        (fun z => (h.edist z.1 z.2).toReal) atTop
        (Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r) := by
  obtain ⟨W, hWo, hzeroW, hWV, _, hdist⟩ :=
    exists_uniform_distance_limit_of_normal_chart_coefficients g h q Φ hS
      hsource htarget hradial hV hzero hconv
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.mp (hWo.mem_nhds hzeroW)
  let r : ℝ := min (δ / 4) (S / 4)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have h2rδ : 2 * r < δ := by
    have := min_le_left (δ / 4) (S / 4)
    dsimp [r]
    linarith
  have h2rS : 2 * r < S := by
    have := min_le_right (δ / 4) (S / 4)
    dsimp [r]
    linarith
  have h2rW : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * r) ⊆ W :=
    (Metric.closedBall_subset_ball h2rδ).trans hδW
  have hrW : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ W :=
    (Metric.closedBall_subset_closedBall (by linarith : r ≤ 2 * r)).trans h2rW
  exact ⟨r, hr, h2rS, h2rW.trans hWV, hdist.mono (Set.prod_mono hrW hrW)⟩

end PoincareConjecture.RiemannianMetric

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_flat_radial_chart_with_source_distances_of_zero_ratio
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
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    ∃ (q : ℕ → M) (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k),
      Tendsto Q atTop (𝓝 0) ∧
      Tendsto (fun k => ((F.metric t₀).edist p (q k)).toReal) atTop atTop ∧
      ∃ S : ℝ, 0 < S ∧ S < 1 / 8 ∧
      ∃ L₀ : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      let G := fun k => F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀
      (∀ k, (((G k).metric 0).edist p (q k)).toReal = 1) ∧
      (∀ k s, s ≤ 0 → ∀ x ∈ ((G k).metric 0).ball (q k) (2 * S),
        ((G k).connection s).curvatureTensorNorm x ≤ 5) ∧
      (∀ k, (Φ k).source = Metric.ball 0 S ∧
        (Φ k).target = ((G k).metric 0).ball (q k) S ∧ Φ k 0 = q k ∧
        (∀ v w, ((G k).metric 0).pullbackCoefficients
          (extChartAt (𝓡 n) (q k)).symm (extChartAt (𝓡 n) (q k) (q k))
            (L₀ k v) (L₀ k w) = inner ℝ v w) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) (q k) (Φ k w))
          (L₀ k).toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 S, ((G k).metric 0).IsGeodesicOn
          (fun t => Φ k (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 S}) ∧
        ∀ w ∈ Metric.ball 0 S,
          ((G k).metric 0).edist (q k) (Φ k w) = ENNReal.ofReal ‖w‖) ∧
      ∃ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (D : LeviCivitaData g) (r : ℝ), 0 < r ∧ 2 * r < S ∧
        (∀ v w, g.inner 0 v w = inner ℝ v w) ∧
        (∀ m E, IsCompact E → E ⊆ Metric.closedBall 0 (2 * r) → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k)))
          (iteratedFDeriv ℝ m g.euclideanCoefficients) atTop E) ∧
        (TendstoUniformlyOn
          (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
            (((G k).metric 0).edist (Φ k z.1) (Φ k z.2)).toReal)
          (fun z => (g.edist z.1 z.2).toReal) atTop
          (Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r)) ∧
        ∃ C : ℝ≥0, ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
          LipschitzOnWith C f (Metric.closedBall 0 (2 * r)) ∧
          TendstoUniformlyOn
            (fun k x => (((G k).metric 0).edist p (Φ k x)).toReal ^ 2 / 2)
            f atTop (Metric.closedBall 0 (2 * r)) ∧ f 0 = 1 / 2 ∧
          ∀ x ∈ Metric.closedBall 0 (2 * r),
            0 < f x ∧ ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x ∧
              D.curvatureTensorNorm x = 0 ∧
              (∀ v w : EuclideanSpace ℝ (Fin n), D.hessian f x v w = g.inner x v w) ∧
              g.inner x (D.gradient f x) (D.gradient f x) = 2 * f x := by
  obtain ⟨q, Q, hQ, hQzero, hescape, S, hS, hSr, L₀, Φ, hcenter, hcurv, hcharts,
    g, D, V, _, _, _, hnorm, hjets, hflat, R, hR, _, hRV, C, f,
    hLip, hpotential, hf0, _⟩ :=
    F.exists_flat_annular_limit_with_radial_potential_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse hn t₀ ht₀ p hzero
  let G := fun k => F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀
  have hsec : (F.connection t₀).NonnegativeSectionalCurvature := by
    intro x v w
    exact (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  have hsmallV : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 2) ⊆ V :=
    (fun x hx => hRV (Metric.ball_subset_closedBall
      ((Metric.ball_subset_ball (by linarith : R / 2 ≤ R)) hx)))
  have hcoeff : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ V →
      TendstoUniformlyOn (fun k => ((G k).metric 0).pullbackCoefficients (Φ k))
        g.euclideanCoefficients atTop K := by
    intro E hE hEV
    have hh := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn (hjets 0 E hE hEV)
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using hh
  obtain ⟨W, hWo, hzeroW, hWsmall, hmodel⟩ :=
    (F.metric t₀).exists_local_radial_model_of_rescaled_normal_charts
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p g D q Q hQ hQzero Φ hS
      (fun k => (hcharts k).1)
      (fun k => by simpa only [ancientRescaleAt_metric, zero_div, add_zero]
        using (hcharts k).2.1)
      (fun k => by simpa only [ancientRescaleAt_metric, zero_div, add_zero]
        using (hcharts k).2.2.2.2.2.2)
      Metric.isOpen_ball (Metric.mem_ball_self (by positivity : 0 < R / 2))
      (fun E hE hEW => by
        simpa only [G, ancientRescaleAt_metric, zero_div, add_zero] using
          hcoeff E hE (hEW.trans hsmallV))
      f (by rw [hf0]; norm_num)
      (Subset.rfl : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 2) ⊆ Metric.ball 0 (R / 2))
      hLip (by simpa only [ancientRescaleAt_metric, zero_div, add_zero] using
        hpotential.mono Metric.ball_subset_closedBall)
  have hWV : W ⊆ V := hWsmall.trans hsmallV
  obtain ⟨r, hr, h2rS, h2rW, hdist⟩ :=
    RiemannianMetric.exists_uniform_distance_limit_on_closedBall_of_normal_chart_coefficients
      (fun k => (G k).metric 0) g q Φ hS (fun k => (hcharts k).1)
      (fun k => (hcharts k).2.1) (fun k => (hcharts k).2.2.2.2.2.2)
      hWo hzeroW (fun E hE hEW => hcoeff E hE (hEW.trans hWV))
  have hpotDomain : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * r) ⊆
      Metric.closedBall 0 (R / 2) := h2rW.trans (hWsmall.trans Metric.ball_subset_closedBall)
  refine ⟨q, Q, hQ, hQzero, hescape, S, hS, hSr, L₀, Φ, hcenter, hcurv, hcharts,
    g, D, r, hr, h2rS, hnorm, ?_, hdist, C, f, hLip.mono hpotDomain,
    hpotential.mono hpotDomain, hf0, ?_⟩
  · intro m E hE hEr
    exact hjets m E hE (hEr.trans (h2rW.trans hWV))
  · intro x hx
    exact ⟨(hmodel x (h2rW hx)).1, (hmodel x (h2rW hx)).2.1,
      hflat x (hWV (h2rW hx)), (hmodel x (h2rW hx)).2.2.1,
      (hmodel x (h2rW hx)).2.2.2⟩

theorem exists_distance_normalized_flat_radial_chart_with_source_distances
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
    (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k) (hQzero : Tendsto Q atTop (𝓝 0))
    (q : ℕ → M)
    (hcenter : Tendsto (fun k => Real.sqrt (Q k) * ((F.metric t₀).edist p (q k)).toReal)
      atTop (𝓝 1)) :
    ∃ S : ℝ, 0 < S ∧ S < 1 / 8 ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ L₀ : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      let G := fun k => F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀
      (∀ k, 3 / 4 ≤ (((G k).metric 0).edist p (q (σ k))).toReal) ∧
      Tendsto (fun k => (((G k).metric 0).edist p (q (σ k))).toReal) atTop (𝓝 1) ∧
      (∀ k s, s ≤ 0 → ∀ x ∈ ((G k).metric 0).ball (q (σ k)) (2 * S),
        ((G k).connection s).curvatureTensorNorm x ≤ 5) ∧
      (∀ k, (Φ k).source = Metric.ball 0 S ∧
        (Φ k).target = ((G k).metric 0).ball (q (σ k)) S ∧ Φ k 0 = q (σ k) ∧
        (∀ v w, ((G k).metric 0).pullbackCoefficients
          (extChartAt (𝓡 n) (q (σ k))).symm (extChartAt (𝓡 n) (q (σ k)) (q (σ k)))
            (L₀ k v) (L₀ k w) = inner ℝ v w) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) (q (σ k)) (Φ k w))
          (L₀ k).toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 S, ((G k).metric 0).IsGeodesicOn
          (fun t => Φ k (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 S}) ∧
        ∀ w ∈ Metric.ball 0 S,
          ((G k).metric 0).edist (q (σ k)) (Φ k w) = ENNReal.ofReal ‖w‖) ∧
      ∃ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (D : LeviCivitaData g) (r : ℝ), 0 < r ∧ 2 * r < S ∧
        (∀ v w, g.inner 0 v w = inner ℝ v w) ∧
        (∀ m E, IsCompact E → E ⊆ Metric.closedBall 0 (2 * r) → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k)))
          (iteratedFDeriv ℝ m g.euclideanCoefficients) atTop E) ∧
        TendstoUniformlyOn
          (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
            (((G k).metric 0).edist (Φ k z.1) (Φ k z.2)).toReal)
          (fun z => (g.edist z.1 z.2).toReal) atTop
          (Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r) ∧
        ∃ C : ℝ≥0, ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
          LipschitzOnWith C f (Metric.closedBall 0 (2 * r)) ∧
          TendstoUniformlyOn
            (fun k x => (((G k).metric 0).edist p (Φ k x)).toReal ^ 2 / 2)
            f atTop (Metric.closedBall 0 (2 * r)) ∧ f 0 = 1 / 2 ∧
          ∀ x ∈ Metric.closedBall 0 (2 * r),
            0 < f x ∧ ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x ∧
              D.curvatureTensorNorm x = 0 ∧
              (∀ v w : EuclideanSpace ℝ (Fin n), D.hessian f x v w = g.inner x v w) ∧
              g.inner x (D.gradient f x) (D.gradient f x) = 2 * f x := by
  obtain ⟨S, hS, hSr, σ, hσ, L₀, Φ, hmargin, hcurv, hcharts, g, D, V,
    hVo, hzeroV, _, hnorm, hjets, hflat⟩ :=
    F.exists_distance_normalized_flat_annular_limit hC hcomplete hoperator hK hbound
      hκ hnoncollapse hn t₀ ht₀ p hzero Q hQ hQzero q hcenter
  let G := fun k => F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀
  have hcenterG : Tendsto (fun k => (((G k).metric 0).edist p (q (σ k))).toReal)
      atTop (𝓝 1) := by
    simpa only [G, ancientRescaleAt_edist_toReal_zero, Function.comp_def] using
      hcenter.comp hσ.tendsto_atTop
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp (hVo.mem_nhds hzeroV)
  let R : ℝ := min (δ / 2) (S / 2)
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hRS : R < S := (min_le_right _ _).trans_lt (by linarith)
  have hRV : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ V :=
    (Metric.closedBall_subset_ball
      ((min_le_left _ _).trans_lt (by linarith : δ / 2 < δ))).trans hδV
  have hcoeff : ∀ E : Set (EuclideanSpace ℝ (Fin n)), IsCompact E → E ⊆ V →
      TendstoUniformlyOn (fun k => ((G k).metric 0).pullbackCoefficients (Φ k))
        g.euclideanCoefficients atTop E := by
    intro E hE hEV
    have hh := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn (hjets 0 E hE hEV)
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using hh
  obtain ⟨τ, hτ, C, f, hLip, hpotential, hfzero, _, _⟩ :=
    RiemannianMetric.exists_radial_square_limit_of_normal_chart_coefficients
      (fun k => (G k).metric 0) p (fun k => q (σ k)) Φ hR hRS.le
      (fun k => (hcharts k).1) (fun k => (hcharts k).2.2.1)
      (fun k => (hcharts k).2.2.2.2.2.2) hcenterG g.euclideanCoefficients
      (fun x _ => (g.contDiffAt_euclideanCoefficients x).continuousAt.continuousWithinAt)
      (hcoeff _ (isCompact_closedBall _ _) hRV)
  have hf0 : f 0 = 1 / 2 := by simpa only [one_pow] using hfzero
  let ι : ℕ → ℕ := fun k => σ (τ k)
  have hι : StrictMono ι := hσ.comp hτ
  have hcoeffτ : ∀ E : Set (EuclideanSpace ℝ (Fin n)), IsCompact E → E ⊆ V →
      TendstoUniformlyOn (fun k => ((G (τ k)).metric 0).pullbackCoefficients (Φ (τ k)))
        g.euclideanCoefficients atTop E := by
    intro E hE hEV A hA
    exact hτ.tendsto_atTop.eventually (hcoeff E hE hEV A hA)
  have hsec : (F.connection t₀).NonnegativeSectionalCurvature := by
    intro x v w
    exact (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  have hsmallV : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 2) ⊆ V :=
    (fun x hx => hRV (Metric.ball_subset_closedBall
      ((Metric.ball_subset_ball (by linarith : R / 2 ≤ R)) hx)))
  obtain ⟨W, hWo, hzeroW, hWsmall, hmodel⟩ :=
    (F.metric t₀).exists_local_radial_model_of_rescaled_normal_charts
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p g D
      (fun k => q (ι k)) (fun k => Q (ι k)) (fun k => hQ (ι k))
      (hQzero.comp hι.tendsto_atTop) (fun k => Φ (τ k)) hS
      (fun k => (hcharts (τ k)).1)
      (fun k => by simpa only [ancientRescaleAt_metric, zero_div, add_zero]
        using (hcharts (τ k)).2.1)
      (fun k => by simpa only [ancientRescaleAt_metric, zero_div, add_zero]
        using (hcharts (τ k)).2.2.2.2.2.2)
      Metric.isOpen_ball (Metric.mem_ball_self (by positivity : 0 < R / 2))
      (fun E hE hEW => by
        simpa only [G, ancientRescaleAt_metric, zero_div, add_zero] using
          hcoeffτ E hE (hEW.trans hsmallV))
      f (by rw [hf0]; norm_num)
      (Subset.rfl : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 2) ⊆ Metric.ball 0 (R / 2))
      hLip (by simpa only [G, ancientRescaleAt_metric, zero_div, add_zero] using
        hpotential.mono Metric.ball_subset_closedBall)
  have hWV : W ⊆ V := hWsmall.trans hsmallV
  obtain ⟨r, hr, h2rS, h2rW, hdist⟩ :=
    RiemannianMetric.exists_uniform_distance_limit_on_closedBall_of_normal_chart_coefficients
      (fun k => (G (τ k)).metric 0) g (fun k => q (ι k)) (fun k => Φ (τ k)) hS
      (fun k => (hcharts (τ k)).1) (fun k => (hcharts (τ k)).2.1)
      (fun k => (hcharts (τ k)).2.2.2.2.2.2)
      hWo hzeroW (fun E hE hEW => hcoeffτ E hE (hEW.trans hWV))
  have hpotDomain : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * r) ⊆
      Metric.closedBall 0 (R / 2) := h2rW.trans (hWsmall.trans Metric.ball_subset_closedBall)
  refine ⟨S, hS, hSr, ι, hι, (fun k => L₀ (τ k)), (fun k => Φ (τ k)),
    (fun k => hmargin (τ k)), hcenterG.comp hτ.tendsto_atTop,
    (fun k => hcurv (τ k)), (fun k => hcharts (τ k)),
    g, D, r, hr, h2rS, hnorm, ?_, hdist, C, f, hLip.mono hpotDomain,
    hpotential.mono hpotDomain, hf0, ?_⟩
  · intro m E hE hEr A hA
    exact hτ.tendsto_atTop.eventually
      (hjets m E hE (hEr.trans (h2rW.trans hWV)) A hA)
  · intro x hx
    exact ⟨(hmodel x (h2rW hx)).1, (hmodel x (h2rW hx)).2.1,
      hflat x (hWV (h2rW hx)), (hmodel x (h2rW hx)).2.2.1,
      (hmodel x (h2rW hx)).2.2.2⟩

end PoincareConjecture.RicciFlow
