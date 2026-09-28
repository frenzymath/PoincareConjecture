import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.AnnularPotential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.MinimizingRay













noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal NNReal Bundle

universe u

namespace PoincareConjecture.RicciFlow




theorem exists_flat_annular_limit_with_radial_potential_of_zero_ratio
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
        (D : LeviCivitaData g) (V : Set (EuclideanSpace ℝ (Fin n))),
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ Metric.ball 0 (S / 4) ∧
        (∀ v w, g.inner 0 v w = inner ℝ v w) ∧
        (∀ m E, IsCompact E → E ⊆ V → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k)))
          (iteratedFDeriv ℝ m g.euclideanCoefficients) atTop E) ∧
        (∀ x ∈ V, D.curvatureTensorNorm x = 0) ∧
        ∃ R : ℝ, 0 < R ∧ R < S ∧ closedBall 0 R ⊆ V ∧
        ∃ C : ℝ≥0, ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
          LipschitzOnWith C f (closedBall 0 (R / 2)) ∧
          TendstoUniformlyOn
            (fun k x => (((G k).metric 0).edist p (Φ k x)).toReal ^ 2 / 2)
            f atTop (closedBall 0 (R / 2)) ∧
          f 0 = 1 / 2 ∧ ∀ x ∈ closedBall 0 (R / 2), 0 ≤ f x := by
  obtain ⟨ray, hray0, hray⟩ := (F.metric t₀).exists_minimizing_ray_of_metricComplete
    (hcomplete t₀ ht₀) p
  let q₀ : ℕ → M := fun k => ray ((k : ℝ) + 1)
  let Q₀ : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹ ^ 2
  have hQ₀ (k : ℕ) : 0 < Q₀ k := by dsimp [Q₀]; positivity
  have hdist (k : ℕ) : ((F.metric t₀).edist p (q₀ k)).toReal = (k : ℝ) + 1 := by
    have hh := hray 0 le_rfl ((k : ℝ) + 1) (by positivity)
    rw [hray0, zero_sub, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) + 1)] at hh
    change ((F.metric t₀).edist p (ray ((k : ℝ) + 1))).toReal = _
    rw [hh, ENNReal.toReal_ofReal (by positivity)]
  have htend : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => by linarith : ∀ k : ℕ, (k : ℝ) ≤ (k : ℝ) + 1)
      tendsto_natCast_atTop_atTop
  have hQzero : Tendsto Q₀ atTop (𝓝 0) := by
    simpa only [Q₀, Function.comp_def, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (tendsto_inv_atTop_zero.comp htend).pow 2
  have hnormCenter (k : ℕ) :
      Real.sqrt (Q₀ k) * ((F.metric t₀).edist p (q₀ k)).toReal = 1 := by
    rw [hdist]
    dsimp [Q₀]
    rw [Real.sqrt_sq (by positivity), inv_mul_cancel₀ (by positivity : (k : ℝ) + 1 ≠ 0)]
  have hcenter : Tendsto
      (fun k => Real.sqrt (Q₀ k) * ((F.metric t₀).edist p (q₀ k)).toReal) atTop (𝓝 1) := by
    simpa only [hnormCenter] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  obtain ⟨S, hS, hSr, σ, hσ, L₀, Φ, _, hcurv, hcharts, g, D, V,
    hVo, hzeroV, hVS, hnorm, hjets, hflat⟩ :=
    F.exists_distance_normalized_flat_annular_limit hC hcomplete hoperator hK hbound
      hκ hnoncollapse hn t₀ ht₀ p hzero Q₀ hQ₀ hQzero q₀ hcenter
  let G := fun k => F.ancientRescaleAt (Q₀ (σ k)) (hQ₀ (σ k)) t₀ ht₀
  have hcenterG (k : ℕ) : (((G k).metric 0).edist p (q₀ (σ k))).toReal = 1 := by
    rw [ancientRescaleAt_edist_toReal_zero]
    exact hnormCenter (σ k)
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp (hVo.mem_nhds hzeroV)
  let R : ℝ := min (δ / 2) (S / 2)
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hRS : R < S := (min_le_right _ _).trans_lt (by linarith)
  have hRV : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ V :=
    (closedBall_subset_ball ((min_le_left _ _).trans_lt (by linarith : δ / 2 < δ))).trans hδV
  have hcoeff : TendstoUniformlyOn (fun k => ((G k).metric 0).pullbackCoefficients (Φ k))
      g.euclideanCoefficients atTop (closedBall 0 R) := by
    have hh := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
        (hjets 0 (closedBall 0 R) (isCompact_closedBall _ _) hRV)
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using hh
  obtain ⟨τ, hτ, C, f, hLip, hpot, hf0, hfnonneg, _⟩ :=
    RiemannianMetric.exists_radial_square_limit_of_normal_chart_coefficients
      (fun k => (G k).metric 0) p (fun k => q₀ (σ k)) Φ hR hRS.le
      (fun k => (hcharts k).1) (fun k => (hcharts k).2.2.1)
      (fun k => (hcharts k).2.2.2.2.2.2)
      (by simpa only [hcenterG] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
      g.euclideanCoefficients
      (fun x _ => (g.contDiffAt_euclideanCoefficients x).continuousAt.continuousWithinAt) hcoeff
  let ι : ℕ → ℕ := fun k => σ (τ k)
  have hι : StrictMono ι := hσ.comp hτ
  refine ⟨fun k => q₀ (ι k), fun k => Q₀ (ι k), fun k => hQ₀ (ι k),
    hQzero.comp hι.tendsto_atTop, ?_, S, hS, hSr, fun k => L₀ (τ k), fun k => Φ (τ k),
    fun k => hcenterG (τ k), fun k => hcurv (τ k), fun k => hcharts (τ k),
    g, D, V, hVo, hzeroV, hVS, hnorm, ?_, hflat, R, hR, hRS, hRV,
    C, f, hLip, hpot, ?_, hfnonneg⟩
  · simpa only [Function.comp_def, hdist] using htend.comp hι.tendsto_atTop
  · intro m E hE hEV W hW
    exact hτ.tendsto_atTop.eventually (hjets m E hE hEV W hW)
  · simpa only [one_pow] using hf0

end PoincareConjecture.RicciFlow
