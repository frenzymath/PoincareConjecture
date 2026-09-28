import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.ConeEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.ChartCoverage

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_open_flat_radial_cone_model_along_ray_of_zero_ratio
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
    letI := (F.metric t₀).toMetricSpace
    let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
      (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoperator t₀ ht₀ x) v w
    let hcomparison := (F.metric t₀).rayComparison_of_metricComplete
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
    ∀ η : basedMinimizingRays p,
      ∃ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (D : LeviCivitaData g) (f : EuclideanSpace ℝ (Fin n) → ℝ)
        (r δ : ℝ), 0 < r ∧ r < 1 / 16 ∧ 0 < δ ∧ δ ≤ min r (1 / 4) ∧
        (∀ v w, g.inner 0 v w = inner ℝ v w) ∧ f 0 = 1 / 2 ∧
        (∀ x ∈ Metric.closedBall 0 (2 * r),
          0 < f x ∧ ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x ∧
            D.curvatureTensorNorm x = 0 ∧
            (∀ v w : EuclideanSpace ℝ (Fin n), D.hessian f x v w = g.inner x v w) ∧
            g.inner x (D.gradient f x) (D.gradient f x) = 2 * f x) ∧
        ∃ H : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (AsymptoticCone p hcomparison),
          H.source = g.ball 0 δ ∧
          H.target = Metric.ball (asymptoticConeRayProjection hcomparison (1, η)) δ ∧
          H 0 = asymptoticConeRayProjection hcomparison (1, η) ∧
          0 ∈ H.source ∧ H.source ⊆ Metric.closedBall 0 r ∧
          (∀ x ∈ H.source, f x = (asymptoticConeRadius hcomparison (H x) : ℝ) ^ 2 / 2) ∧
          (∀ x ∈ H.source, ∀ y ∈ H.source, dist (H x) (H y) = (g.edist x y).toReal) ∧
          (∀ x ∈ H.target, ∀ y ∈ H.target,
            (g.edist (H.symm x) (H.symm y)).toReal = dist x y) := by
  classical
  let := (F.metric t₀).toMetricSpace
  let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
    (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  let hcomparison := (F.metric t₀).rayComparison_of_metricComplete
    (F.connection t₀) (hcomplete t₀ ht₀) hsec p
  dsimp only
  intro η
  let q := fun k : ℕ => rayExtension η ((k : ℝ) + 1)
  let Q := fun k : ℕ => ((k : ℝ) + 1)⁻¹ ^ 2
  have hQ : ∀ k, 0 < Q k := fun k => by dsimp [Q]; positivity
  obtain ⟨S, hS, hSr, σ, hσ, L₀, Φ, hcenters, hcurv, hcharts,
    g, D, r, hr, h2rS, hnorm, hjets, hdist, C, f, hLip, hpotential, hf0, hmodel,
    τ, hτ, hL, hsource, U, hU, ψ, e, hrelated, hdistortion, he, hlim, hcover⟩ :=
    F.exists_flat_radial_cone_embedding_along_ray_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse hn t₀ ht₀ p hzero η
  let A := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r
  let metricA : MetricSpace A := MetricSpace.induced Subtype.val Subtype.val_injective g.toMetricSpace
  let : PseudoEMetricSpace A :=
    @PseudoMetricSpace.toPseudoEMetricSpace A metricA.toPseudoMetricSpace
  let o : A := ⟨0, Metric.mem_closedBall_self hr.le⟩
  let gk := fun k => (F.ancientRescaleAt (Q (σ (τ k))) (hQ (σ (τ k))) t₀ ht₀).metric 0
  let L := fun k => 1 / Real.sqrt (Q (σ (τ k)))
  let ε := fun k : ℕ => 1 / ((k : ℝ) + 1)
  have hε : Tendsto ε (U : Filter ℕ) (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto ε atTop (𝓝 0)).mono_left hU
  have hτerror : Tendsto (fun k => ε k / 4) (U : Filter ℕ) (𝓝 0) := by
    simpa only [zero_div] using hε.div_const 4
  have hLformula (k : ℕ) : L k = (σ (τ k) : ℝ) + 1 := by
    dsimp only [L, Q]
    rw [Real.sqrt_sq (by positivity : 0 ≤ ((σ (τ k) : ℝ) + 1)⁻¹), one_div, inv_inv]
  have hscale (k : ℕ) (x y : M) :
      ((gk k).edist x y).toReal = ((F.metric t₀).edist x y).toReal / L k := by
    rw [ancientRescaleAt_edist_toReal_zero]
    dsimp only [L]
    rw [div_div_eq_mul_div, div_one, mul_comm]
  have hcenterlim : Tendsto (fun k => ((gk k).edist p (q (σ (τ k)))).toReal)
      (U : Filter ℕ) (𝓝 1) := by
    have hconst : (fun k => ((gk k).edist p (q (σ (τ k)))).toReal) = fun _ => 1 := by
      funext k
      exact hcenters (τ k)
    rw [hconst]
    exact tendsto_const_nhds
  obtain ⟨δ, hδ, hδr, hδA, H, hHsource, hHtarget, hHcenter, hHe, hHdist, hHinv⟩ :=
    (F.metric t₀).exists_open_cone_chart_of_normal_chart_limit gk g p
      (fun k => q (σ (τ k))) (fun k => Φ (τ k)) hr (by linarith : r < S)
      (fun k => (hcharts (τ k)).1) (fun k => (hcharts (τ k)).2.1)
      (fun k => (hcharts (τ k)).2.2.1) (fun k => (hcharts (τ k)).2.2.2.2.2.2)
      L hL hscale hcomparison ψ e ε (fun k => ε k / 4)
      (fun k => by dsimp [ε]; positivity) hε hsource hrelated
      (fun k x y z w hxz hyw =>
        (hdistortion k x y x.property y.property z w hxz hyw).le)
      he hlim hcenterlim
  have heo : (e o : AsymptoticCone p hcomparison) =
      asymptoticConeRayProjection hcomparison (1, η) := by
    have hpoint : Tendsto (fun k => (ψ k o : AsymptoticCone p hcomparison))
        (U : Filter ℕ) (𝓝 (e o : AsymptoticCone p hcomparison)) :=
      (continuous_subtype_val.tendsto _).comp (hlim.tendsto_at o)
    apply tendsto_nhds_unique hpoint
    apply tendsto_unit_cone_of_annulusConeRelation_ray hcomparison η
      (Eventually.of_forall hL) hτerror
    apply Eventually.of_forall
    intro k
    change annulusConeRelation hcomparison (L k) (ε k / 4)
      (rayExtension η (L k)) (ψ k o)
    have hchartonray : Φ (τ k) 0 = rayExtension η (L k) := by
      rw [(hcharts (τ k)).2.2.1, hLformula]
    rw [← hchartonray]
    exact hrelated k o
  have hpotentialE (x : A) :
      (asymptoticConeRadius hcomparison (e x) : ℝ) ^ 2 / 2 = f x := by
    apply cone_radial_potential_eq_of_annulusConeRelation hcomparison
      (Eventually.of_forall hL) (Eventually.of_forall (fun k => hrelated k x))
      ((continuous_subtype_val.tendsto _).comp (hlim.tendsto_at x))
    have hx : (x : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall 0 (2 * r) :=
      Metric.closedBall_subset_closedBall (by linarith : r ≤ 2 * r) x.property
    have hpot := ((hpotential.tendsto_at hx).comp hτ).mono_left hU
    change Tendsto (fun k => ((gk k).edist p (Φ (τ k) x)).toReal ^ 2 / 2)
      (U : Filter ℕ) (𝓝 (f x)) at hpot
    simp_rw [hscale] at hpot
    exact hpot
  refine ⟨g, D, f, r, δ, hr, by linarith, hδ, hδr, hnorm, hf0, hmodel,
    H, hHsource, ?_, ?_, ?_, ?_, ?_, hHdist, hHinv⟩
  · exact hHtarget.trans (congrArg (fun z => Metric.ball z δ) heo)
  · exact hHcenter.trans heo
  · rw [hHsource, ← g.toMetricSpace_ball]
    exact @Metric.mem_ball_self _ g.toMetricSpace.toPseudoMetricSpace 0 δ hδ
  · simpa only [hHsource] using hδA
  · intro x hx
    have hxball : x ∈ g.ball 0 δ := hHsource ▸ hx
    rw [hHe x hxball]
    exact (hpotentialE ⟨x, hδA hxball⟩).symm

end PoincareConjecture.RicciFlow
