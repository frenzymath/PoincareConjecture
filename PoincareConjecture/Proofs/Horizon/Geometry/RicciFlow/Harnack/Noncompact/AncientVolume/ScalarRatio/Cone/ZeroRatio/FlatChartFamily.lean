import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.ChartFamily
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.PullbackExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.RadialGauss

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_common_flat_annular_metrics_of_zero_ratio
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
      ∃ (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (D : ∀ j, LeviCivitaData (g j)) (r : ℝ),
        0 < r ∧ 2 * r < S / 4 ∧
        (∀ k j, ∀ x ∈ Metric.closedBall 0 (2 * r), ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ((G k).metric 0).pullbackCoefficients (Φ k j) x v v ∧
          ((G k).metric 0).pullbackCoefficients (Φ k j) x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) ∧
        (∀ j v w, (g j).inner 0 v w = inner ℝ v w) ∧
        (∀ j (x v : EuclideanSpace ℝ (Fin n)), ‖v‖ / 2 ≤ (g j).tangentNorm x v ∧
          (g j).tangentNorm x v ≤ 3 * ‖v‖ / 2) ∧
        (∀ j x v, (g j).inner x x v = inner ℝ x v) ∧
        (∀ j x, 2 * r ≤ ‖x‖ → (g j).euclideanCoefficients x = innerSL ℝ) ∧
        (∀ j m C, IsCompact C → C ⊆ Metric.closedBall 0 r → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k j)))
          (iteratedFDeriv ℝ m (g j).euclideanCoefficients) atTop C) ∧
        ∀ j x, x ∈ Metric.closedBall 0 r → (D j).curvatureTensorNorm x = 0 := by
  obtain ⟨S, hS, hSr, σ, hσ, L₀, Φ, hcurv, hcharts, B, hB, hjets, hnorm,
    r, hr, hrS, hsourcebound, hlimitbound⟩ :=
      F.exists_common_annular_chart_coefficients_of_zero_ratio hC hcomplete hoperator hK hbound
        hκ hnoncollapse hn t₀ ht₀ p hzero Q hQ hQzero q hcenter
  let G := fun k => F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * r) ⊆
      Metric.ball 0 (S / 4) := Metric.ball_subset_ball hrS.le
  have hsubS : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (S / 4) ⊆
      Metric.ball 0 S := Metric.ball_subset_ball (by linarith)
  have hclosed : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆
      Metric.ball 0 (S / 4) := Metric.closedBall_subset_ball (by linarith)
  have hconv (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 (S / 4)) :
      Tendsto (fun k => ((G k).metric 0).pullbackCoefficients (Φ k j) x) atTop (𝓝 (B j x)) := by
    have hjet := hjets j 0 {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    have hvalue := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn hjet
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using hvalue.tendsto_at (mem_singleton x)
  have heval (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 (S / 4))
      (v w : EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun k => ((G k).metric 0).pullbackCoefficients (Φ k j) x v w) atTop
        (𝓝 (B j x v w)) :=
    ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto (B j x v)).comp
      (((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) v).continuous.tendsto
        (B j x)).comp (hconv j x hx))
  have hsymm (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 (S / 4))
      (v w : EuclideanSpace ℝ (Fin n)) : B j x v w = B j x w v :=
    tendsto_nhds_unique (heval j x hx v w)
      ((heval j x hx w v).congr (fun k => ((G k).metric 0).symm (Φ k j x) _ _))
  have hgaussSource (k j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 S)
      (v : EuclideanSpace ℝ (Fin n)) :
      ((G k).metric 0).pullbackCoefficients (Φ k j) x x v = inner ℝ x v := by
    obtain ⟨hsource, _, hzeroΦ, horth, hderiv, hgeo, _⟩ := hcharts k j
    have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (Φ k j) (Metric.ball 0 S) := by
      simpa only [hsource] using (Φ k j).contMDiffOn
    have hnormalized := ((G k).metric 0).pullbackCoefficients_zero_of_orthonormal (q j (σ k))
      (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hS)))
      hzeroΦ hderiv horth
    exact ((G k).metric 0).radial_gauss_identity ((G k).connection 0) he hnormalized hgeo x hx v
  have hgauss (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 (S / 4))
      (v : EuclideanSpace ℝ (Fin n)) : B j x x v = inner ℝ x v :=
    tendsto_nhds_unique (heval j x hx x v)
      (tendsto_const_nhds.congr (fun k => (hgaussSource k j x (hsubS hx) v).symm))
  have hextend (j : ℕ) : ∃ g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)),
      (∀ x ∈ Metric.closedBall 0 r, g.euclideanCoefficients =ᶠ[𝓝 x] B j) ∧
      (∀ x v : EuclideanSpace ℝ (Fin n),
        ‖v‖ / 2 ≤ g.tangentNorm x v ∧ g.tangentNorm x v ≤ 3 * ‖v‖ / 2) ∧
      (∀ x v, g.inner x x v = inner ℝ x v) ∧
      ∀ x, 2 * r ≤ ‖x‖ → g.euclideanCoefficients x = innerSL ℝ := by
    apply RiemannianMetric.exists_uniform_extension_of_quadratic_bounds hr (by linarith) (B j)
      ((hB j).mono hsub) (fun x hx => hsymm j x (hsub hx))
    · intro x hx v
      have hb := hlimitbound j x (Metric.ball_subset_closedBall hx) v
      constructor <;> linarith [hb.1, hb.2]
    · intro x hx
      exact hgauss j x (hsub hx)
  choose g hagree hgnorm hggauss hgoutside using hextend
  let D := fun j => (g j).euclideanLeviCivitaData
  have hgjets (j m : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (hCcompact : IsCompact C)
      (hCball : C ⊆ Metric.closedBall 0 r) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k j)))
      (iteratedFDeriv ℝ m (g j).euclideanCoefficients) atTop C := by
    apply (hjets j m C hCcompact (hCball.trans hclosed)).congr_right
    intro x hx
    exact ((hagree j x (hCball hx)).iteratedFDeriv ℝ m).self_of_nhds.symm
  refine ⟨S, hS, hSr, σ, hσ, L₀, Φ, hcurv, hcharts, g, D, r, hr, hrS,
    hsourcebound, ?_, hgnorm, hggauss, hgoutside, hgjets, ?_⟩
  · intro j v w
    have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall 0 r := Metric.mem_closedBall_self hr.le
    exact (congrArg (fun A => A v w) (hagree j 0 h0).self_of_nhds).trans (hnorm j v w)
  · intro j x hx
    have hxS := hsubS (hclosed hx)
    have hlimit := (D j).tendsto_curvatureTensorNorm_of_partialDiffeomorph_metric_jets
      (fun k => (G k).metric 0) (fun k => (G k).connection 0) (fun k => Φ k j) x
      (fun k => by rw [(hcharts k j).1]; exact hxS)
      (fun m _ => (hgjets j m {x} isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at
        (mem_singleton x))
    have hvanish : Tendsto (fun k => ((G k).connection 0).curvatureTensorNorm (Φ k j x))
        atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have hsmall := (F.eventually_ancientRescaleAt_annular_curvature_lt_of_zero_ratio
        hC hcomplete hoperator hK hbound t₀ ht₀ p hzero Q hQ hQzero
        (by norm_num : (0 : ℝ) < 1 / 2) hε).filter_mono hσ.tendsto_atTop
      filter_upwards [hsmall] with k hk
      have hball : Φ k j x ∈ ((G k).metric 0).ball (q j (σ k)) (2 * S) := by
        have hm := (Φ k j).map_source (by rw [(hcharts k j).1]; exact hxS)
        rw [(hcharts k j).2.1] at hm
        exact (fun y (hy : ((G k).metric 0).edist (q j (σ k)) y < ENNReal.ofReal S) =>
          hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith : S ≤ 2 * S))) _ hm
      have hmargin : 1 / 2 + 2 * S ≤ (((G k).metric 0).edist p (q j (σ k))).toReal := by
        have hh := hcenter j (σ k)
        change 3 / 4 ≤ (((G k).metric 0).edist p (q j (σ k))).toReal at hh
        linarith
      have houter := ((G k).metric 0).radial_lower_bound_on_ball p (q j (σ k))
        hmargin (Φ k j x) hball
      have hb := hk 0 le_rfl (Φ k j x) houter.le
      simpa only [Real.dist_eq, sub_zero,
        abs_of_nonneg (show 0 ≤ ((G k).connection 0).curvatureTensorNorm (Φ k j x) from
          Real.sqrt_nonneg _)] using hb
    exact tendsto_nhds_unique hlimit hvanish

end PoincareConjecture.RicciFlow
