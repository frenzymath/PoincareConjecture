import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Control
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Local
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.Ellipticity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FiniteOrder.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactGauss
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.FiniteDimensional

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem antitoneOn_metric_inner_self_on_ancient_of_ricci_nonneg
    (F : RicciFlow n M (Iic 0)) (x : M) (v : TangentSpace (𝓡 n) x)
    (hRic : ∀ t ≤ 0, 0 ≤ (F.connection t).ricci x v v) :
    AntitoneOn (fun t => (F.metric t).inner x v v) (Iic 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic 0)
    (fun t ht => (F.equation t ht x v v).continuousWithinAt)
    (f' := fun t => -2 * (F.connection t).ricci x v v)
  · intro t ht
    exact (F.equation t (interior_subset ht) x v v).mono interior_subset
  · intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (hRic t (show t ∈ Iic (0 : ℝ) from interior_subset ht))

theorem ball_subset_terminal_ball_of_ancient_ricci_nonneg
    (F : RicciFlow n M (Iic 0)) (p : M) (r : ℝ) {s : ℝ} (hs : s ≤ 0)
    (hRic : ∀ t ≤ 0, ∀ x ∈ (F.metric s).ball p r,
      ∀ v : TangentSpace (𝓡 n) x, 0 ≤ (F.connection t).ricci x v v) :
    (F.metric s).ball p r ⊆ (F.metric 0).ball p r := by
  simpa only [one_mul] using
    RiemannianMetric.ball_subset_ball_of_tangentNorm_le (F.metric s) (F.metric 0) p r
      1 zero_lt_one (by
        intro x hx v
        simpa only [one_mul, RiemannianMetric.tangentNorm] using Real.sqrt_le_sqrt
          (F.antitoneOn_metric_inner_self_on_ancient_of_ricci_nonneg x v
            (fun t ht => hRic t ht x hx v) hs (by simp) hs))

theorem exists_terminal_ball_curvatureDerivative_bound
    (hC : RicciFlowCurvatureTheory.{u}) (n k : ℕ) {K R : ℝ}
    (hK : 0 < K) (hR : 0 < R) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (F : RicciFlow n M (Iic 0)),
        (∀ t ≤ 0, MetricComplete (F.metric t)) →
        (∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x) →
        ∀ p : M,
        (∀ t ≤ 0, ∀ x ∈ (F.metric 0).ball p R,
          (F.connection t).curvatureTensorNorm x ≤ K) →
        ∀ x ∈ (F.metric 0).ball p (R / 4),
          (F.connection 0).curvatureDerivativeNorm k x ≤ D := by
  let L : ℝ := (n : ℝ) ^ 3 * K
  let δ : ℝ := min (1 / K) (Real.log 2 / (L + 1))
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδK : δ ≤ 1 / K := min_le_left _ _
  have hδL : L * δ ≤ Real.log 2 := by
    have hsmall : δ ≤ Real.log 2 / (L + 1) := min_le_right _ _
    have hm := (le_div_iff₀ (by linarith : 0 < L + 1)).mp hsmall
    nlinarith
  obtain ⟨C, hCpos, hShi⟩ := hC.local_derivative_estimates n k K 1 R hK (by norm_num) hR
  refine ⟨C / δ ^ ((k : ℝ) / 2), by positivity, ?_⟩
  intro M _ _ _ _ _ _ F hcomplete hoperator p hcurv
  have hRic (t : ℝ) (ht : t ≤ 0) (x : M) (v : TangentSpace (𝓡 n) x) :
      0 ≤ (F.connection t).ricci x v v :=
    ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus n M (F.metric t) (F.connection t)) x (hoperator t ht x) v).1
  have hshift : (fun t : ℝ => t + (-δ)) '' Icc 0 δ ⊆ Iic 0 := by
    rintro _ ⟨t, ht, rfl⟩
    change t + -δ ≤ 0
    linarith [ht.2]
  have hne : (Icc (0 : ℝ) δ).Nontrivial :=
    ⟨0, ⟨le_rfl, hδ.le⟩, δ, ⟨hδ.le, le_rfl⟩, hδ.ne'.symm⟩
  let Ft := F.translate (-δ) hshift ordConnected_Icc hne
  have hball : (F.metric (-δ)).ball p R ⊆ (F.metric 0).ball p R :=
    F.ball_subset_terminal_ball_of_ancient_ricci_nonneg p R (by linarith)
      (fun t ht x _ v => hRic t ht x v)
  have hcompact : IsCompact (closure ((Ft.metric 0).ball p R)) := by
    change IsCompact (closure ((F.metric (0 + -δ)).ball p R))
    rw [zero_add]
    let := (F.metric (-δ)).toMetricSpace
    let : ProperSpace M := (F.metric (-δ)).properSpace_toMetricSpace (hcomplete _ (by linarith))
    rw [← (F.metric (-δ)).toMetricSpace_ball]
    exact (isCompact_closedBall p R).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hcurv' : ∀ t ∈ Icc 0 δ, ∀ x ∈ (Ft.metric 0).ball p R,
      (Ft.connection t).curvatureTensorNorm x ≤ K := by
    intro t ht x hx
    have hx' : x ∈ (F.metric (-δ)).ball p R := by
      simpa only [Ft, translate, zero_add] using hx
    exact hcurv (t + -δ) (by linarith [ht.2]) x (hball hx')
  have hderiv := hShi M δ hδ hδK Ft p hcompact hcurv' δ ⟨hδ, le_rfl⟩
  intro x hx
  have hRicAbs : ∀ t ∈ Icc (-δ) 0, ∀ y ∈ (F.metric 0).ball p (R / 4),
      ∀ v : TangentSpace (𝓡 n) y,
        |(F.connection t).ricci y v v| ≤ L * (F.metric t).inner y v v := by
    intro t ht y hy v
    have hnorm := (F.connection t).abs_ricci_quadratic_le_curvatureTensorNorm y v
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) y) = n := finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at hnorm
    have hQ : 0 ≤ (F.metric t).inner y v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact ((F.metric t).pos y v hv).le
    apply hnorm.trans
    apply mul_le_mul_of_nonneg_right _ hQ
    exact mul_le_mul_of_nonneg_left
      (hcurv t ht.2 y (hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith)))) (by positivity)
  have hcontain := F.ball_subset_ball_of_ricci_bound (convex_Icc (-δ) 0)
    (fun _ ht => ht.2) p (R / 4) L
    (s := 0) (t := -δ) ⟨by linarith, le_rfl⟩ ⟨le_rfl, by linarith⟩ hRicAbs
  have hexp : Real.exp (L * δ) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hδL
  have hxinitial : x ∈ (Ft.metric 0).ball p (R / 2) := by
    change x ∈ (F.metric (0 + -δ)).ball p (R / 2)
    rw [zero_add]
    have h := hcontain hx
    rw [sub_zero, abs_neg, abs_of_pos hδ] at h
    exact h.trans_le (ENNReal.ofReal_le_ofReal (by nlinarith))
  have h := hderiv x hxinitial
  change (F.connection (δ + -δ)).curvatureDerivativeNorm k x ≤ _ at h
  rwa [add_neg_cancel] at h

theorem exists_terminal_exponential_metric_jet_bound
    (hC : RicciFlowCurvatureTheory.{u}) (n m : ℕ) {K S ρ : ℝ}
    (hK : 0 < K) (hS : 0 < S) (hρ : 0 < ρ) (hρS : ρ < S / 2) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (F : RicciFlow n M (Iic 0)),
        (∀ t ≤ 0, MetricComplete (F.metric t)) →
        (∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x) →
        ∀ p : M,
        (∀ t ≤ 0, ∀ x ∈ (F.metric 0).ball p (2 * S),
          (F.connection t).curvatureTensorNorm x ≤ K) →
        ∀ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        ∀ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
          Φ.source = Metric.ball 0 S → Φ 0 = p →
          (∀ v w, (F.metric 0).pullbackCoefficients (extChartAt (𝓡 n) p).symm
            (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w) →
          HasFDerivAt (fun w => extChartAt (𝓡 n) p (Φ w)) L.toContinuousLinearMap 0 →
          (∀ w ∈ Metric.ball 0 S,
            (F.metric 0).IsGeodesicOn (fun t => Φ (t • w))
              {t : ℝ | t • w ∈ Metric.ball 0 S}) →
          (∀ w ∈ Metric.ball 0 S,
            (F.metric 0).edist p (Φ w) = ENNReal.ofReal ‖w‖) →
          ∀ x ∈ Metric.closedBall 0 ρ,
            ‖iteratedFDeriv ℝ m ((F.metric 0).pullbackCoefficients Φ) x‖ ≤ B := by
  choose D hD hbound using fun k =>
    exists_terminal_ball_curvatureDerivative_bound hC n k hK (by positivity : 0 < 2 * S)
  obtain ⟨B, hB, hjet⟩ := CoordinateExponential.exists_uniform_pullback_metric_jet_bound
    n m hρ hρS D (fun k => (hD k).le)
  refine ⟨B, hB, ?_⟩
  intro M _ _ _ _ _ _ F hcomplete hoperator p hcurv L Φ hsource hzero hL hderiv hgeo hdist
  let g := F.metric 0
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (S / 2) ⊆ Metric.ball 0 S :=
    Metric.ball_subset_ball (by linarith)
  have heS : ContMDiffOn (𝓡 n) (𝓡 n) ∞ Φ (Metric.ball 0 S) := by
    simpa only [hsource] using Φ.contMDiffOn
  have he := heS.mono hsub
  have hnorm := g.pullbackCoefficients_zero_of_orthonormal p
    (heS.contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hS))) hzero hderiv hL
  have hgeo' : ∀ w ∈ Metric.ball 0 (S / 2),
      g.IsGeodesicOn (fun t => Φ (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 (S / 2)} := by
    intro w hw t ht
    exact hgeo w (hsub hw) t (hsub ht)
  apply hjet g (F.connection 0) Φ he
  · intro x hx
    exact ⟨(Φ.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞
      (hsource.symm ▸ hsub hx)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  · exact hnorm
  · exact CoordinateExponential.gauss_identity_of_radial_family g he hgeo'
      (fun v hv t ht =>
        g.tangentNorm_radial_of_normalized_exponential p L hzero hL hderiv hgeo' hv ht)
  · intro k _ x hx
    apply hbound k M F hcomplete hoperator p hcurv (Φ x)
    change g.edist p (Φ x) < ENNReal.ofReal (2 * S / 4)
    rw [hdist x (hsub hx), ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg x)]
    have hxnorm : ‖x‖ < S / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    linarith

theorem exists_terminal_exponential_coefficient_subsequence
    [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) {K S ρ : ℝ}
    (hK : 0 < K) (hS : 0 < S) (hρ : 0 < ρ) (hρS : ρ < S / 2)
    (F : ℕ → RicciFlow n M (Iic 0))
    (hcomplete : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hoperator : ∀ k t, t ≤ 0 → ∀ x,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (p : ℕ → M)
    (hcurv : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (2 * S),
      ((F k).connection t).curvatureTensorNorm x ≤ K)
    (L : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (hzero : ∀ k, Φ k 0 = p k)
    (hL : ∀ k v w, ((F k).metric 0).pullbackCoefficients
      (extChartAt (𝓡 n) (p k)).symm (extChartAt (𝓡 n) (p k) (p k))
        (L k v) (L k w) = inner ℝ v w)
    (hderiv : ∀ k, HasFDerivAt (fun w => extChartAt (𝓡 n) (p k) (Φ k w))
      (L k).toContinuousLinearMap 0)
    (hgeo : ∀ k w, w ∈ Metric.ball 0 S →
      ((F k).metric 0).IsGeodesicOn (fun t => Φ k (t • w))
        {t : ℝ | t • w ∈ Metric.ball 0 S})
    (hdist : ∀ k w, w ∈ Metric.ball 0 S →
      ((F k).metric 0).edist (p k) (Φ k w) = ENNReal.ofReal ‖w‖) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ B : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        ContDiffOn ℝ ∞ B (Metric.ball 0 ρ) ∧
        (∀ m C, IsCompact C → C ⊆ Metric.ball 0 ρ → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m
            (((F (σ k)).metric 0).pullbackCoefficients (Φ (σ k))))
          (iteratedFDeriv ℝ m B) atTop C) ∧
        (∀ v w, B 0 v w = inner ℝ v w) := by
  let f (k : ℕ) := ((F k).metric 0).pullbackCoefficients (Φ k)
  have he (k : ℕ) : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (Φ k) (Metric.ball 0 S) := by
    simpa only [hsource k] using (Φ k).contMDiffOn
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ρ ⊆ Metric.ball 0 S :=
    Metric.ball_subset_ball (by linarith)
  have hf (k : ℕ) : ContDiffOn ℝ ∞ (f k) (Metric.ball 0 ρ) := by
    intro x hx
    exact (((F k).metric 0).contDiffAt_pullbackCoefficients
      ((he k).contMDiffAt (Metric.isOpen_ball.mem_nhds (hsub hx)))).contDiffWithinAt
  have hbound : ∀ C : Set (EuclideanSpace ℝ (Fin n)), IsCompact C →
      C ⊆ Metric.ball 0 ρ → ∀ m : ℕ,
      ∃ B : ℝ, ∀ᶠ k in atTop, ∀ x ∈ C, ‖iteratedFDeriv ℝ m (f k) x‖ ≤ B := by
    intro C _ hCρ m
    obtain ⟨B, _, hB⟩ := exists_terminal_exponential_metric_jet_bound hC n m hK hS hρ hρS
    refine ⟨B, Filter.Eventually.of_forall ?_⟩
    intro k x hx
    exact hB M (F k) (hcomplete k) (hoperator k) (p k) (hcurv k) (L k) (Φ k)
      (hsource k) (hzero k) (hL k) (hderiv k) (hgeo k) (hdist k) x
      (Metric.ball_subset_closedBall (hCρ hx))
  obtain ⟨σ, hσ, B, hB, hjets⟩ :=
    Poincare.Analysis.Calculus.exists_common_smoothSubsequenceExtraction_finiteDimensional
      (E := fun _ : ℕ => EuclideanSpace ℝ (Fin n))
      (F := fun _ : ℕ =>
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (Ω := fun _ => Metric.ball 0 ρ) (fun _ => Metric.isOpen_ball)
      (fun _ k => f k) (fun _ => hf) (fun _ => hbound)
  refine ⟨σ, hσ, B 0, hB 0, hjets 0, ?_⟩
  have hzeroρ : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 ρ := Metric.mem_ball_self hρ
  have hconv : Tendsto (fun k => f (σ k) 0) atTop (𝓝 (B 0 0)) := by
    have hjet := hjets 0 0 {0} isCompact_singleton (singleton_subset_iff.mpr hzeroρ)
    have hvalue := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn hjet
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      hvalue.tendsto_at (mem_singleton 0)
  intro v w
  have hnorm (k : ℕ) : f k 0 v w = inner ℝ v w :=
    ((F k).metric 0).pullbackCoefficients_zero_of_orthonormal (p k)
      ((he k).contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hS)))
      (hzero k) (hderiv k) (hL k) v w
  have hvalue := ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto (B 0 0 v)).comp
    (((ContinuousLinearMap.apply ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) v).continuous.tendsto (B 0 0)).comp hconv)
  exact tendsto_nhds_unique hvalue
    (tendsto_const_nhds.congr (fun k => (hnorm (σ k)).symm))

end PoincareConjecture.RicciFlow
