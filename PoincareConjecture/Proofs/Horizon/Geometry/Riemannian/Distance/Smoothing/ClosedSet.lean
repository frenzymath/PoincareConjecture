import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.DistanceToSet
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Quantitative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Compact

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_local_infDist_smoothing_with_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ v w : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y v w)
    (S : Set M) (hS : IsClosed S) (hSne : S.Nonempty)
    (x : M) (hx : x ∉ S) {η : ℝ} (hη : 0 < η) :
    letI := g.toMetricSpace
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ Sᶜ ∧
      ∀ ε : ℝ, 0 < ε → ∃ rho : M → ℝ,
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U ∧
        (∀ y ∈ U, |rho y - Metric.infDist y S| ≤ ε) ∧
        (∀ y ∈ U, g.tangentNorm y (D.gradient rho y) ≤ 1 + η) ∧
        ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
          D.hessian rho y v v ≤
            (4 / (3 * Metric.infDist x S) + K * Metric.infDist x S / 4 + η) *
              g.inner y v v := by
  let := g.toMetricSpace
  let d0 := Metric.infDist x S
  have hd0 : 0 < d0 := (hS.notMem_iff_infDist_pos hSne).mp hx
  let H0 := 4 / (3 * d0) + K * d0 / 4
  have hH0 : 0 ≤ H0 := by dsimp [H0]; positivity
  obtain ⟨t, ht, htquarter, hgradloss, hhessloss⟩ :=
    exists_distance_smoothing_parameter hH0 hη
  let A := 1 + t
  let H := H0 + t
  let C := H * A + A * t
  let L : ℝ≥0 := ⟨Real.sqrt A, Real.sqrt_nonneg A⟩
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hA0 : 0 ≤ A := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : 0 < 1 - t := by linarith
  obtain ⟨e, R0, hR0, hsource0, he0, he, hei, hcoeff⟩ :=
    g.exists_normalized_exponential_chart_bounds x ht
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source :=
    hsource0 (Metric.mem_ball_self hR0)
  let d : EuclideanSpace ℝ (Fin n) → ℝ := fun z => Metric.infDist (e z) S
  have hdcont : ContinuousAt d 0 :=
    (Metric.continuous_infDist_pt S).continuousAt.comp
      (he.contMDiffAt (e.open_source.mem_nhds hzero)).continuousAt
  have hdcenter : d 0 = d0 := by dsimp [d]; rw [he0]
  have hdpos : 0 < d 0 := hdcenter.symm ▸ hd0
  have hHcont : ContinuousAt (fun z => 4 / (3 * d z) + K * d z / 4) 0 :=
    (continuousAt_const.div (continuousAt_const.mul hdcont)
      (mul_ne_zero (by norm_num) hdpos.ne')).add
      ((continuousAt_const.mul hdcont).div_const 4)
  have hev : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      z ∈ Metric.ball 0 R0 ∧ 0 < d z ∧ 4 / (3 * d z) + K * d z / 4 ≤ H := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) hR0,
      continuousAt_const.eventually_lt hdcont hdpos,
      hHcont.eventually_lt continuousAt_const (show _ < H by
        rw [hdcenter]
        dsimp [H, H0]
        linarith)] with z hz hdz hHz
    exact ⟨hz, hdz, hHz.le⟩
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hsource : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R ⊆ e.source :=
    fun z hz => hsource0 (hball hz).1
  have hne (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 R) : e z ∉ S :=
    (hS.notMem_iff_infDist_pos hSne).mpr (hball hz).2.1
  have hmetric (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 R)
      (v : EuclideanSpace ℝ (Fin n)) :
      (1 - t) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients e z v v ∧
        g.pullbackCoefficients e z v v ≤ A * ‖v‖ ^ 2 :=
    (hcoeff z (hball hz).1).2.2 v
  have hconn (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 R) :
      ‖CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) z‖ ≤ t :=
    (hcoeff z (hball hz).1).2.1.le
  have hLip : LipschitzOnWith L d (Metric.ball 0 R) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro z hz w hw
    have hdist : dist (Metric.infDist (e z) S) (Metric.infDist (e w) S) ≤
        (g.edist (e z) (e w)).toReal := by
      change dist (Metric.infDist (e z) S) (Metric.infDist (e w) S) ≤ dist (e z) (e w)
      simpa only [NNReal.coe_one, one_mul] using
        (Metric.lipschitz_infDist_pt S).dist_le_mul (e z) (e w)
    apply hdist.trans
    exact g.toReal_edist_le_of_pullback_upper Metric.isOpen_ball (convex_ball 0 R)
      (he.mono hsource) hA0 (fun y hy v => (hmetric y hy v).2) hz hw
  have hconc : ConcaveOn ℝ (Metric.ball 0 R) (fun z => d z - C * ‖z‖ ^ 2 / 2) := by
    apply Poincare.Analysis.concaveOn_sub_norm_sq_of_hessian_upper_support (convex_ball 0 R)
    · exact (Metric.continuous_infDist_pt S).comp_continuousOn (he.continuousOn.mono hsource)
    · intro z hz
      obtain ⟨V, rho, hV, hzV, hrho, htouch, hmajor, hgrad, hhess⟩ :=
        g.exists_infDist_hessian_upper_support D hcomplete hK hsec S hS hSne (e z) (hne z hz)
      have hrhoz := hrho.contMDiffAt (hV.mem_nhds hzV)
      have hez := he.contMDiffAt (e.open_source.mem_nhds (hsource hz))
      refine ⟨rho ∘ e,
        (contMDiffAt_iff_contDiffAt.mp (hrhoz.comp z hez)).of_le (by norm_cast),
        htouch, ?_, ?_⟩
      · filter_upwards [hez.continuousAt.preimage_mem_nhds (hV.mem_nhds hzV)] with y hy
        exact hmajor (e y) hy
      · intro v
        apply D.fderiv2_parametrization_le_of_hessian_le e he hei (hsource hz)
          hrhoz hgrad hH hA ht.le (fun w => (hmetric z hz w).2) (hconn z hz)
        intro w
        apply (hhess w).trans
        apply mul_le_mul_of_nonneg_right (hball hz).2.2
        by_cases hw : w = 0
        · simp [hw]
        · exact (g.pos _ w hw).le
  let U := e.target ∩ e.symm ⁻¹' Metric.ball 0 (R / 2)
  have hU : IsOpen U := hei.continuousOn.isOpen_inter_preimage e.open_target Metric.isOpen_ball
  have hxU : x ∈ U := by
    refine ⟨he0 ▸ e.map_source hzero, ?_⟩
    change e.symm x ∈ Metric.ball 0 (R / 2)
    rw [← he0, e.left_inv hzero]
    exact Metric.mem_ball_self (half_pos hR)
  have hlarge (y : M) (hy : y ∈ U) : e.symm y ∈ Metric.ball 0 R :=
    Metric.ball_subset_ball (half_le_self hR.le) hy.2
  have hUS : U ⊆ Sᶜ := by
    intro y hy
    change y ∉ S
    simpa only [e.right_inv hy.1] using hne (e.symm y) (hlarge y hy)
  refine ⟨U, hU, hxU, hUS, ?_⟩
  intro ε hε
  obtain ⟨u, hu, hLu, herr, hsecond⟩ :=
    Poincare.exists_contDiff_hessian_approx_of_lipschitzOn_ball
      (half_lt_self hR) hLip hconc hε
  let rho := u ∘ e.symm
  have hrho : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U := by
    intro y hy
    exact ((contMDiffAt_iff_contDiffAt.mpr hu.contDiffAt).comp y
      (hei.contMDiffAt (e.open_target.mem_nhds hy.1))).contMDiffWithinAt
  have hbounds (y : M) (hy : y ∈ U) :
      g.tangentNorm y (D.gradient rho y) ≤ 1 + η ∧
      ∀ v : TangentSpace (𝓡 n) y,
        D.hessian rho y v v ≤ (H0 + η) * g.inner y v v := by
    let z := e.symm y
    have hz : z ∈ e.source := e.map_target hy.1
    have heq : (rho ∘ e) =ᶠ[𝓝 z] u := by
      filter_upwards [e.open_source.mem_nhds hz] with w hw
      exact congrArg u (e.left_inv hw)
    have hfirst : ‖fderiv ℝ (rho ∘ e) z‖ ≤ (L : ℝ) := by
      rw [heq.fderiv_eq]
      exact norm_fderiv_le_of_lipschitz ℝ hLu
    have hsecond' : ∀ v : EuclideanSpace ℝ (Fin n),
        fderiv ℝ (fderiv ℝ (rho ∘ e)) z v v ≤ C * ‖v‖ ^ 2 := by
      rw [heq.fderiv.fderiv_eq]
      exact hsecond z hy.2
    have hrhoz : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho (e z) := by
      rw [show e z = y from e.right_inv hy.1]
      exact hrho.contMDiffAt (hU.mem_nhds hy)
    have hconverted := D.intrinsic_bounds_of_parametrization e he hei hz hrhoz
      hb hC L.coe_nonneg ht.le (fun v => (hmetric z (hlarge y hy) v).1)
      hfirst hsecond' (hconn z (hlarge y hy))
    let P : M → Prop := fun q =>
      g.tangentNorm q (D.gradient rho q) ≤ 1 + η ∧
      ∀ v : TangentSpace (𝓡 n) q,
        D.hessian rho q v v ≤ (H0 + η) * g.inner q v v
    have hP : P (e z) := by
      refine ⟨hconverted.1.trans hgradloss, ?_⟩
      intro v
      apply (hconverted.2 v).trans
      apply mul_le_mul_of_nonneg_right hhessloss
      by_cases hv : v = 0
      · simp [hv]
      · exact (g.pos _ v hv).le
    exact (congrArg P (e.right_inv hy.1)).mp hP
  refine ⟨rho, hrho, ?_, fun y hy => (hbounds y hy).1, fun y hy => (hbounds y hy).2⟩
  intro y hy
  have heq : e (e.symm y) = y := e.right_inv hy.1
  have herr' := herr (e.symm y) (hlarge y hy)
  change |u (e.symm y) - Metric.infDist y S| ≤ ε
  simpa only [Real.dist_eq, d, heq] using herr'

theorem exists_infDist_smoothing_on_compact
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ v w : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y v w)
    (S : Set M) (hS : IsClosed S) (hSne : S.Nonempty)
    {T : Set M} (hT : IsCompact T) {r R : ℝ} (hr : 0 < r)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    letI := g.toMetricSpace
    (∀ x ∈ T, r ≤ Metric.infDist x S) →
    (∀ x ∈ T, Metric.infDist x S ≤ R) →
    ∃ rho : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho ∧
      (∀ x ∈ T, |rho x - Metric.infDist x S| ≤ ε) ∧
      (∀ x ∈ T, g.tangentNorm x (D.gradient rho x) ≤ 1 + η) ∧
      ∀ x ∈ T, ∀ v : TangentSpace (𝓡 n) x,
        D.hessian rho x v v ≤ (4 / (3 * r) + K * R / 4 + η) * g.inner x v v := by
  let := g.toMetricSpace
  intro hrT hRT
  have hhalf : 0 < η / 2 := half_pos hη
  have hlocal (x : M) (hx : x ∈ T) :
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ∀ e : ℝ, 0 < e → ∃ rho : M → ℝ,
          ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U ∧
          (∀ y ∈ U, |rho y - Metric.infDist y S| ≤ e) ∧
          (∀ y ∈ U, g.tangentNorm y (D.gradient rho y) ≤ 1 + η / 2) ∧
          ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
            D.hessian rho y v v ≤
              (4 / (3 * r) + K * R / 4 + η / 2) * g.inner y v v := by
    have hxS : x ∉ S := (hS.notMem_iff_infDist_pos hSne).mpr (hr.trans_le (hrT x hx))
    obtain ⟨U, hU, hxU, _, happrox⟩ :=
      g.exists_local_infDist_smoothing_with_bounds D hcomplete hK hsec S hS hSne x hxS hhalf
    refine ⟨U, hU, hxU, ?_⟩
    intro e he
    obtain ⟨rho, hrho, herr, hgrad, hhess⟩ := happrox e he
    refine ⟨rho, hrho, herr, hgrad, ?_⟩
    intro y hy v
    apply (hhess y hy v).trans
    have hinv : 4 / (3 * Metric.infDist x S) ≤ 4 / (3 * r) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left (hrT x hx) (by norm_num))
    have hcurv : K * Metric.infDist x S / 4 ≤ K * R / 4 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hRT x hx) hK) (by norm_num)
    apply mul_le_mul_of_nonneg_right (by linarith : _ ≤ _)
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos y v hv).le
  obtain ⟨rho, hrho, herr, hgrad, hhess⟩ :=
    D.exists_contMDiff_approx_on_compact_of_local hT (Metric.continuous_infDist_pt S).continuousOn
      (L := 1 + η / 2) (H := 4 / (3 * r) + K * R / 4 + η / 2)
      (by linarith) hlocal hε hhalf
  refine ⟨rho, hrho, herr, ?_, ?_⟩
  · intro x hx
    simpa only [show (1 + η / 2) + η / 2 = 1 + η by ring] using hgrad x hx
  · intro x hx v
    simpa only [show (4 / (3 * r) + K * R / 4 + η / 2) + η / 2 =
      4 / (3 * r) + K * R / 4 + η by ring] using hhess x hx v

end PoincareConjecture.RiemannianMetric
