import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.CoordinateSemiconcavity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Constants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Coordinates
import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.Convolution.DirectionalLocal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.ConstraintsCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Coordinates









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology NNReal

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace


theorem exists_local_distance_smoothing_with_directional_bounds_of_upper_supports
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ v w : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y v w)
    (p x : M) (hpx : p ≠ x)
    {ι : Type*} [Finite ι] (f : ι → M → ℝ) (B : ι → ℝ)
    {W : Set M} (hW : IsOpen W) (hxW : x ∈ W)
    (hf : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) W)
    (hsupport : ∀ y ∈ W, ∃ (V : Set M) (q : M → ℝ),
      IsOpen V ∧ y ∈ V ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q V ∧
      q y = (g.edist p y).toReal ∧
      (∀ z ∈ V, (g.edist p z).toReal ≤ q z) ∧
      g.inner y (D.gradient q y) (D.gradient q y) = 1 ∧
      ∀ i, |g.inner y (D.gradient q y) (D.gradient (f i) y)| ≤ B i)
    {η : ℝ} (hη : 0 < η) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ p ∉ U ∧ U ⊆ W ∧
      ∀ ε : ℝ, 0 < ε → ∃ rho : M → ℝ,
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U ∧
        (∀ y ∈ U, |rho y - (g.edist p y).toReal| ≤ ε) ∧
        (∀ y ∈ U, g.tangentNorm y (D.gradient rho y) ≤ 1 + η) ∧
        (∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
          D.hessian rho y v v ≤
            (4 / (3 * (g.edist p x).toReal) + K * (g.edist p x).toReal / 4 + η) *
              g.inner y v v) ∧
        ∀ i y, y ∈ U →
          |g.inner y (D.gradient rho y) (D.gradient (f i) y)| ≤ B i + η := by
  let d0 := (g.edist p x).toReal
  have hd0 : 0 < d0 := by
    have hpos : 0 < g.edist p x := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
      let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
      exact edist_pos.mpr hpx
    exact ENNReal.toReal_pos hpos.ne' (g.edist_ne_top p x)
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
  let w : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun i => mpullback (𝓡 n) (𝓡 n) e (D.gradient (f i))
  have hwcont (i : ι) : ContinuousAt (w i) 0 := by
    apply (D.contDiffAt_coordinateGradient e he hei hzero ?_).continuousAt
    rw [he0]
    exact (hf i).contMDiffAt (hW.mem_nhds hxW)
  have hosc0 : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      ∀ i, ‖w i z - w i 0‖ < η / (4 * A) := by
    apply Filter.eventually_all.mpr
    intro i
    apply ((hwcont i).sub continuousAt_const).norm.eventually_lt continuousAt_const
    simpa only [w, Pi.sub_apply, sub_self, norm_zero] using
      (div_pos hη (by positivity : 0 < 4 * A))
  have heW : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), e z ∈ W := by
    apply (he.contMDiffAt (e.open_source.mem_nhds hzero)).continuousAt.preimage_mem_nhds
    rw [he0]
    exact hW.mem_nhds hxW
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hpush (i : ι) (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ e.source) :
      mfderiv (𝓡 n) (𝓡 n) e z (w i z) = D.gradient (f i) (e z) :=
    (show (mfderiv (𝓡 n) (𝓡 n) e z).IsInvertible from
      ⟨hD.mfderiv hz, rfl⟩).self_apply_inverse _
  let d : EuclideanSpace ℝ (Fin n) → ℝ := fun z => (g.edist p (e z)).toReal
  have hdcont : ContinuousAt d 0 :=
    (g.continuous_toReal_edist p).continuousAt.comp
      (he.contMDiffAt (e.open_source.mem_nhds hzero)).continuousAt
  have hdcenter : d 0 = d0 := by dsimp [d]; rw [he0]
  have hdpos : 0 < d 0 := hdcenter.symm ▸ hd0
  have hHcont : ContinuousAt (fun z => 4 / (3 * d z) + K * d z / 4) 0 :=
    (continuousAt_const.div (continuousAt_const.mul hdcont)
      (mul_ne_zero (by norm_num) hdpos.ne')).add
      ((continuousAt_const.mul hdcont).div_const 4)
  have hev : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      z ∈ Metric.ball 0 R0 ∧ 0 < d z ∧ (4 / (3 * d z) + K * d z / 4 ≤ H) ∧
        e z ∈ W ∧ ∀ i, ‖w i z - w i 0‖ < η / (4 * A) := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) hR0,
      continuousAt_const.eventually_lt hdcont hdpos,
      hHcont.eventually_lt continuousAt_const (show _ < H by
        rw [hdcenter]
        dsimp [H, H0]
        linarith), heW, hosc0] with z hz hdz hHz hzW hzw
    exact ⟨hz, hdz, hHz.le, hzW, hzw⟩
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hsource : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R ⊆ e.source :=
    fun z hz => hsource0 (hball hz).1
  have hne (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 R) : e z ≠ p := by
    intro heq
    have h := (hball hz).2.1
    dsimp [d] at h
    rw [heq] at h
    simp only [edist, Manifold.riemannianEDist_self, ENNReal.toReal_zero,
      lt_self_iff_false] at h
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
    apply (g.abs_toReal_edist_sub_le p (e z) (e w)).trans
    exact g.toReal_edist_le_of_pullback_upper Metric.isOpen_ball (convex_ball 0 R)
      (he.mono hsource) hA0 (fun y hy v => (hmetric y hy v).2) hz hw
  have hconc : ConcaveOn ℝ (Metric.ball 0 R) (fun z => d z - C * ‖z‖ ^ 2 / 2) := by
    apply Poincare.Analysis.concaveOn_sub_norm_sq_of_hessian_upper_support (convex_ball 0 R)
    · exact (g.continuous_toReal_edist p).comp_continuousOn (he.continuousOn.mono hsource)
    · intro z hz
      obtain ⟨V, rho, hV, hzV, hrho, htouch, hmajor, hgrad, hhess⟩ :=
        g.exists_distance_hessian_upper_support D hcomplete hK hsec p (e z) (hne z hz).symm
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
        apply mul_le_mul_of_nonneg_right (hball hz).2.2.1
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
  have hpU : p ∉ U := by
    intro hp
    exact hne (e.symm p) (hlarge p hp) (e.right_inv hp.1)
  have hUW : U ⊆ W := by
    intro y hy
    have hh := (hball (hlarge y hy)).2.2.2.1
    simpa only [e.right_inv hy.1] using hh
  refine ⟨U, hU, hxU, hpU, hUW, ?_⟩
  intro ε hε
  have hvariation : ∀ i z, z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 2) →
      ∀ y ∈ Metric.ball 0 R, ‖w i z - w i y‖ ≤ η / (2 * A) := by
    intro i z hz y hy
    have hz' := (hball (Metric.ball_subset_ball (half_le_self hR.le) hz)).2.2.2.2 i
    have hy' := (hball hy).2.2.2.2 i
    have htri := norm_sub_le_norm_sub_add_norm_sub (w i z) (w i 0) (w i y)
    rw [norm_sub_rev (w i 0)] at htri
    have heq : η / (4 * A) + η / (4 * A) = η / (2 * A) := by
      field_simp
      ring
    linarith
  have hsupportE : ∀ i y, y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R →
      ∃ q : EuclideanSpace ℝ (Fin n) → ℝ,
        DifferentiableAt ℝ q y ∧ q y = d y ∧ (∀ᶠ z in 𝓝 y, d z ≤ q z) ∧
        ‖fderiv ℝ q y‖ ≤ A ∧ |fderiv ℝ q y (w i y)| ≤ B i := by
    intro i y hy
    obtain ⟨V, q, hV, hyV, hq, htouch, hmajor, hunit, hpair⟩ :=
      hsupport (e y) (hball hy).2.2.2.1
    have hqAt := hq.contMDiffAt (hV.mem_nhds hyV)
    have hgrad : g.tangentNorm (e y) (D.gradient q (e y)) ≤ (1 : ℝ) := by
      change Real.sqrt _ ≤ 1
      rw [hunit, Real.sqrt_one]
    have hbound : |mvfderiv (𝓡 n) q (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y (w i y))| ≤ B i := by
      rw [hpush i y (hsource hy), ← D.inner_gradient q]
      exact hpair i
    obtain ⟨hqE, htouchE, hmajorE, hnormE, hboundE⟩ :=
      D.directional_upper_support_in_parametrization e
        (he.contMDiffAt (e.open_source.mem_nhds (hsource hy))) hqAt htouch
        (Filter.eventually_of_mem (hV.mem_nhds hyV) hmajor)
        (by norm_num : (0 : ℝ) ≤ 1) hA hgrad
        (fun v => (hmetric y hy v).2) hbound
    exact ⟨q ∘ e, hqE, htouchE, hmajorE, by simpa only [one_mul] using hnormE, hboundE⟩
  obtain ⟨u, hu, hLu, herr, hsecond, hdir⟩ :=
    Poincare.exists_contDiff_hessian_directional_approx_of_field_upper_support
      (half_lt_self hR) hLip hconc w B hA0 hvariation hsupportE hε
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
  have hdirectional (i : ι) (y : M) (hy : y ∈ U) :
      |g.inner y (D.gradient rho y) (D.gradient (f i) y)| ≤ B i + η := by
    let z := e.symm y
    have hz : z ∈ e.source := e.map_target hy.1
    have heqU : (rho ∘ e) =ᶠ[𝓝 z] u := by
      filter_upwards [e.open_source.mem_nhds hz] with a ha
      exact congrArg u (e.left_inv ha)
    have hrhoz := hrho.contMDiffAt (hU.mem_nhds hy)
    have hrhoez : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho (e z) := by
      simpa only [z, e.right_inv hy.1] using hrhoz
    have heq := congrArg (fun T => T (w i z))
      (mfderiv_comp z (hrhoez.mdifferentiableAt (by simp))
        ((he.contMDiffAt (e.open_source.mem_nhds hz)).mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at heq
    change fderiv ℝ (rho ∘ e) z (w i z) =
      mvfderiv (𝓡 n) rho (e z) (mfderiv (𝓡 n) (𝓡 n) e z (w i z)) at heq
    rw [heqU.fderiv_eq, hpush i z hz, ← D.inner_gradient rho] at heq
    have hbnd := hdir i z hy.2
    have hApos : 0 < A := by linarith
    have hsmall : A * (η / (2 * A)) ≤ η := by
      have heqA : A * (η / (2 * A)) = η / 2 := by field_simp
      rw [heqA]
      linarith
    have hbnd' := hbnd.trans (add_le_add le_rfl hsmall)
    rw [heq] at hbnd'
    let P : M → Prop := fun y =>
      |g.inner y (D.gradient rho y) (D.gradient (f i) y)| ≤ B i + η
    exact (congrArg P (e.right_inv hy.1)).mp hbnd'
  refine ⟨rho, hrho, ?_, fun y hy => (hbounds y hy).1,
    fun y hy => (hbounds y hy).2, hdirectional⟩
  intro y hy
  have heq : e (e.symm y) = y := e.right_inv hy.1
  have herr' := herr (e.symm y) (hlarge y hy)
  change |u (e.symm y) - (g.edist p y).toReal| ≤ ε
  simpa only [Real.dist_eq, d, heq] using herr'

end PoincareConjecture.RiemannianMetric
