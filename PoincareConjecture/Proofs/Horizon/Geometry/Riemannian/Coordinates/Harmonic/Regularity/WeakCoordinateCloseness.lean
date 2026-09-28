import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.RadialFrame
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.RadialFrameComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.CorrectionEstimate
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Classical
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.FrameEnergy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.LocalGradientDifference
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.RepresentativeEnergy

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1200000

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology Bundle BigOperators

namespace PoincareConjecture.HarmonicCoordinates

open LeviCivitaData.Dirichlet

private theorem weakCoordinate_inner_nonneg {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x v : EuclideanSpace ℝ (Fin n)) : 0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

private theorem differential_sub_linear_sq_le {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : DifferentiableAt ℝ f x) (ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (X : EuclideanSpace ℝ (Fin n)) {b δ : ℝ} (hb : 0 ≤ b)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ b * ‖v‖ ^ 2)
    (hreference : g.tangentNorm x
      ((show EuclideanSpace ℝ (Fin n) from D.gradient ℓ x) - X) ≤ δ) :
    ‖fderiv ℝ f x - ℓ‖ ^ 2 ≤ 2 * b *
      (g.inner x ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X)
        ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X) + δ ^ 2) := by
  let u : EuclideanSpace ℝ (Fin n) := (show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X
  let v : EuclideanSpace ℝ (Fin n) := (show EuclideanSpace ℝ (Fin n) from D.gradient ℓ x) - X
  have hgrad : D.gradient (fun y => f y - ℓ y) x =
      D.gradient f x - D.gradient ℓ x := by
    apply (g.inner_isInvertible x).injective
    ext w
    rw [D.inner_gradient, mvfderiv_fun_sub hf.mdifferentiableAt ℓ.mdifferentiableAt]
    simp only [map_sub, sub_apply, D.inner_gradient]
  have hv : g.inner x v v ≤ δ ^ 2 := by
    have hnn : 0 ≤ g.tangentNorm x v := Real.sqrt_nonneg _
    have h := (sq_le_sq₀ hnn (hnn.trans hreference)).mpr hreference
    simpa only [RiemannianMetric.tangentNorm,
      Real.sq_sqrt (weakCoordinate_inner_nonneg g x v)] using h
  have hsub : g.inner x (u - v) (u - v) ≤
      2 * g.inner x u u + 2 * g.inner x v v := by
    have h := weakCoordinate_inner_nonneg g x (u + v)
    simp only [map_add, add_apply] at h
    simp only [map_sub, sub_apply]
    rw [g.symm x v u] at h ⊢
    linarith
  have h := fderiv_sq_le_gradient_energy D (fun y => f y - ℓ y) x hb hupper
  have hdf : fderiv ℝ (fun y => f y - ℓ y) x = fderiv ℝ f x - ℓ :=
    (hf.hasFDerivAt.sub ℓ.hasFDerivAt).fderiv
  rw [hdf, hgrad] at h
  have heq : D.gradient f x - D.gradient ℓ x =
      (show TangentSpace (𝓡 n) x from u - v) := by
    change (show EuclideanSpace ℝ (Fin n) from D.gradient f x) -
        (show EuclideanSpace ℝ (Fin n) from D.gradient ℓ x) =
      ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X) -
        ((show EuclideanSpace ℝ (Fin n) from D.gradient ℓ x) - X)
    abel
  rw [heq] at h
  change ‖fderiv ℝ f x - ℓ‖ ^ 2 ≤ 2 * b * (g.inner x u u + δ ^ 2)
  exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_left hsub hb,
    mul_le_mul_of_nonneg_left hv hb])

theorem exists_uniform_weakHarmonicCoordinate_differential_close
    {n : ℕ} (hn : 2 ≤ n) {R K τ : ℝ} (hR : 0 < R) (hK : 0 ≤ K) (hτ : 0 < τ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ 4 * r < R ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) →
        (∀ x w, g.euclideanCoefficients x x w = inner ℝ x w) →
        (∀ x ∈ Metric.ball 0 R, D.curvatureTensorNorm x ≤ K) →
        ∀ i : Fin n, ∃ w : H1Zero D (Metric.ball 0 (2 * r)),
          (∀ φ : EnergyTest D (Metric.ball 0 (2 * r)),
            (∫ x, (x i + (toL2 D (Metric.ball 0 (2 * r)) w) x) *
              D.laplacian φ x ∂g.volumeMeasure) = 0) ∧
          ∀ U : EuclideanSpace ℝ (Fin n) → ℝ,
            ContDiffOn ℝ ∞ U (Metric.ball 0 (2 * r)) →
            (U =ᵐ[g.volumeMeasure.restrict (Metric.ball 0 (2 * r))]
              fun x => x i + (toL2 D (Metric.ball 0 (2 * r)) w) x) →
            ∀ z ∈ Metric.ball 0 (r / 2),
              ‖fderiv ℝ U z - EuclideanSpace.proj (𝕜 := ℝ) i‖ ≤ τ := by
  let : NeZero n := ⟨by omega⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  let a : ℝ := 1 / 4
  let b : ℝ := 9 / 4
  have ha : 0 < a := by norm_num [a]
  have hb : 0 < b := by norm_num [b]
  obtain ⟨C, hC, hmean⟩ := exists_uniform_local_gradient_difference_mean_value hn ha hb.le hK
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  let V₀ := (2 : ℝ) ^ n * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  let d := b / Real.sqrt (a ^ n)
  let P₀ := Real.sqrt (b ^ n) * d
  let W₀ := (P₀ + 1) * d * V₀
  let t := 5 * (K + 1)
  let σ := 10 * ((n : ℝ) + 1) * (K + 1)
  let A := 2 * b * C * 8 * (n : ℝ) * d * W₀
  let B := 2 * b * (C * V₀ * (2 * t ^ 2 + σ ^ 2) + t ^ 2)
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hV₀ : 0 ≤ V₀ := by dsimp only [V₀]; positivity
  have hP₀ : 0 ≤ P₀ := by dsimp only [P₀]; positivity
  have hW₀ : 0 ≤ W₀ := by dsimp only [W₀]; positivity
  have ht : 0 < t := by dsimp only [t]; positivity
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hepsNear : ∀ᶠ e : ℝ in 𝓝 0, A * e ^ 2 < τ ^ 2 / 4 := by
    have hc : Continuous (fun e : ℝ => A * e ^ 2) := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by simp; positivity)
  obtain ⟨e₀, he₀, heBound⟩ := Metric.eventually_nhds_iff.mp hepsNear
  let ε := e₀ / 2
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεsmall : A * ε ^ 2 ≤ τ ^ 2 / 4 := (heBound (y := ε) (by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using
      (show ε < e₀ by dsimp only [ε]; linarith))).le
  obtain ⟨δ, hδ, htolerance⟩ :=
    exists_divergence_coefficient_tolerance_of_quadratic (n := n) hε
  let θ := min 1 (δ / 3)
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hθone : θ ≤ 1 := min_le_left _ _
  have hθδ : θ * (2 + θ) ≤ δ := by
    have hθδ' := min_le_right (1 : ℝ) (δ / 3)
    change θ ≤ δ / 3 at hθδ'
    nlinarith [mul_nonneg hθ.le (sub_nonneg.mpr hθone)]
  have hnear : ∀ᶠ u : ℝ in 𝓝 0,
      36 * K * u ^ 2 < θ ∧ B * u ^ 4 < τ ^ 2 / 4 := by
    have hc : Continuous (fun u : ℝ => 36 * K * u ^ 2) := by fun_prop
    have hd' : Continuous (fun u : ℝ => B * u ^ 4) := by fun_prop
    exact (hc.continuousAt.eventually_lt continuousAt_const (by simpa using hθ)).and
      (hd'.continuousAt.eventually_lt continuousAt_const (by simp; positivity))
  obtain ⟨r₀, hr₀, hrBound⟩ := Metric.eventually_nhds_iff.mp hnear
  let r := min (R / 8) (min (1 / 4) (r₀ / 2))
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrR : r ≤ R / 8 := min_le_left _ _
  have hrquarter : r ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₀ : r < r₀ := lt_of_le_of_lt
    ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  obtain ⟨hrθ, hrsmall⟩ := hrBound (y := r) (by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using hrr₀)
  have hr4R : 4 * r < R := by linarith
  have hr1 : r ≤ 1 := by linarith
  refine ⟨r, hr, hrquarter, hr4R, fun g D hell hgauss hcurv i => ?_⟩
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (4 * r) ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball hr4R.le
  have hsubr : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  have hmetric (x) (hx : x ∈ Metric.ball 0 R) (v : EuclideanSpace ℝ (Fin n)) :
      g.tangentNorm x v ≤ (3 / 2 : ℝ) * ‖v‖ := by
    have h := Real.sqrt_le_sqrt (hell x hx v).2
    change Real.sqrt (g.inner x v v) ≤ Real.sqrt ((9 / 4 : ℝ) * ‖v‖ ^ 2) at h
    simpa only [RiemannianMetric.tangentNorm, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9 / 4),
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 9), Real.sqrt_sq (norm_nonneg v),
      show Real.sqrt (9 : ℝ) = 3 by norm_num,
      show Real.sqrt (4 : ℝ) = 2 by norm_num] using h
  obtain ⟨T, hT, -, hTinv, hTiso, hTconn, hTcoframe⟩ :=
    exists_radial_frame_of_gauss D hgauss hK (by norm_num : (0 : ℝ) ≤ 3 / 2)
      hcurv hmetric
  have hcoframe (x) (hx : x ∈ Metric.ball 0 (4 * r))
      (v : EuclideanSpace ℝ (Fin n)) : ‖(T x).inverse v - v‖ ≤ θ * ‖v‖ := by
    have hxnorm : ‖x‖ ≤ 4 * r := le_of_lt (by
      simpa only [Metric.mem_ball, dist_zero_right] using hx)
    calc
      _ ≤ K * (3 / 2 : ℝ) ^ 2 * ‖x‖ ^ 2 * ‖v‖ := hTcoframe x (hsub hx) v
      _ ≤ K * (3 / 2 : ℝ) ^ 2 * (4 * r) ^ 2 * ‖v‖ := by gcongr
      _ = (36 * K * r ^ 2) * ‖v‖ := by ring
      _ ≤ θ * ‖v‖ := mul_le_mul_of_nonneg_right hrθ.le (norm_nonneg v)
  have hclose (x) (hx : x ∈ Metric.ball 0 (4 * r)) :
      ‖euclideanDivergenceOperator g x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ ε := by
    apply (htolerance g x ?_).le
    intro v
    exact (inner_self_sub_norm_sq_le_of_frame_inverse x (hTinv x) (hTiso x)
      hθ.le (hcoframe x hx) v).trans
      (mul_le_mul_of_nonneg_right hθδ (sq_nonneg _))
  have hconstruct := exists_weakHarmonicCoordinate_small_energy D
    (show 0 < 4 * r by positivity) ha hb hε.le (fun x hx => hell x (hsub hx)) hclose i
  rw [show 4 * r / 2 = 2 * r by ring] at hconstruct
  obtain ⟨w, hweak, -, hwnorm⟩ := hconstruct
  have hvol : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * r)) = V₀ * r ^ n := by
    rw [Measure.real_def, Measure.addHaar_ball_of_pos volume _ (by positivity : 0 < 2 * r),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    simp only [finrank_euclideanSpace_fin, mul_pow, V₀, Measure.real_def]
    ring
  have hw : ‖w‖ ^ 2 ≤ W₀ * ε ^ 2 * r ^ n := by
    calc
      _ ≤ (Real.sqrt (b ^ n) * (4 * r) ^ 2 * b / Real.sqrt (a ^ n) + 1) *
          ((b / Real.sqrt (a ^ n)) * ε ^ 2 *
            volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * r))) := hwnorm
      _ ≤ (P₀ + 1) * (d * ε ^ 2 *
          volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * r))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hrad : (4 * r) ^ 2 ≤ 1 := by nlinarith only [hr, hrquarter]
        have h := mul_le_mul_of_nonneg_left hrad hP₀
        convert add_le_add_right h 1 using 1 <;> dsimp only [P₀, d] <;> ring
      _ = W₀ * ε ^ 2 * r ^ n := by rw [hvol]; dsimp only [W₀]; ring
  refine ⟨w, hweak, fun U hUs hU z hz => ?_⟩
  have hΩR : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * r) ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  have hharm : ∀ x ∈ Metric.ball 0 (2 * r), D.laplacian U x = 0 := by
    apply laplacian_eq_zero_of_smooth_distributional Metric.isOpen_ball
      (contMDiffOn_iff_contDiffOn.mpr hUs)
    intro φ
    have heq := integral_mul_eq_of_ae_eq_on Metric.isOpen_ball hU
      ((D.tsupport_laplacian_subset φ).trans φ.support_subset)
    calc
      _ = ∫ x, (x i + (toL2 D (Metric.ball 0 (2 * r)) w) x) *
          D.laplacian φ x ∂g.volumeMeasure := by simpa only [mul_comm] using heq
      _ = 0 := hweak φ
  let S := Metric.closedBall z (r / 2)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hSr : S ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    intro x hx
    have hdist := dist_triangle x z 0
    have hx' := Metric.mem_closedBall.mp hx
    have hz' := Metric.mem_ball.mp hz
    apply Metric.mem_ball.mpr
    linarith
  have hrΩ : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ Metric.ball 0 (2 * r) :=
    Metric.ball_subset_ball (by linarith)
  have hSΩ := hSr.trans hrΩ
  have hclosed : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ Metric.ball 0 (2 * r) :=
    Metric.closedBall_subset_ball (by linarith)
  have hmassvol : volume.real S ≤ V₀ * r ^ n := by
    rw [← hvol]
    exact measureReal_mono hSΩ measure_ball_lt_top.ne
  let q := EuclideanSpace.proj (𝕜 := ℝ) i
  have hcorr : (fun x => U x - q x) =ᵐ[g.volumeMeasure.restrict (Metric.ball 0 (2 * r))]
      (toL2 D (Metric.ball 0 (2 * r)) w : EuclideanSpace ℝ (Fin n) → ℝ) := by
    filter_upwards [hU] with x hx
    simp only [q, EuclideanSpace.coe_proj, hx, add_sub_cancel_left]
  have henergy := integral_fderiv_sq_le_of_smooth_representative ha hb.le D hell
    Metric.isOpen_ball hΩR (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * r))
    Metric.ball_subset_closedBall hS hSΩ w (hUs.sub q.contDiff.contDiffOn) hcorr
  have henergy' : (∫ x in S, ‖fderiv ℝ (fun y => U y - q y) x‖ ^ 2) ≤
      (n : ℝ) * d * W₀ * ε ^ 2 * r ^ n := by
    exact henergy.trans (by
      change (n : ℝ) * d * ‖w‖ ^ 2 ≤ _
      calc
        _ ≤ (n : ℝ) * d * (W₀ * ε ^ 2 * r ^ n) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
        _ = _ := by ring)
  let X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => T x (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hX : ContDiff ℝ ∞ X := hT.clm_apply contDiff_const
  have hXB (x) (_hx : x ∈ Metric.ball 0 r) : g.tangentNorm x (X x) ≤ 1 := by
    dsimp only [RiemannianMetric.tangentNorm, X]
    rw [hTiso, real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one]
    norm_num
  have hreference (x) (hx : x ∈ Metric.ball 0 r) :
      g.tangentNorm x ((show EuclideanSpace ℝ (Fin n) from D.gradient q x) - X x) ≤ t * r ^ 2 := by
    have hxnorm : ‖x‖ ≤ r := le_of_lt (by
      simpa only [Metric.mem_ball, dist_zero_right] using hx)
    have hc (v : EuclideanSpace ℝ (Fin n)) :
        ‖(T x).inverse v - v‖ ≤ ((9 / 4 : ℝ) * K * r ^ 2) * ‖v‖ := by
      calc
        _ ≤ K * (3 / 2 : ℝ) ^ 2 * ‖x‖ ^ 2 * ‖v‖ := hTcoframe x (hsubr hx) v
        _ ≤ K * (3 / 2 : ℝ) ^ 2 * r ^ 2 * ‖v‖ := by gcongr
        _ = _ := by ring
    have h := gradient_coordinate_sub_frame_norm_le D x (hTinv x) (hTiso x) ha
      (by positivity : 0 ≤ (9 / 4 : ℝ) * K * r ^ 2)
      (fun v => (hell x (hsubr hx) v).1) hc i
    change g.tangentNorm x ((show EuclideanSpace ℝ (Fin n) from D.gradient q x) - X x) ≤ _ at h
    apply h.trans
    norm_num [a, Real.sqrt_div] at ⊢
    dsimp only [t]
    nlinarith only [hK, sq_nonneg r, mul_nonneg hK (sq_nonneg r)]
  let s := σ * r ^ 2
  have hs : 0 < s := by dsimp only [s]; positivity
  have hscale : r ^ 2 * (n : ℝ) * K * 1 ≤ s := by
    have hnk : (n : ℝ) * K ≤ σ := by
      dsimp only [σ]
      nlinarith only [hn0, hK, mul_nonneg hn0 hK]
    simpa only [s, mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right hnk (sq_nonneg r)
  have hXE (x) (hx : x ∈ Metric.ball 0 r) :
      (∑ j, g.inner x (D.connection X x (g.orthonormalBasis x j))
        (D.connection X x (g.orthonormalBasis x j))) ≤ (s / r) ^ 2 := by
    have hxnorm : ‖x‖ ≤ r := le_of_lt (by
      simpa only [Metric.mem_ball, dist_zero_right] using hx)
    have hdir (v : EuclideanSpace ℝ (Fin n)) :
        g.tangentNorm x (D.connection X x v) ≤ (3 * (K + 1) * r) * ‖v‖ := by
      have h := hTconn x (hsubr hx) (EuclideanSpace.basisFun (Fin n) ℝ i) v
      simp only [OrthonormalBasis.norm_eq_one, mul_one] at h
      calc
        _ ≤ K * (3 / 2 : ℝ) ^ 2 * ‖x‖ * ‖v‖ := h
        _ ≤ K * (3 / 2 : ℝ) ^ 2 * r * ‖v‖ := by gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by nlinarith only [hr, hK, mul_nonneg hK hr.le]) (norm_nonneg v)
    have h := D.connection_energy_le_of_directional_bound X x ha
      (fun v => (hell x (hsubr hx) v).1) hdir
    apply h.trans
    have hdim : 36 * (n : ℝ) ≤ 100 * ((n : ℝ) + 1) ^ 2 := by
      nlinarith only [hn0, sq_nonneg (n : ℝ)]
    have hratio : s / r = 10 * ((n : ℝ) + 1) * (K + 1) * r := by
      dsimp only [s, σ]
      field_simp
    rw [hratio]
    dsimp only [a]
    convert mul_le_mul_of_nonneg_right hdim (sq_nonneg ((K + 1) * r)) using 1 <;>
      ring
  obtain ⟨F, hF, -, hFf⟩ := Poincare.Parabolic.Interior.exists_compact_smooth_extension
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r) Metric.isOpen_ball hclosed hUs
  have hgrad (x) (hx : x ∈ Metric.closedBall 0 r) : D.gradient F x = D.gradient U x := by
    simp only [LeviCivitaData.gradient, Poincare.mvfderiv_eq_of_eventuallyEq (hFf x hx)]
  have hFq (x) (hx : x ∈ S) :
      fderiv ℝ (fun y => F y - q y) x = fderiv ℝ (fun y => U y - q y) x :=
    ((hFf x (Metric.ball_subset_closedBall (hSr hx))).sub Filter.EventuallyEq.rfl).fderiv_eq
  have hI := D.integral_gradient_sub_reference_energy_le hF q.contDiff hX hS ha
    (fun x hx v => (hell x (hsubr (hSr hx)) v).1)
    (fun x hx => hreference x (hSr hx))
  have hIF : (∫ x in S, g.inner x ((show EuclideanSpace ℝ (Fin n) from D.gradient F x) - X x)
      ((show EuclideanSpace ℝ (Fin n) from D.gradient F x) - X x)) =
      ∫ x in S, g.inner x ((show EuclideanSpace ℝ (Fin n) from D.gradient U x) - X x)
        ((show EuclideanSpace ℝ (Fin n) from D.gradient U x) - X x) := by
    apply setIntegral_congr_fun hS.measurableSet
    intro x hx
    dsimp only
    rw [hgrad x (Metric.ball_subset_closedBall (hSr hx))]
  have hDF : (∫ x in S, ‖fderiv ℝ (fun y => F y - q y) x‖ ^ 2) =
      ∫ x in S, ‖fderiv ℝ (fun y => U y - q y) x‖ ^ 2 := by
    apply setIntegral_congr_fun hS.measurableSet
    intro x hx
    dsimp only
    rw [hFq x hx]
  rw [hIF, hDF] at hI
  have hI' : (∫ x in S, g.inner x ((show EuclideanSpace ℝ (Fin n) from D.gradient U x) - X x)
      ((show EuclideanSpace ℝ (Fin n) from D.gradient U x) - X x)) ≤
      8 * ((n : ℝ) * d * W₀ * ε ^ 2 * r ^ n) +
        2 * (t * r ^ 2) ^ 2 * (V₀ * r ^ n) := by
    have h := hI.trans (add_le_add
      (mul_le_mul_of_nonneg_left henergy' (by positivity))
      (mul_le_mul_of_nonneg_left hmassvol (by positivity)))
    simpa only [a, show (2 : ℝ) / (1 / 4) = 8 by norm_num, Measure.real_def] using h
  have hm := hmean (2 * r) r hr hr1 hclosed g D
    (fun x hx => hell x (hsubr hx)) (fun x hx => hcurv x (hsubr hx)) z hSr
    U X hUs hX hharm 1 s hs hscale hXB hXE
  dsimp only at hm
  let Z := 8 * (n : ℝ) * d * W₀ * ε ^ 2 + V₀ * (2 * t ^ 2 + σ ^ 2) * r ^ 4
  have htotal : (∫ x in S, g.inner x ((show EuclideanSpace ℝ (Fin n) from D.gradient U x) - X x)
      ((show EuclideanSpace ℝ (Fin n) from D.gradient U x) - X x)) + volume.real S * s ^ 2 ≤
      Z * r ^ n := by
    calc
      _ ≤ 8 * ((n : ℝ) * d * W₀ * ε ^ 2 * r ^ n) +
          2 * (t * r ^ 2) ^ 2 * (V₀ * r ^ n) + (V₀ * r ^ n) * s ^ 2 :=
        add_le_add hI' (mul_le_mul_of_nonneg_right hmassvol (sq_nonneg s))
      _ = _ := by dsimp only [Z, s]; ring
  have hQ : g.inner z ((show EuclideanSpace ℝ (Fin n) from D.gradient U z) - X z)
      ((show EuclideanSpace ℝ (Fin n) from D.gradient U z) - X z) ≤ C * Z := by
    have h := hm.trans (mul_le_mul_of_nonneg_left htotal (by positivity))
    rw [Real.rpow_neg hr.le, Real.rpow_natCast] at h
    have hcancel : C * (r ^ n)⁻¹ * (Z * r ^ n) = C * Z := by
      field_simp
    rw [hcancel] at h
    nlinarith only [h, sq_nonneg s]
  have hzS : z ∈ S := Metric.mem_closedBall_self (by positivity)
  have hzΩ := hSΩ hzS
  have hdiff := differential_sub_linear_sq_le D
    ((hUs.contDiffAt (Metric.isOpen_ball.mem_nhds hzΩ)).differentiableAt (by simp)) q
    (X z) hb.le (fun v => (hell z (hsubr (hSr hzS)) v).2) (hreference z (hSr hzS))
  have hsq : ‖fderiv ℝ U z - q‖ ^ 2 ≤ τ ^ 2 := by
    calc
      _ ≤ 2 * b * (g.inner z ((show EuclideanSpace ℝ (Fin n) from D.gradient U z) - X z)
          ((show EuclideanSpace ℝ (Fin n) from D.gradient U z) - X z) + (t * r ^ 2) ^ 2) := hdiff
      _ ≤ 2 * b * (C * Z + (t * r ^ 2) ^ 2) := by gcongr
      _ = A * ε ^ 2 + B * r ^ 4 := by dsimp only [A, B, Z]; ring
      _ ≤ τ ^ 2 := by nlinarith only [hεsmall, hrsmall.le, sq_nonneg τ]
  exact (sq_le_sq₀ (norm_nonneg _) hτ.le).mp hsq

end PoincareConjecture.HarmonicCoordinates
