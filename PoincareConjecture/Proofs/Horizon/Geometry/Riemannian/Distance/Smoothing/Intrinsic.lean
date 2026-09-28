import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Local
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactEnergy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Chart








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal

namespace PoincareConjecture

section LocalConversion

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem chart_intrinsic_bounds (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (a : M) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ (extChartAt (𝓡 n) a).target)
    {f : M → ℝ}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ((extChartAt (𝓡 n) a).symm z))
    {b C L G : ℝ} (hb : 0 < b) (hC : 0 ≤ C) (hL : 0 ≤ L) (hG : 0 ≤ G)
    (hlow : ∀ v : EuclideanSpace ℝ (Fin n), b * ‖v‖ ^ 2 ≤
      g.pullbackCoefficients (extChartAt (𝓡 n) a).symm z v v)
    (hfirst : ‖fderiv ℝ (f ∘ (extChartAt (𝓡 n) a).symm) z‖ ≤ L)
    (hsecond : ∀ v : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 n) a).symm)) z v v ≤ C * ‖v‖ ^ 2)
    (hconn : ‖CoordinateExponential.christoffelBilinear
      (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm) z‖ ≤ G) :
    g.tangentNorm ((extChartAt (𝓡 n) a).symm z)
      (D.gradient f ((extChartAt (𝓡 n) a).symm z)) ≤ L / Real.sqrt b ∧
    ∀ w : TangentSpace (𝓡 n) ((extChartAt (𝓡 n) a).symm z),
      D.hessian f ((extChartAt (𝓡 n) a).symm z) w w ≤
        ((C + L * G) / b) * g.inner ((extChartAt (𝓡 n) a).symm z) w w := by
  let c := extChartAt (𝓡 n) a
  let T := mfderiv (𝓡 n) (𝓡 n) c.symm z
  let Γ := CoordinateExponential.christoffelBilinear (g.pullbackCoefficients c.symm) z
  have hlow' (v : EuclideanSpace ℝ (Fin n)) :
      b * ‖v‖ ^ 2 ≤ g.inner (c.symm z) (T v) (T v) := by
    simpa only [RiemannianMetric.pullbackCoefficients,
      ContinuousLinearMap.bilinearComp_apply] using! hlow v
  have hT : T.IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hz
  have hnorm (v : EuclideanSpace ℝ (Fin n)) :
      ‖v‖ ≤ g.tangentNorm (c.symm z) (T v) / Real.sqrt b := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr
    have h := Real.sqrt_le_sqrt (hlow' v)
    simpa +instances only [Real.sqrt_mul hb.le, Real.sqrt_sq (norm_nonneg v),
      RiemannianMetric.tangentNorm, mul_comm] using h
  have hfirst' (v : EuclideanSpace ℝ (Fin n)) :
      |fderiv ℝ (f ∘ c.symm) z v| ≤ L * ‖v‖ :=
    ((fderiv ℝ (f ∘ c.symm) z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hfirst (norm_nonneg v))
  constructor
  · apply (D.gradient_norm_le_iff f (c.symm z) (by positivity)).mpr
    intro w
    obtain ⟨v, rfl⟩ := hT.surjective w
    have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) a hz).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
    have heq := congrArg (fun F => F v)
      (mfderiv_comp z (hf.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at heq
    change fderiv ℝ (f ∘ c.symm) z v = mvfderiv (𝓡 n) f (c.symm z) (T v) at heq
    rw [← heq]
    exact (hfirst' v).trans (by
      simpa [div_mul_eq_mul_div, mul_div_assoc] using
        mul_le_mul_of_nonneg_left (hnorm v) hL)
  · intro w
    obtain ⟨v, rfl⟩ := hT.surjective w
    have hΓ : ‖Γ v v‖ ≤ G * ‖v‖ ^ 2 :=
      (Γ.le_opNorm₂ v v).trans (by nlinarith [sq_nonneg ‖v‖])
    have hterm : -fderiv ℝ (f ∘ c.symm) z (Γ v v) ≤ L * G * ‖v‖ ^ 2 :=
      (neg_le_abs _).trans ((hfirst' _).trans (by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hΓ hL))
    have hcoord : D.hessian f (c.symm z) (T v) (T v) ≤ (C + L * G) * ‖v‖ ^ 2 := by
      rw [D.hessian_in_chart a hz hf]
      change fderiv ℝ (fderiv ℝ (f ∘ c.symm)) z v v -
        fderiv ℝ (f ∘ c.symm) z (Γ v v) ≤ _
      nlinarith [hsecond v]
    apply hcoord.trans
    change (C + L * G) * ‖v‖ ^ 2 ≤ ((C + L * G) / b) *
      g.inner (c.symm z) (T v) (T v)
    have hsquare : ‖v‖ ^ 2 ≤ g.inner (c.symm z) (T v) (T v) / b :=
      (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using hlow' v)
    simpa only [div_mul_eq_mul_div, mul_div_assoc] using
      mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ C + L * G)

end LocalConversion

namespace RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem exists_intrinsic_local_distance_smoothing
    [T3Space M] [ConnectedSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ v w : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y v w)
    (p x : M) (hpx : p ≠ x) :
    ∃ (U : Set M) (L H : ℝ), IsOpen U ∧ x ∈ U ∧ p ∉ U ∧ 0 ≤ L ∧ 0 ≤ H ∧
      ∀ ε : ℝ, 0 < ε → ∃ rho : M → ℝ,
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U ∧
        (∀ y ∈ U, |rho y - (g.edist p y).toReal| ≤ ε) ∧
        (∀ y ∈ U, g.tangentNorm y (D.gradient rho y) ≤ L) ∧
        ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
          D.hessian rho y v v ≤ H * g.inner y v v := by
  let c := extChartAt (𝓡 n) x
  obtain ⟨r, C, L, hr, hC, htarget, hne, hsmooth⟩ :=
    g.exists_local_distance_smoothing D hcomplete hK hsec p x hpx
  let S := Metric.closedBall (c x) r
  have hS : IsCompact S := isCompact_closedBall _ _
  have hStarget : S ⊆ c.target := by
    intro z hz
    apply htarget
    exact (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt (by linarith)))
  have hTi (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ (extChartAt (𝓡 n) x).target) :
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm z).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hz
  let B := g.pullbackCoefficients c.symm
  obtain ⟨b, hb, hlow⟩ := exists_uniform_bilinear_lower_bound hS
    ((g.contDiffOn_chartCoefficients x).continuousOn.mono hStarget)
    (fun z hz v hv => g.pos _ _ (fun hzero => hv ((hTi z (hStarget hz)).injective (by
      simpa only [map_zero] using! hzero))))
  let Γ := CoordinateExponential.christoffelBilinear B
  have hΓ : ContinuousOn Γ S := by
    intro z hz
    exact (CoordinateExponential.contDiffAt_christoffelBilinear
      ((g.contDiffOn_chartCoefficients x).contDiffAt
        (extChartAt_target_mem_nhds' (hStarget hz)))
      (g.isInvertible_chartCoefficients x (hStarget hz))).continuousAt.continuousWithinAt
  have hΓnorm : ContinuousOn (fun z => ‖Γ z‖) S :=
    (continuous_norm (E := EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).comp_continuousOn hΓ
  obtain ⟨G, hGimage⟩ := hS.bddAbove_image hΓnorm
  have hGbound (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ S) : ‖Γ z‖ ≤ G :=
    hGimage ⟨z, hz, rfl⟩
  have hG : 0 ≤ G := (norm_nonneg (Γ (c x))).trans
    (hGbound (c x) (Metric.mem_closedBall_self hr.le))
  let U := c.source ∩ c ⁻¹' Metric.ball (c x) (r / 2)
  have hchart : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source := by
    simpa only [c, extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓡 n) (x := x) (n := ∞))
  have hU : IsOpen U := hchart.continuousOn.isOpen_inter_preimage
    (isOpen_extChartAt_source x) Metric.isOpen_ball
  have hxU : x ∈ U := ⟨mem_extChartAt_source x, Metric.mem_ball_self (half_pos hr)⟩
  have hsmall (y : M) (hy : y ∈ U) : c y ∈ Metric.ball (c x) r :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hy.2).trans (half_lt_self hr))
  have hlarge (y : M) (hy : y ∈ U) : c y ∈ Metric.ball (c x) (2 * r) :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp (hsmall y hy)).trans (by linarith))
  have hpU : p ∉ U := by
    intro hp
    exact hne (c p) (hlarge p hp) (c.left_inv hp.1)
  refine ⟨U, (L : ℝ) / Real.sqrt b, (C + (L : ℝ) * G) / b,
    hU, hxU, hpU, by positivity, by positivity, ?_⟩
  intro ε hε
  obtain ⟨u, hu, hLu, herr, hsecond⟩ := hsmooth ε hε
  let rho := u ∘ c
  have hrho : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U := by
    intro y hy
    exact ((contMDiffAt_iff_contDiffAt.mpr (hu.contDiffAt)).comp y
      (hchart.contMDiffAt (extChartAt_source_mem_nhds' hy.1))).contMDiffWithinAt
  have hbounds (y : M) (hy : y ∈ U) :
      g.tangentNorm y (D.gradient rho y) ≤ (L : ℝ) / Real.sqrt b ∧
      ∀ v : TangentSpace (𝓡 n) y, D.hessian rho y v v ≤
        ((C + (L : ℝ) * G) / b) * g.inner y v v := by
    have hz : c y ∈ c.target := c.map_source hy.1
    have heq : (rho ∘ c.symm) =ᶠ[𝓝 (c y)] u := by
      filter_upwards [extChartAt_target_mem_nhds' hz] with z hzt
      exact congrArg u (c.right_inv hzt)
    have hfirst : ‖fderiv ℝ (rho ∘ c.symm) (c y)‖ ≤ (L : ℝ) := by
      rw [heq.fderiv_eq]
      exact norm_fderiv_le_of_lipschitz ℝ hLu
    have hsecond' : ∀ v : EuclideanSpace ℝ (Fin n),
        fderiv ℝ (fderiv ℝ (rho ∘ c.symm)) (c y) v v ≤ C * ‖v‖ ^ 2 := by
      rw [heq.fderiv.fderiv_eq]
      exact hsecond (c y) (hsmall y hy)
    have hρ : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho (c.symm (c y)) := by
      rw [c.left_inv hy.1]
      exact hrho.contMDiffAt (hU.mem_nhds hy)
    have h := chart_intrinsic_bounds g D x hz hρ hb hC L.coe_nonneg hG
      (hlow (c y) (Metric.ball_subset_closedBall (hsmall y hy))) hfirst hsecond'
      (hGbound (c y) (Metric.ball_subset_closedBall (hsmall y hy)))
    have hyinv : (extChartAt (𝓡 n) x).symm (c y) = y := c.left_inv hy.1
    let P : M → Prop := fun q =>
      g.tangentNorm q (D.gradient rho q) ≤ (L : ℝ) / Real.sqrt b ∧
      ∀ v : TangentSpace (𝓡 n) q, D.hessian rho q v v ≤
        ((C + (L : ℝ) * G) / b) * g.inner q v v
    have hP : P ((extChartAt (𝓡 n) x).symm (c y)) := h
    exact (congrArg P hyinv).mp hP
  refine ⟨rho, hrho, ?_, fun y hy => (hbounds y hy).1, fun y hy => (hbounds y hy).2⟩
  intro y hy
  have hyinv : (extChartAt (𝓡 n) x).symm (c y) = y := c.left_inv hy.1
  change |u (c y) - (g.edist p y).toReal| ≤ ε
  simpa only [hyinv] using herr (c y) (hlarge y hy)

end RiemannianMetric
end PoincareConjecture
