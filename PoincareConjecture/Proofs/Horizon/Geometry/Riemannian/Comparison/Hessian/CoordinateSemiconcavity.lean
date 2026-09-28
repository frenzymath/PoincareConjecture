import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.CoordinateBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.Distance
import PoincareConjecture.Proofs.Horizon.Analysis.Convex.EuclideanUpperSupport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle NNReal

namespace PoincareConjecture.RiemannianMetric

theorem exists_distance_coordinate_semiconcave_ball
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ u v : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y u v)
    (p x : M) (hpx : p ≠ x) :
    ∃ r C : ℝ, ∃ L : ℝ≥0, 0 < r ∧ 0 ≤ C ∧
      Metric.ball ((extChartAt (𝓡 n) x) x) r ⊆ (extChartAt (𝓡 n) x).target ∧
      (∀ z ∈ Metric.ball ((extChartAt (𝓡 n) x) x) r,
        (extChartAt (𝓡 n) x).symm z ≠ p) ∧
      ConcaveOn ℝ (Metric.ball ((extChartAt (𝓡 n) x) x) r)
        (fun z => (g.edist p ((extChartAt (𝓡 n) x).symm z)).toReal -
          C * ‖z‖ ^ 2 / 2) ∧
      LipschitzOnWith L (fun z => (g.edist p ((extChartAt (𝓡 n) x).symm z)).toReal)
        (Metric.ball ((extChartAt (𝓡 n) x) x) r) := by
  let c := extChartAt (𝓡 n) x
  let z₀ := c x
  let d : EuclideanSpace ℝ (Fin n) → ℝ := fun z => (g.edist p (c.symm z)).toReal
  let B := g.pullbackCoefficients c.symm
  let Γ := CoordinateExponential.christoffelBilinear B
  have hz₀ : z₀ ∈ c.target := mem_extChartAt_target x
  have hc (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm z :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hz).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
  have hdcont : ContinuousAt d z₀ :=
    (g.continuous_toReal_edist p).continuousAt.comp (hc z₀ hz₀).continuousAt
  have hdpos : 0 < d z₀ := by
    have heq : c.symm z₀ = x := extChartAt_to_inv x
    change 0 < (g.edist p (c.symm z₀)).toReal
    rw [heq]
    have hpos : 0 < g.edist p x := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
      let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
      exact edist_pos.mpr hpx
    exact ENNReal.toReal_pos hpos.ne' (g.edist_ne_top p x)
  let H := 4 / (3 * d z₀) + K * d z₀ / 4 + 1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hHcont : ContinuousAt (fun z => 4 / (3 * d z) + K * d z / 4) z₀ := by
    exact (continuousAt_const.div (continuousAt_const.mul hdcont)
      (mul_ne_zero (by norm_num) hdpos.ne')).add
      ((continuousAt_const.mul hdcont).div_const 4)
  have hBcont : ContinuousAt B z₀ :=
    ((g.contDiffOn_chartCoefficients x).contDiffAt
      (extChartAt_target_mem_nhds' hz₀)).continuousAt
  have hΓcont : ContinuousAt Γ z₀ :=
    (CoordinateExponential.contDiffAt_christoffelBilinear
      ((g.contDiffOn_chartCoefficients x).contDiffAt
        (extChartAt_target_mem_nhds' hz₀))
      (g.isInvertible_chartCoefficients x hz₀)).continuousAt
  let A := ‖B z₀‖ + ‖Γ z₀‖ + 2
  have hA : 1 ≤ A := by dsimp [A]; linarith [norm_nonneg (B z₀), norm_nonneg (Γ z₀)]
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hBnorm : ContinuousAt (fun z => ‖B z‖) z₀ :=
    (continuous_norm (E := EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).continuousAt.comp hBcont
  have hΓnorm : ContinuousAt (fun z => ‖Γ z‖) z₀ :=
    (continuous_norm (E := EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).continuousAt.comp hΓcont
  have hBnear : ∀ᶠ z in 𝓝 z₀, ‖B z‖ < A :=
    hBnorm.eventually_lt continuousAt_const
      (by dsimp [A]; linarith [norm_nonneg (Γ z₀)])
  have hΓnear : ∀ᶠ z in 𝓝 z₀, ‖Γ z‖ < A :=
    hΓnorm.eventually_lt continuousAt_const
      (by dsimp [A]; linarith [norm_nonneg (B z₀)])
  have hev : ∀ᶠ z in 𝓝 z₀,
      z ∈ c.target ∧ 0 < d z ∧
      4 / (3 * d z) + K * d z / 4 ≤ H ∧ ‖B z‖ ≤ A ∧ ‖Γ z‖ ≤ A := by
    filter_upwards [extChartAt_target_mem_nhds' hz₀,
      continuousAt_const.eventually_lt hdcont hdpos,
      hHcont.eventually_lt continuousAt_const (show _ < H by dsimp [H]; linarith),
      hBnear, hΓnear]
      with z hz hd hH' hB' hΓ'
    exact ⟨hz, hd, hH'.le, hB'.le, hΓ'.le⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have htarget : Metric.ball z₀ r ⊆ c.target := fun z hz => (hball hz).1
  have hne (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball z₀ r) :
      c.symm z ≠ p := by
    intro heq
    have h := (hball hz).2.1
    dsimp [d] at h
    rw [heq] at h
    simp only [edist, Manifold.riemannianEDist_self, ENNReal.toReal_zero,
      lt_self_iff_false] at h
  let L : ℝ≥0 := ⟨Real.sqrt A, Real.sqrt_nonneg A⟩
  have hLip : LipschitzOnWith L d (Metric.ball z₀ r) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro z hz w hw
    apply (g.abs_toReal_edist_sub_le p (c.symm z) (c.symm w)).trans
    apply g.toReal_edist_le_of_pullback_upper Metric.isOpen_ball (convex_ball z₀ r)
      (fun z hz => (hc z (htarget hz)).contMDiffWithinAt) hA0 ?_ hz hw
    intro y hy v
    change B y v v ≤ A * ‖v‖ ^ 2
    have h := (B y).le_opNorm₂ v v
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (by
      nlinarith [(hball hy).2.2.2.1, sq_nonneg ‖v‖]))
  refine ⟨r, H * A + A * A, L, hr, by positivity, htarget, hne, ?_, hLip⟩
  apply Poincare.Analysis.concaveOn_sub_norm_sq_of_hessian_upper_support
    (convex_ball z₀ r)
  · exact (g.continuous_toReal_edist p).comp_continuousOn
      (fun z hz => (hc z (htarget hz)).continuousAt.continuousWithinAt)
  · intro z hz
    obtain ⟨U, rho, hU, hzU, hrho, htouch, hmajor, hgrad, hhess⟩ :=
      g.exists_distance_hessian_upper_support D hcomplete hK hsec p (c.symm z) (hne z hz).symm
    have hrhoz := hrho.contMDiffAt (hU.mem_nhds hzU)
    refine ⟨rho ∘ c.symm,
      (contMDiffAt_iff_contDiffAt.mp (hrhoz.comp z (hc z (htarget hz)))).of_le
        (by norm_cast), htouch, ?_, ?_⟩
    · filter_upwards [(hc z (htarget hz)).continuousAt.preimage_mem_nhds
        (hU.mem_nhds hzU)] with w hw
      exact hmajor (c.symm w) hw
    · intro v
      apply D.fderiv2_chart_le_of_hessian_le x (htarget hz) hrhoz hgrad hH hA
        (hball hz).2.2.2.1 (hball hz).2.2.2.2
      intro w
      apply (hhess w).trans
      apply mul_le_mul_of_nonneg_right (hball hz).2.2.1
      by_cases hw : w = 0
      · simp [hw]
      · exact (g.pos _ w hw).le

end PoincareConjecture.RiemannianMetric
