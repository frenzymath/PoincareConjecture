import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Poisson.Approximation











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Bundle Topology
open Bundle

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M] [CompactSpace M] in
private theorem continuous_gradient_inner (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ v) :
    Continuous (fun x => g.inner x (D.gradient u x) (D.gradient v x)) := by
  have hs : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (D.gradient u x) (D.gradient v x)) := by
    intro x
    simpa using (contMDiffAt_totalSpace.mp
      (((g.contMDiff x).clm_bundle_apply (D.contMDiffAt_gradient (hu x))).clm_bundle_apply
        (D.contMDiffAt_gradient (hv x)))).2
  exact hs.continuous


theorem integral_scalar_mul_laplacian_le_fisher_add_laplacian_sq
    (D : LeviCivitaData g) (hR : ∀ x, 0 < D.scalarCurvature x)
    {u : M → ℝ} (hu : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ u) (r : ℝ) :
    2 * (∫ x, (D.scalarCurvature x - r) * D.laplacian u x ∂g.volumeMeasure) ≤
      (∫ x, g.inner x (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x) /
        D.scalarCurvature x ∂g.volumeMeasure) +
      ∫ x, (D.laplacian u x) ^ 2 ∂g.volumeMeasure := by
  let R := D.scalarCurvature
  have hRs := D.contMDiff_scalarCurvature
  have hnr := continuous_gradient_inner D hRs hRs
  have hnu := continuous_gradient_inner D hu hu
  have hnru := continuous_gradient_inner D hRs hu
  have hji : Integrable (fun x =>
      g.inner x (D.gradient R x) (D.gradient R x) / R x) g.volumeMeasure :=
    (hnr.div hRs.continuous (fun x => (hR x).ne')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hei : Integrable (fun x => R x * g.inner x (D.gradient u x) (D.gradient u x))
      g.volumeMeasure := (hRs.continuous.mul hnu).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hci := hnru.integrable_of_hasCompactSupport
    (μ := g.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  have hp (x : M) : 0 ≤
      g.inner x (D.gradient R x) (D.gradient R x) / R x +
      2 * g.inner x (D.gradient R x) (D.gradient u x) +
      R x * g.inner x (D.gradient u x) (D.gradient u x) := by
    let : RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) := ⟨g.toRiemannianMetric⟩
    have hs : 0 ≤ g.inner x (D.gradient R x + R x • D.gradient u x)
        (D.gradient R x + R x • D.gradient u x) := by
      change 0 ≤ inner ℝ (D.gradient R x + R x • D.gradient u x)
        (D.gradient R x + R x • D.gradient u x)
      exact real_inner_self_nonneg
    change 0 ≤ inner ℝ (D.gradient R x + R x • D.gradient u x)
      (D.gradient R x + R x • D.gradient u x) at hs
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right] at hs
    have hsymm : inner ℝ (D.gradient u x) (D.gradient R x) =
        inner ℝ (D.gradient R x) (D.gradient u x) := real_inner_comm _ _
    rw [hsymm] at hs
    apply (nonneg_of_mul_nonneg_right (a := R x) ?_ (hR x))
    change 0 ≤ R x * (inner ℝ (D.gradient R x) (D.gradient R x) / R x +
      2 * inner ℝ (D.gradient R x) (D.gradient u x) +
      R x * inner ℝ (D.gradient u x) (D.gradient u x))
    have hne : R x ≠ 0 := (hR x).ne'
    rw [mul_add, mul_add, mul_div_cancel₀ _ hne]
    nlinarith
  have hint : 0 ≤ ∫ x,
      g.inner x (D.gradient R x) (D.gradient R x) / R x +
      2 * g.inner x (D.gradient R x) (D.gradient u x) +
      R x * g.inner x (D.gradient u x) (D.gradient u x) ∂g.volumeMeasure :=
    integral_nonneg hp
  have hadd : Integrable (fun x =>
      g.inner x (D.gradient R x) (D.gradient R x) / R x +
      2 * g.inner x (D.gradient R x) (D.gradient u x)) g.volumeMeasure :=
    hji.add (hci.const_mul 2)
  rw [integral_add hadd hei, integral_add hji (hci.const_mul 2), integral_const_mul] at hint
  have hgreen := D.integral_mul_laplacian hRs hu (HasCompactSupport.of_compactSpace _)
  have hmean : (∫ x, (R x - r) * D.laplacian u x ∂g.volumeMeasure) =
      ∫ x, R x * D.laplacian u x ∂g.volumeMeasure := by
    simp_rw [sub_mul]
    rw [integral_sub (D.integrable_mul_laplacian hRs hu (HasCompactSupport.of_compactSpace _))
      (((D.contMDiff_laplacian hu).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul r), integral_const_mul,
      D.integral_laplacian_eq_zero_compact hu, mul_zero, sub_zero]
  rw [hmean]
  have hb := D.integral_scalar_gradient_le_laplacian_sq hu
  change 0 ≤ (∫ x, g.inner x (D.gradient R x) (D.gradient R x) / R x ∂g.volumeMeasure) +
    2 * (∫ x, g.inner x (D.gradient R x) (D.gradient u x) ∂g.volumeMeasure) +
    ∫ x, R x * g.inner x (D.gradient u x) (D.gradient u x) ∂g.volumeMeasure at hint
  dsimp [R] at *
  linarith


theorem integral_scalar_variance_le_fisher (D : LeviCivitaData g)
    (hR : ∀ x, 0 < D.scalarCurvature x) {r : ℝ}
    (hr : (∫ x, D.scalarCurvature x ∂g.volumeMeasure) = r * g.volumeMeasure.real univ) :
    (∫ x, (D.scalarCurvature x - r) ^ 2 ∂g.volumeMeasure) ≤
      ∫ x, g.inner x (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x) /
        D.scalarCurvature x ∂g.volumeMeasure := by
  let J := ∫ x, g.inner x (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x) /
    D.scalarCurvature x ∂g.volumeMeasure
  have hmem : MemLp (fun x => D.scalarCurvature x - r) 2
      (g.volumeMeasure.restrict univ) := by
    have hcont : Continuous (fun x => D.scalarCurvature x - r) :=
      D.contMDiff_scalarCurvature.continuous.sub continuous_const
    simpa only [Measure.restrict_univ] using hcont.memLp_of_hasCompactSupport
        (μ := g.volumeMeasure) (p := 2) (HasCompactSupport.of_compactSpace _)
  let F := hmem.toLp (fun x => D.scalarCurvature x - r)
  have hFae : (F : M → ℝ) =ᵐ[g.volumeMeasure] (fun x => D.scalarCurvature x - r) := by
    simpa only [Measure.restrict_univ] using hmem.coeFn_toLp
  have hmean : (∫ x, F x ∂g.volumeMeasure) = 0 := by
    rw [integral_congr_ae hFae, integral_sub
      (D.contMDiff_scalarCurvature.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) (integrable_const r), integral_const, hr]
    simp only [smul_eq_mul]
    ring
  have hclosed : IsClosed {H : Lp ℝ 2 (g.volumeMeasure.restrict univ) |
      2 * ⟪F, H⟫_ℝ ≤ J + ‖H‖ ^ 2} :=
    isClosed_le (continuous_const.mul (continuous_const.inner continuous_id))
      (continuous_const.add (continuous_norm.pow 2))
  have hrange : Set.range (Dirichlet.closedLaplacianToL2 D) ⊆
      {H : Lp ℝ 2 (g.volumeMeasure.restrict univ) | 2 * ⟪F, H⟫_ℝ ≤ J + ‖H‖ ^ 2} := by
    rintro _ ⟨u, rfl⟩
    have hΔ : (Dirichlet.closedLaplacianToL2 D u : M → ℝ) =ᵐ[g.volumeMeasure]
        D.laplacian u := by
      simpa only [Measure.restrict_univ] using Dirichlet.closedLaplacianToL2_ae D u
    have hpair : ⟪F, Dirichlet.closedLaplacianToL2 D u⟫_ℝ =
        ∫ x, (D.scalarCurvature x - r) * D.laplacian u x ∂g.volumeMeasure := by
      rw [L2.inner_def, setIntegral_univ]
      apply integral_congr_ae
      filter_upwards [hFae, hΔ] with x hx hy
      simp [hx, hy, mul_comm]
    have hnorm : ‖Dirichlet.closedLaplacianToL2 D u‖ ^ 2 =
        ∫ x, (D.laplacian u x) ^ 2 ∂g.volumeMeasure := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def, setIntegral_univ]
      apply integral_congr_ae
      filter_upwards [hΔ] with x hx
      simp [hx, pow_two]
    change 2 * ⟪F, Dirichlet.closedLaplacianToL2 D u⟫_ℝ ≤
      J + ‖Dirichlet.closedLaplacianToL2 D u‖ ^ 2
    rw [hpair, hnorm]
    exact D.integral_scalar_mul_laplacian_le_fisher_add_laplacian_sq hR u.smooth r
  have hlim := (closure_minimal hrange hclosed)
    (Dirichlet.mem_closure_range_closedLaplacian_of_integral_eq_zero D F hmean)
  change 2 * ⟪F, F⟫_ℝ ≤ J + ‖F‖ ^ 2 at hlim
  have hnorm : ‖F‖ ^ 2 = ∫ x, (D.scalarCurvature x - r) ^ 2 ∂g.volumeMeasure := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, setIntegral_univ]
    apply integral_congr_ae
    filter_upwards [hFae] with x hx
    simp [hx, pow_two]
  rw [real_inner_self_eq_norm_sq, hnorm] at hlim
  dsimp [J] at hlim
  linarith


theorem integral_scalar_variance_le_fisher_of_integral_sub_eq_zero
    (D : LeviCivitaData g) (hR : ∀ x, 0 < D.scalarCurvature x) {r : ℝ}
    (hr : (∫ x, D.scalarCurvature x - r ∂g.volumeMeasure) = 0) :
    (∫ x, (D.scalarCurvature x - r) ^ 2 ∂g.volumeMeasure) ≤
      ∫ x, g.inner x (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x) /
        D.scalarCurvature x ∂g.volumeMeasure := by
  apply D.integral_scalar_variance_le_fisher hR
  rw [integral_sub
    (D.contMDiff_scalarCurvature.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (integrable_const r), integral_const,
    smul_eq_mul] at hr
  linarith

end PoincareConjecture.LeviCivitaData
