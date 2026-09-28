import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallSphereCorrection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereNormalSign
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartDerivative
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem fderiv_normal_pos_of_local_interior
    (f : E3 → E3) {x : E3} (hx : ‖x‖ = 1)
    (hf : DifferentiableAt ℝ f x)
    (hfixed : ∀ᶠ y in 𝓝 x, ‖y‖ = 1 → f y = y)
    (hi : Function.Injective (fderiv ℝ f x))
    (hin : ∀ᶠ y in 𝓝 x, ‖y‖ ≤ 1 → ‖f y‖ ≤ 1) :
    0 < ⟪x, fderiv ℝ f x x⟫_ℝ := by
  have hfx : f x = x := hfixed.self_of_nhds hx
  have hne := fixedHyperplane_normal_ne_zero (fderiv ℝ f x) x hx
    (fun v hv => fderiv_eq_of_local_fixed_sphere f x v hx hf hfixed hv) hi
  let γ : ℝ → E3 := fun t => (1 + t) • x
  have hγ0 : γ 0 = x := by simp only [γ, add_zero, one_smul]
  have hγ : HasDerivAt γ x 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const x
  have hF : HasFDerivAt f (fderiv ℝ f x) (γ 0) := by
    rw [hγ0]
    exact hf.hasFDerivAt
  have hg : HasDerivAt (fun t => ‖f (γ t)‖ ^ 2)
      (2 * ⟪x, fderiv ℝ f x x⟫_ℝ) 0 := by
    simpa only [Function.comp_def, hγ0, hfx] using (hF.comp_hasDerivAt 0 hγ).norm_sq
  have hcont : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := by
    simpa only [hγ0] using hγ.continuousAt.tendsto
  have hnonneg : 0 ≤ 2 * ⟪x, fderiv ℝ f x x⟫_ℝ := by
    apply ge_of_tendsto hg.tendsto_slope_zero_left
    filter_upwards [(hcont.eventually hin).filter_mono nhdsWithin_le_nhds,
      (lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htlow htneg
    have ht0 : t < 0 := htneg
    have hγnorm : ‖γ t‖ ≤ 1 := by
      simp only [γ, norm_smul, Real.norm_eq_abs, hx, mul_one,
        abs_of_pos (by linarith only [htlow] : 0 < 1 + t)]
      linarith only [ht0]
    have hn := ht hγnorm
    have hs : ‖f (γ t)‖ ^ 2 - 1 ≤ 0 := by nlinarith [norm_nonneg (f (γ t))]
    simpa only [zero_add, hγ0, hfx, hx, one_pow, smul_eq_mul] using
      mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr ht0.le) hs
  exact lt_of_le_of_ne (by linarith) (Ne.symm hne)

theorem exists_ball_chart_common_germ_of_sphere_patch
    (A B : BallNeighborhoodChart E3 E3)
    {K U : Set E3} (hK : IsCompact K)
    (hKS : K ⊆ sphere (0 : E3) 1)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hpatch : ∀ y ∈ U, ‖y‖ = 1 → A.chart y = B.chart y)
    (hBA : B.closedRegion ⊆ A.closedRegion) :
    let T := B.chart.trans A.chart.symm
    ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      (∀ y ∈ sphere (0 : E3) 1, F y = y) ∧
      F '' ball (0 : E3) 1 = ball 0 1 ∧
      F '' closedBall (0 : E3) 1 = closedBall 0 1 ∧
      (∀ᶠ y in 𝓝ˢ K, F y = T y) ∧
      ∃ A' : BallNeighborhoodChart E3 E3,
        A'.chart = F.toHomeomorph.toOpenPartialHomeomorph.trans A.chart ∧
        A'.chart.source = F ⁻¹' A.chart.source ∧
        A'.chart.target = A.chart.target ∧
        (∀ y : E3, A'.chart y = A.chart (F y)) ∧
        (∀ Y : E3, A'.chart.symm Y = F.symm (A.chart.symm Y)) ∧
        A'.inside = A.inside ∧ A'.closedRegion = A.closedRegion ∧
        A'.boundary = A.boundary ∧
        (∀ y ∈ sphere (0 : E3) 1, A'.chart y = A.chart y) ∧
        ∀ᶠ y in 𝓝ˢ K,
          y ∈ A'.chart.source ∧ y ∈ B.chart.source ∧ A'.chart y = B.chart y := by
  let T := B.chart.trans A.chart.symm
  have hT : ContDiffOn ℝ ∞ T T.source :=
    A.smooth_symm.comp (B.smooth.mono inter_subset_left) (fun _ hy => hy.2)
  have hTi : ContDiffOn ℝ ∞ T.symm T.target :=
    B.smooth_symm.comp (A.smooth.mono inter_subset_left) (fun _ hy => hy.2)
  let V := U ∩ T.source
  have hV : IsOpen V := hU.inter T.open_source
  have hKV : K ⊆ V := by
    intro y hy
    have hys := sphere_subset_closedBall (hKS hy)
    have hyn := mem_sphere_zero_iff_norm.mp (hKS hy)
    refine ⟨hKU hy, B.closedBall_subset_source hys, ?_⟩
    change B.chart y ∈ A.chart.target
    rw [← hpatch y (hKU hy) hyn]
    exact A.chart.map_source (A.closedBall_subset_source hys)
  have hfixed (y : E3) (hy : y ∈ V) (hyn : ‖y‖ = 1) : T y = y := by
    change A.chart.symm (B.chart y) = y
    rw [← hpatch y hy.1 hyn]
    exact A.chart.left_inv (A.closedBall_subset_source (mem_closedBall_zero_iff.mpr hyn.le))
  have hinner (z : E3) (hzn : ‖z‖ ≤ 1) : ‖T z‖ ≤ 1 := by
    obtain ⟨w, hw, heq⟩ := hBA ⟨z, mem_closedBall_zero_iff.mpr hzn, rfl⟩
    change ‖A.chart.symm (B.chart z)‖ ≤ 1
    rw [← heq, A.chart.left_inv (A.closedBall_subset_source hw)]
    exact mem_closedBall_zero_iff.mp hw
  have hn (y : E3) (hy : y ∈ V) (hyn : ‖y‖ = 1) :
      0 < ⟪y, fderiv ℝ T y y⟫_ℝ := by
    obtain ⟨L, hL⟩ := exists_smoothChart_derivative T hT hTi hy.2
    apply fderiv_normal_pos_of_local_interior T hyn hL.differentiableAt
    · filter_upwards [hV.mem_nhds hy] with z hz
      exact hfixed z hz
    · rw [hL.fderiv]
      exact L.injective
    · exact Filter.Eventually.of_forall hinner
  obtain ⟨F, hFfixed, hFball, hFclosed, hFnear, _hFsupport⟩ :=
    exists_sphere_fixed_patch_extension T hK hKS hV hKV
      (hT.mono inter_subset_right) hfixed hn
  let e := F.toHomeomorph.toOpenPartialHomeomorph.trans A.chart
  have hesource : closedBall (0 : E3) 1 ⊆ e.source := by
    intro y hy
    refine ⟨mem_univ _, A.closedBall_subset_source ?_⟩
    rw [← hFclosed]
    exact ⟨y, hy, rfl⟩
  let A' : BallNeighborhoodChart E3 E3 := {
    chart := e
    closedBall_subset_source := hesource
    smooth := A.smooth.comp F.contMDiff_toFun.contDiff.contDiffOn (fun _ hy => hy.2)
    smooth_symm := F.contMDiff_invFun.contDiff.comp_contDiffOn
      (A.smooth_symm.mono inter_subset_left) }
  have hAsource : A'.chart.source = F ⁻¹' A.chart.source := by
    ext y
    change (y ∈ (univ : Set E3) ∧ F y ∈ A.chart.source) ↔ F y ∈ A.chart.source
    simp only [mem_univ, true_and]
  have hAtarget : A'.chart.target = A.chart.target := by
    ext Y
    change (Y ∈ A.chart.target ∧ A.chart.symm Y ∈ (univ : Set E3)) ↔ Y ∈ A.chart.target
    simp only [mem_univ, and_true]
  have hAf (y : E3) : A'.chart y = A.chart (F y) := rfl
  have hAi (Y : E3) : A'.chart.symm Y = F.symm (A.chart.symm Y) := rfl
  have hinside : A'.inside = A.inside := by
    change (fun y => A.chart (F y)) '' ball (0 : E3) 1 = A.chart '' ball (0 : E3) 1
    rw [← image_image, hFball]
  have hclosed : A'.closedRegion = A.closedRegion := by
    change (fun y => A.chart (F y)) '' closedBall (0 : E3) 1 =
      A.chart '' closedBall (0 : E3) 1
    rw [← image_image, hFclosed]
  have hpointwise (y : E3) (hy : y ∈ sphere (0 : E3) 1) : A'.chart y = A.chart y := by
    rw [hAf, hFfixed y hy]
  have hboundary : A'.boundary = A.boundary := image_congr hpointwise
  have hTsnear : ∀ᶠ y in 𝓝ˢ K, y ∈ T.source :=
    T.open_source.mem_nhdsSet.mpr (fun _ hy => (hKV hy).2)
  refine ⟨F, hFfixed, hFball, hFclosed, hFnear, A', rfl, hAsource, hAtarget,
    hAf, hAi, hinside, hclosed, hboundary, hpointwise, ?_⟩
  filter_upwards [hFnear, hTsnear] with y hFy hyt
  have hactual : y ∈ B.chart.source ∧ B.chart y ∈ A.chart.target := hyt
  refine ⟨?_, hactual.1, ?_⟩
  · rw [hAsource]
    change F y ∈ A.chart.source
    rw [hFy]
    exact A.chart.map_target hactual.2
  · rw [hAf, hFy]
    exact A.chart.right_inv hactual.2

end PoincareConjecture.M25.Topology3D
