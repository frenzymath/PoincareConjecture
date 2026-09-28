import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ChartReaderCenteredInverseTwoSided
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.C2CurveStraightening
import PoincareConjecture.Proofs.M64.Mathlib.C2BoundedExtension

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

theorem m64ChartReadable_bounded_C2_boundary_chart {n m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    (e : M → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 (n + 1)) (𝓡 m) ∞ e) (hemb : Topology.IsEmbedding e)
    (hread : M60.SUChartReadable (n := n + 1) e)
    (C : ℝ → M) (hC : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 (n + 1)) 2 C)
    (hregular : curveVelocity (n := n + 1) C 0 ≠ 0)
    {O : Set M} (hO : IsOpen O) (hCO : C 0 ∈ O) :
    ∃ (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin (n + 1)))
      (A : EuclideanSpace ℝ (Fin (n + 1)) → M) (L : NNReal) (rho delta eta K : ℝ),
      0 < rho ∧ 0 < delta ∧ 0 < eta ∧ eta ≤ rho / 4 ∧ 0 < K ∧
      H (e (C 0)) = 0 ∧ A 0 = C 0 ∧
      ContDiff ℝ 2 H ∧ LipschitzWith L H ∧
      (∀ y, ‖fderiv ℝ H y‖ ≤ K ∧ ‖fderiv ℝ (fderiv ℝ H) y‖ ≤ K) ∧
      ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) 2 A (ball 0 (2 * rho)) ∧
      MapsTo A (ball 0 (2 * rho)) O ∧
      (∀ y ∈ ball 0 (2 * rho), H (e (A y)) = y) ∧
      (∀ y ∈ closedBall 0 rho, ‖fderiv ℝ (e ∘ A) y‖ ≤ K) ∧
      (∀ q : M, dist (e q) (e (C 0)) < delta →
        ‖H (e q)‖ < rho / 4 ∧ A (H (e q)) = q) ∧
      ∀ t ∈ Ioo (-eta) eta,
        H (e (C t)) = EuclideanSpace.single 0 t ∧
        A (EuclideanSpace.single 0 t) = C t := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  obtain ⟨T, P, hP0, hP, hPinv, hPright⟩ :=
    m64ChartReadable_centered_inverse_two_sided hread (C 0)
  let c := fun t : ℝ => T (e (C t) - e (C 0))
  have hc : ContDiff ℝ 2 c :=
    T.contDiff.comp (((he.of_le (WithTop.coe_le_coe.mpr le_top)).comp hC).contDiff.sub
      contDiff_const)
  have hc0 : c 0 = 0 := by simp [c]
  have hPC : (P ∘ c) =ᶠ[𝓝 0] C := hC.continuous.continuousAt.eventually hPinv
  have hcne : deriv c 0 ≠ 0 := by
    intro hz
    apply hregular
    have hPc : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ P (c 0) := hc0.symm ▸ hP
    have h := congrArg (fun D : ℝ →L[ℝ] E => D 1)
      (mfderiv_comp 0 (hPc.mdifferentiableAt (by simp))
        (hc.contMDiff.contMDiffAt.mdifferentiableAt (by norm_num)))
    rw [hPC.mfderiv_eq, mfderiv_eq_fderiv] at h
    change curveVelocity C 0 = mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) P (c 0)
      (fderiv ℝ c 0 1) at h
    rwa [fderiv_apply_one_eq_deriv, hz, map_zero] at h
  obtain ⟨J, hJ0, -, hJzero, hJ, hJi, haxis⟩ :=
    m64_exists_C2_curve_straightening hc hcne isOpen_univ (mem_univ _)
  have hJz : J 0 = 0 := hJzero.trans hc0
  have hJt : (0 : E) ∈ J.target := hJz ▸ J.map_source hJ0
  have hJiz : J.symm 0 = 0 := by simpa only [hJz] using J.left_inv hJ0
  let coordinate := fun y => J.symm (T (y - e (C 0)))
  have hcoord : ContDiffAt ℝ 2 coordinate (e (C 0)) := by
    have hJiAt : ContDiffAt ℝ 2 J.symm (T (e (C 0) - e (C 0))) := by
      simpa only [sub_self, map_zero] using hJi.contDiffAt (J.open_target.mem_nhds hJt)
    exact hJiAt.comp (e (C 0))
      (T.contDiff.contDiffAt.comp (e (C 0)) (contDiffAt_id.sub contDiffAt_const))
  obtain ⟨H, B, hB, hH, -, hHD, hHeq⟩ := m64C2_exists_bounded_extension hcoord
  let L : NNReal := ⟨B, hB.le⟩
  have hLip : LipschitzWith L H := lipschitzWith_of_nnnorm_fderiv_le
    (hH.differentiable (by norm_num)) (fun y => by exact_mod_cast (hHD y).1)
  have hH0 : H (e (C 0)) = 0 := by
    rw [hHeq.self_of_nhds]
    simpa only [coordinate, sub_self, map_zero] using hJiz
  let A := P ∘ J
  have hA0 : A 0 = C 0 := by simp only [A, Function.comp_apply, hJz, hP0]
  have hA : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)) 2 A 0 := by
    have hPJ : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)) 2 P (J 0) :=
      hJz.symm ▸ hP.of_le (WithTop.coe_le_coe.mpr le_top)
    exact hPJ.comp 0 (hJ.contDiffAt (J.open_source.mem_nhds hJ0)).contMDiffAt
  obtain ⟨W, hW, hAW⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hA
  have heA : ContDiffAt ℝ 2 (e ∘ A) 0 :=
    contMDiffAt_iff_contDiffAt.mp
      ((he.of_le (WithTop.coe_le_coe.mpr le_top)).contMDiffAt.comp 0 hA)
  have hJlim : Tendsto J (𝓝 (0 : E)) (𝓝 0) := by
    simpa only [ContinuousAt, hJz] using
      (hJ.contDiffAt (J.open_source.mem_nhds hJ0)).continuousAt
  have heAlim : Tendsto (e ∘ A) (𝓝 (0 : E)) (𝓝 (e (C 0))) := by
    simpa only [ContinuousAt, Function.comp_apply, hA0] using heA.continuousAt
  have hAright : ∀ᶠ y in 𝓝 (0 : E), H (e (A y)) = y := by
    filter_upwards [heAlim.eventually hHeq, hJlim.eventually hPright,
      J.open_source.mem_nhds hJ0] with y hy hPy hyJ
    dsimp only [Function.comp_apply] at hy
    rw [hy]
    change J.symm (T (e (P (J y)) - e (C 0))) = y
    rw [hPy, J.left_inv hyJ]
  let K0 := ‖fderiv ℝ (e ∘ A) 0‖ + 1
  have hK0 : 0 < K0 := by dsimp only [K0]; positivity
  have hKn : ∀ᶠ y in 𝓝 (0 : E), ‖fderiv ℝ (e ∘ A) y‖ < K0 :=
    (heA.fderiv_right (m := 1) (by norm_num)).continuousAt.norm.eventually
      (Iio_mem_nhds (by dsimp only [K0]; linarith))
  have hAO : A ⁻¹' O ∈ 𝓝 (0 : E) :=
    hA.continuousAt.preimage_mem_nhds (hO.mem_nhds (hA0.symm ▸ hCO))
  obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem hW hKn) (inter_mem hAO hAright))
  let rho := r / 3
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hball : ball (0 : E) (2 * rho) ⊆ ball 0 r :=
    ball_subset_ball (by dsimp only [rho]; linarith)
  have hclosed : closedBall (0 : E) rho ⊆ ball 0 r :=
    closedBall_subset_ball (by dsimp only [rho]; linarith)
  have hAOn : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) 2 A (ball 0 (2 * rho)) :=
    hAW.mono (fun y hy => (hrW (hball hy)).1.1)
  have hTcont : Continuous (fun q : M => T (e q - e (C 0))) :=
    T.continuous.comp (he.continuous.sub continuous_const)
  have hnearJ : ∀ᶠ q in 𝓝 (C 0), T (e q - e (C 0)) ∈ J.target := by
    apply hTcont.continuousAt.preimage_mem_nhds
    simpa only [sub_self, map_zero] using J.open_target.mem_nhds hJt
  have hinverse : ∀ᶠ q in 𝓝 (C 0), A (H (e q)) = q := by
    filter_upwards [he.continuous.continuousAt.eventually hHeq, hPinv, hnearJ]
      with q hh hq hqJ
    rw [hh]
    change P (J (J.symm (T (e q - e (C 0))))) = q
    rw [J.right_inv hqJ, hq]
  have hinverse' : ∀ᶠ y in 𝓝 (e (C 0)), ∀ q : M, e q = y → A (H (e q)) = q := by
    rw [hemb.isInducing.nhds_eq_comap (C 0), Filter.eventually_comap] at hinverse
    exact hinverse
  have hsmall : ∀ᶠ y in 𝓝 (e (C 0)), ‖H y‖ < rho / 4 := by
    have hzero : ‖H (e (C 0))‖ < rho / 4 := by rw [hH0, norm_zero]; positivity
    exact hH.continuous.continuousAt.norm.eventually (Iio_mem_nhds hzero)
  obtain ⟨delta, hdelta, hcap⟩ := Metric.mem_nhds_iff.mp (hinverse'.and hsmall)
  have hnearAxis : ∀ᶠ t in 𝓝 (0 : ℝ), (EuclideanSpace.single 0 t : E) ∈ J.source := by
    have hline : Continuous (fun t : ℝ => (EuclideanSpace.single 0 t : E)) := by
      have hsingle (t : ℝ) : (EuclideanSpace.single 0 t : E) =
          t • EuclideanSpace.single 0 1 := by
        ext j
        by_cases hj : j = 0 <;> simp [hj]
      exact (continuous_id.smul continuous_const).congr fun t => (hsingle t).symm
    apply hline.continuousAt.preimage_mem_nhds
    have hzero : (EuclideanSpace.single 0 0 : E) = 0 := by ext j; simp
    simpa only [hzero] using J.open_source.mem_nhds hJ0
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ),
      H (e (C t)) = EuclideanSpace.single 0 t ∧ A (EuclideanSpace.single 0 t) = C t := by
    filter_upwards [hnearAxis, (he.continuous.comp hC.continuous).continuousAt.eventually
      hHeq, hPC] with t ht hHt hPt
    dsimp only [Function.comp_apply] at hHt
    refine ⟨?_, ?_⟩
    · rw [hHt]
      change J.symm (c t) = EuclideanSpace.single 0 t
      rw [← haxis t, J.left_inv ht]
    · change P (J (EuclideanSpace.single 0 t)) = C t
      rw [haxis t]
      exact hPt
  obtain ⟨eta0, heta0, heta⟩ := Metric.mem_nhds_iff.mp htarget
  let eta := min eta0 (rho / 4)
  let K := B + K0 + 1
  refine ⟨H, A, L, rho, delta, eta, K, hrho, hdelta,
    lt_min heta0 (by positivity), min_le_right _ _, by dsimp only [K]; positivity,
    hH0, hA0, hH, hLip, ?_, hAOn, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    have hBK : B ≤ K := by dsimp only [K]; linarith
    exact ⟨(hHD y).1.trans hBK, (hHD y).2.trans hBK⟩
  · intro y hy
    exact (hrW (hball hy)).2.1
  · intro y hy
    exact (hrW (hball hy)).2.2
  · intro y hy
    exact (hrW (hclosed hy)).1.2.le.trans (by dsimp only [K]; linarith)
  · intro q hq
    have hh := hcap (show e q ∈ ball (e (C 0)) delta from hq)
    exact ⟨hh.2, hh.1 q rfl⟩
  · intro t ht
    apply heta
    rw [mem_ball, Real.dist_eq, sub_zero]
    exact (abs_lt.mpr ht).trans_le (min_le_left _ _)

end PoincareConjecture
