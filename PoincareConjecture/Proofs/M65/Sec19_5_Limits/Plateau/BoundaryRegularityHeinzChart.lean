import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityTargetChart
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerChartBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Boundary

open M65Euler

private theorem bounded_straight_chart_extension
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p)) (p : M)
    (E : OpenPartialHomeomorph LoopAmbient LoopAmbient)
    (hsource : (chartAt LoopAmbient p) p ∈ E.source)
    (hE : ContDiffOn ℝ ∞ E E.source) :
    ∃ (B : EuclideanSpace ℝ (Fin N) → LoopAmbient) (L : NNReal),
      ContDiff ℝ 1 B ∧ LipschitzWith L B ∧
        (∀ y, ‖fderiv ℝ B y‖ ≤ (L : ℝ)) ∧
        ∀ᶠ q in 𝓝 p, B (e q) = E ((chartAt LoopAmbient p) q) := by
  obtain ⟨H, C, hH, hHD, hHL, hHeq⟩ := exists_bounded_chart_extension e he hinj p
  have hHchart : ∀ᶠ q in 𝓝 p, H (e q) = (chartAt LoopAmbient p) q := by
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] using hHeq
  have hEH : ContDiffAt ℝ 1 E (H (e p)) := by
    rw [hHchart.self_of_nhds]
    exact (hE.contDiffAt (E.open_source.mem_nhds hsource)).of_le (by simp)
  obtain ⟨A, K, hA, hAD, hAeq⟩ := exists_bounded_extension hEH
  have hAL : LipschitzWith K A := lipschitzWith_of_nnnorm_fderiv_le
    (hA.differentiable one_ne_zero) (fun y => hAD y)
  refine ⟨A ∘ H, K * C, hA.comp hH, hAL.comp hHL, ?_, ?_⟩
  · intro y
    rw [fderiv_comp y (hA.differentiable one_ne_zero _) (hH.differentiable one_ne_zero _),
      NNReal.coe_mul]
    exact ((fderiv ℝ A (H y)).opNorm_comp_le _).trans
      (mul_le_mul (hAD _) (hHD _) (norm_nonneg _) K.coe_nonneg)
  · filter_upwards [(hH.continuous.comp he.continuous).continuousAt.eventually hAeq,
      hHchart] with q hAq hHq
    change A (H (e q)) = E ((chartAt LoopAmbient p) q)
    change A (H (e q)) = E (H (e q)) at hAq
    rw [hAq, hHq]

set_option maxHeartbeats 1400000 in

theorem continuous_boundary_straight_weak_chart
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    {R : ℝ} (hR : 0 < R) (F : M65LocalWeakMap e (ball (0 : LoopPlane) R))
    {q : LoopPlane → M} (hq : ContinuousOn q (closedBall (0 : LoopPlane) R))
    (hqAE : q =ᵐ[volume.restrict (ball (0 : LoopPlane) R)] F.value)
    (hqs : ContMDiffOn (𝓡 2) (𝓡 3) ∞ q
      (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (C : ℝ → M) (hC : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ C) (s : ℝ)
    (hregular : curveVelocity (n := 3) C s ≠ 0)
    (b : ℝ → ℝ) (hb : ContinuousAt b 0) (hb0 : b 0 = s)
    (htrace : ∀ t ∈ Icc (-R) R,
      q (t • EuclideanSpace.basisFun (Fin 2) ℝ 0) = C (b t)) :
    let c := chartAt LoopAmbient (C s)
    ∃ (j : Fin 3) (E : OpenPartialHomeomorph LoopAmbient LoopAmbient)
      (r : ℝ) (B : EuclideanSpace ℝ (Fin N) → LoopAmbient) (L : NNReal),
      0 < r ∧ r < R ∧ ContDiffOn ℝ ∞ E E.source ∧
      ContDiffOn ℝ ∞ E.symm E.target ∧
      ContDiff ℝ 1 B ∧ LipschitzWith L B ∧ (∀ y, ‖fderiv ℝ B y‖ ≤ (L : ℝ)) ∧
      MapsTo q (closedBall (0 : LoopPlane) r) c.source ∧
      MapsTo (c ∘ q) (closedBall (0 : LoopPlane) r) E.source ∧
      ∃ X : M65LocalWeakMap (id : LoopAmbient → LoopAmbient) (ball (0 : LoopPlane) r),
        (∀ z, X.value z = B (e (q z))) ∧
        (∀ i z, X.derivative i z = fderiv ℝ B (e (q z)) (F.derivative i z)) ∧
        EqOn X.value (E ∘ c ∘ q) (closedBall (0 : LoopPlane) r) ∧
        ContinuousOn X.value (closedBall (0 : LoopPlane) r) ∧
        ContDiffOn ℝ ∞ X.value (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}) ∧
        ∀ t ∈ Icc (-r) r,
          X.value (t • EuclideanSpace.basisFun (Fin 2) ℝ 0) =
            (b t - s) • EuclideanSpace.basisFun (Fin 3) ℝ j := by
  let c := chartAt LoopAmbient (C s)
  let I := C ⁻¹' c.source
  have hI : IsOpen I := c.open_source.preimage hC.continuous
  have hs : s ∈ I := mem_chart_source LoopAmbient (C s)
  have hc : ContDiffOn ℝ ∞ (c ∘ C) I :=
    (contMDiffOn_chart.comp hC.contMDiffOn (fun _ ht => ht)).contDiffOn
  have hcder : deriv (c ∘ C) s = mfderiv (𝓡 3) (𝓡 3) c (C s)
      (curveVelocity (n := 3) C s) := by
    have hh := congrArg (fun A : ℝ →L[ℝ] LoopAmbient => A 1)
      (mfderiv_comp s ((mdifferentiable_chart (I := 𝓡 3) (C s)).mdifferentiableAt hs)
        ((hC s).mdifferentiableAt (by simp)))
    simpa +instances only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      fderiv_apply_one_eq_deriv, curveVelocity, c] using! hh
  have hcne : deriv (c ∘ C) s ≠ 0 := by
    intro hz
    apply hregular
    apply ((mdifferentiable_chart (I := 𝓡 3) (C s)).mfderiv hs).injective
    change mfderiv (𝓡 3) (𝓡 3) c (C s) (curveVelocity (n := 3) C s) =
      mfderiv (𝓡 3) (𝓡 3) c (C s) 0
    rw [← hcder, hz, map_zero]
  obtain ⟨j, J, E, hJ, hsJ, _hJI, hsrc, _hzero, _hmap, hE, hEs, haxis, _hinv⟩ :=
    exists_boundary_arc_straightening hI hs hc hcne
  obtain ⟨B, L, hB, hLip, hBD, hBeq⟩ := bounded_straight_chart_extension e he hinj (C s) E hsrc hE
  have hq0 : q 0 = C s := by
    simpa only [zero_smul, hb0] using htrace 0 ⟨by linarith, hR.le⟩
  have hqAt : ContinuousAt q 0 := hq.continuousAt (closedBall_mem_nhds _ hR)
  have hcAt : ContinuousAt c (q 0) := by
    rw [hq0]
    exact c.continuousOn.continuousAt (c.open_source.mem_nhds hs)
  have hnear : ∀ᶠ z in 𝓝 (0 : LoopPlane),
      q z ∈ c.source ∧ c (q z) ∈ E.source ∧ B (e (q z)) = E (c (q z)) := by
    have ha : ∀ᶠ z in 𝓝 (0 : LoopPlane), q z ∈ c.source :=
      hqAt.eventually (by rw [hq0]; exact c.open_source.mem_nhds hs)
    have hb' : ∀ᶠ z in 𝓝 (0 : LoopPlane), c (q z) ∈ E.source :=
      (hcAt.comp hqAt).eventually (by
        change ∀ᶠ y in 𝓝 (c (q 0)), y ∈ E.source
        rw [hq0]
        exact E.open_source.mem_nhds hsrc)
    have hd : ∀ᶠ z in 𝓝 (0 : LoopPlane), B (e (q z)) = E (c (q z)) :=
      hqAt.eventually (by simpa only [hq0, c] using hBeq)
    exact ha.and (hb'.and hd)
  obtain ⟨eta, heta, hcap⟩ := Metric.mem_nhds_iff.mp hnear
  have hbJ : ∀ᶠ t in 𝓝 (0 : ℝ), b t ∈ J :=
    hb.eventually (by rw [hb0]; exact hJ.mem_nhds hsJ)
  obtain ⟨delta, hdelta, hbc⟩ := Metric.mem_nhds_iff.mp hbJ
  let r := min (R / 2) (min (eta / 2) (delta / 2))
  have hr : 0 < r := lt_min (half_pos hR) (lt_min (half_pos heta) (half_pos hdelta))
  have hrR : r < R := (min_le_left _ _).trans_lt (by linarith)
  have hre : r < eta := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hrd : r < delta := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  have hsmall (z : LoopPlane) (hz : z ∈ closedBall 0 r) :
      q z ∈ c.source ∧ c (q z) ∈ E.source ∧ B (e (q z)) = E (c (q z)) :=
    hcap (closedBall_subset_ball hre hz)
  let Fq := replace_value F q (hqAE.mono fun _ hz => congrArg e hz)
  let X := compose_on_ball Fq isOpen_ball 0 hr.le (closedBall_subset_ball hrR) B hB L hBD
  have hX (z : LoopPlane) : X.value z = B (e (q z)) := rfl
  have hXe : EqOn X.value (E ∘ c ∘ q) (closedBall (0 : LoopPlane) r) :=
    fun z hz => (hX z).trans (hsmall z hz).2.2
  have hU : ball (0 : LoopPlane) r ∩ {z | 0 < z 1} ⊆ closedBall (0 : LoopPlane) r :=
    inter_subset_left.trans ball_subset_closedBall
  have hXcont : ContinuousOn X.value (closedBall (0 : LoopPlane) r) :=
    (hB.continuous.comp_continuousOn (he.continuous.comp_continuousOn
      (hq.mono (closedBall_subset_closedBall hrR.le)))).congr (fun z _ => hX z)
  have hXsmooth : ContDiffOn ℝ ∞ X.value (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}) := by
    have hqc := (contMDiffOn_chart.comp
      (hqs.mono (inter_subset_inter_left _ (ball_subset_ball hrR.le)))
      (fun z hz => (hsmall z (hU hz)).1)).contDiffOn
    exact (hE.comp hqc (fun z hz => (hsmall z (hU hz)).2.1)).congr (hXe.mono hU)
  refine ⟨j, E, r, B, L, hr, hrR, hE, hEs, hB, hLip, hBD,
    (fun z hz => (hsmall z hz).1), (fun z hz => (hsmall z hz).2.1),
    X, hX, (fun _ _ => rfl), hXe, hXcont, hXsmooth, ?_⟩
  intro t ht
  have htn : ‖t • EuclideanSpace.basisFun (Fin 2) ℝ 0‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one]
    exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  rw [hXe (mem_closedBall_zero_iff.mpr htn)]
  change E (c (q (t • EuclideanSpace.basisFun (Fin 2) ℝ 0))) = _
  rw [htrace t ⟨by linarith [ht.1], by linarith [ht.2]⟩]
  exact haxis (b t) (hbc (show t ∈ ball (0 : ℝ) delta by
    rw [mem_ball_zero_iff, Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩).trans_lt hrd))

end PoincareConjecture.M65Boundary
