import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalCutoff
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityTomiRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture.M65Boundary

set_option maxHeartbeats 2000000 in

theorem local_quadratic_contDiffOn {N : ℕ} (p : LoopPlane) {R : ℝ} (hR : 0 < R)
    (Y : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) (ball p (8 * R)))
    (hYc : ContinuousOn Y.value (ball p (8 * R)))
    (f : Fin N → LoopPlane → ℝ) (hf : ∀ j, IntegrableOn (f j) (ball p (8 * R)))
    (heq : ∀ j (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ →
      tsupport φ ⊆ ball p (8 * R) →
      (∫ z in ball p (8 * R), ∑ i : Fin 2,
        Y.derivative i z j * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
          -(∫ z in ball p (8 * R), f j z * φ z))
    {C H beta Λ : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hb : 0 < beta) (hΛ : 0 ≤ Λ)
    (hgrowth : ∀ j, ∀ᵐ z ∂volume.restrict (ball p (8 * R)),
      |f j z| ≤ C * ∑ i : Fin 2, ‖Y.derivative i z‖ ^ 2)
    (hholder : ∀ x ∈ ball p (8 * R), ∀ z ∈ ball p (8 * R),
      ‖Y.value z - Y.value x‖ ≤ H * dist z x ^ beta)
    (hdecay : ∀ y ∈ ball p (2 * R), ∀ r : ℝ, 0 < r → r ≤ R →
      (∫ z in closedBall y r, ∑ i : Fin 2, ‖Y.derivative i z‖ ^ 2) ≤
        Λ * r ^ (2 * beta)) :
    ContDiffOn ℝ 1 Y.value (ball p R) := by
  classical
  let W := ball p (8 * R)
  let K := closedBall p (4 * R)
  let U := ball p (2 * R)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKW : K ⊆ W := closedBall_subset_ball (by linarith)
  have hUK : U ⊆ K := ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hUW : U ⊆ W := hUK.trans hKW
  obtain ⟨θ, hθc, hθs, hθ⟩ := M65Interior.exists_disk_cutoff isOpen_ball p
    (show 0 ≤ 4 * R by positivity) hKW
  choose u d hu hd hw using fun j : Fin N => Y.cutoff_global j θ hθc hθs
  have huK (j : Fin N) : (u j : LoopPlane → ℝ) =ᵐ[volume.restrict K]
      fun z => Y.value z j := by
    filter_upwards [ae_restrict_of_ae (hu j), ae_restrict_mem hK.measurableSet] with z hz hzK
    rw [hz, (hθ z hzK).2.1, one_mul]
  have hdK (j : Fin N) (i : Fin 2) : (d j i : LoopPlane → ℝ) =ᵐ[volume.restrict K]
      fun z => Y.derivative i z j := by
    filter_upwards [ae_restrict_of_ae (hd j i), ae_restrict_mem hK.measurableSet] with z hz hzK
    rw [hz, (hθ z hzK).2.1, (hθ z hzK).2.2]
    simp only [one_mul, zero_apply, zero_mul, add_zero]
  have hsumK : (fun z => ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2)
      =ᵐ[volume.restrict K] fun z => ∑ i : Fin 2, ‖Y.derivative i z‖ ^ 2 := by
    filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (hdK j))] with z hz
    simp only [hz]
    rw [Finset.sum_comm]
    simp only [EuclideanSpace.real_norm_sq_eq]
  obtain ⟨Bθ, hBθ⟩ := hθc.exists_bound_of_continuous θ.continuous
  obtain ⟨V, hV⟩ := hθc.exists_bound_of_continuousOn (hYc.mono hθs)
  let B := max Bθ 0 * max V 0
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hub (j : Fin N) : ∀ᵐ z ∂volume, ‖u j z‖ ≤ B := by
    filter_upwards [hu j] with z hz
    rw [hz]
    by_cases hzt : z ∈ tsupport θ
    · rw [norm_mul]
      exact mul_le_mul ((hBθ z).trans (le_max_left _ _))
        ((PiLp.norm_apply_le (Y.value z) j).trans ((hV z hzt).trans (le_max_left _ _)))
        (norm_nonneg _) (le_max_right _ _)
    · rw [image_eq_zero_of_notMem_tsupport hzt, zero_mul, norm_zero]
      exact hB
  let F := fun j => K.indicator (f j)
  have hFI (j : Fin N) : Integrable (F j) :=
    (integrable_indicator_iff hK.measurableSet).mpr ((hf j).mono_set hKW)
  have hFs (j : Fin N) : Function.support (F j) ⊆
      closedBall (0 : LoopPlane) (‖p‖ + 4 * R) := by
    apply Set.support_indicator_subset.trans
    exact closedBall_subset_closedBall' (by rw [dist_zero_right]; linarith)
  have hweak : ∀ j i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d j i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)) := by
    simpa only [EuclideanSpace.basisFun_apply] using hw
  have hAm (i : Fin 2) := Y.derivative_memLp i K hK hKW
  have hEq0 (j : Fin N) (φ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport φ)
      (hs : tsupport φ ⊆ U) :
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, F j z * φ z) := by
    have hsK := hs.trans hUK
    have hterm (i : Fin 2) :
        ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ =
          ∫ z in K, Y.derivative i z j *
            fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
      rw [DeTurckDomainRegularityNative.inner_schwartz]
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (fun z hz => by
        rw [fderiv_of_notMem_tsupport ℝ (fun ht => hz (hsK ht)), zero_apply, mul_zero])]
      apply integral_congr_ae
      filter_upwards [hdK j i] with z hz
      rw [hz, EuclideanSpace.basisFun_apply]
    have hterms (i : Fin 2) : IntegrableOn
        (fun z => Y.derivative i z j *
          fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) K :=
      ((hAm i).eval_piLp j).integrable_mul
        (((∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} φ).memLp 2 volume).restrict K)
    have hFEq : (fun z => F j z * φ z) = K.indicator (fun z => f j z * φ z) := by
      funext z
      by_cases hz : z ∈ K
      · simp only [F, indicator_of_mem hz]
      · simp only [F, indicator_of_notMem hz, zero_mul]
    have hleft : (∫ z in W, ∑ i : Fin 2, Y.derivative i z j *
        fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
        ∫ z in K, ∑ i : Fin 2, Y.derivative i z j *
          fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hKW
      intro z hz
      simp only [fderiv_of_notMem_tsupport ℝ (fun ht => hz.2 (hsK ht)), zero_apply,
        mul_zero, Finset.sum_const_zero]
    have hright : (∫ z in W, f j z * φ z) = ∫ z in K, f j z * φ z := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hKW
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hz.2 (hsK ht)), mul_zero]
    have h := heq j φ hc (hs.trans hUW)
    rw [hleft, hright] at h
    simp_rw [hterm]
    rw [← integral_finsetSum _ (fun i _ => hterms i), hFEq, integral_indicator hK.measurableSet]
    exact h
  have hG (j : Fin N) : ∀ᵐ z ∂volume, z ∈ U →
      |F j z| ≤ C * ∑ k : Fin N, ∑ i : Fin 2, (d k i z) ^ 2 := by
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp (hgrowth j),
      (ae_restrict_iff' hK.measurableSet).mp hsumK] with z hg hz hzU
    rw [hz (hUK hzU), show F j z = f j z from indicator_of_mem (hUK hzU) _]
    exact hg (hUW hzU)
  have hv (j : Fin N) : ContinuousOn (fun z => Y.value z j) U :=
    (by fun_prop : Continuous (fun y : EuclideanSpace ℝ (Fin N) => y j)).comp_continuousOn
      (hYc.mono hUW)
  have huv (j : Fin N) : (u j : LoopPlane → ℝ) =ᵐ[volume.restrict U]
      fun z => Y.value z j := ae_restrict_of_ae_restrict_of_subset hUK (huK j)
  have hHlocal (x : LoopPlane) (hx : x ∈ U) (z : LoopPlane) (hz : z ∈ U) (j : Fin N) :
      |Y.value z j - Y.value x j| ≤ H * ‖z - x‖ ^ beta := by
    have hcoord : |Y.value z j - Y.value x j| ≤ ‖Y.value z - Y.value x‖ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
        PiLp.norm_apply_le (Y.value z - Y.value x) j
    exact hcoord.trans (by simpa only [dist_eq_norm] using hholder x (hUW hx) z (hUW hz))
  intro q hq
  have hqU : q ∈ U := ball_subset_ball (by linarith : R ≤ 2 * R) hq
  have hdecay0 (y : LoopPlane) (hy : y ∈ ball q R) (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
      (∫ z in closedBall y r, ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) ≤
        Λ * r ^ (2 * beta) := by
    have hyq : dist y q < R := hy
    have hqp : dist q p < R := hq
    have hyp : dist y p < 2 * R := by linarith [dist_triangle y q p]
    have hsub : closedBall y r ⊆ K := closedBall_subset_closedBall' (by linarith)
    rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hsub hsumK)]
    exact hdecay y hyp r hr hrR
  have hC1 := quadratic_holder_contDiffAt u d F (fun j z => Y.value z j)
    hFI isOpen_ball hFs hweak hEq0 hC hH hb hΛ hR hG hub hv huv hHlocal hqU hdecay0
  exact (contDiffAt_euclidean.mpr hC1).contDiffWithinAt

end PoincareConjecture.M65Boundary
