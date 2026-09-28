import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerEquation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalHolder
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityTomiRegularity













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture.M65Euler

set_option maxHeartbeats 3000000 in






theorem weak_harmonic_contDiffAt {N : ℕ}
    {g : RiemannianMetric N (EuclideanSpace ℝ (Fin N))} (D : LeviCivitaData g)
    (x : LoopPlane) {R : ℝ} (hR : 0 < R)
    (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) (ball x (8 * R)))
    (hXc : ContinuousOn X.value (ball x (8 * R)))
    (a : EuclideanSpace ℝ (Fin N)) {ε : ℝ} (hε : 0 < ε)
    (hXcap : MapsTo X.value (ball x (8 * R)) (ball a (ε / 2)))
    (hEq : ∀ (k : Fin N) (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ →
      tsupport φ ⊆ ball x R →
      (∫ z in closedBall x (2 * R), ∑ i : Fin 2,
        fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * (X.derivative i z) k) =
        ∫ z in closedBall x (2 * R), φ z * ∑ i : Fin 2,
          (M65Gauss.connectionCoefficient D (X.value z)
            (X.derivative i z) (X.derivative i z)) k)
    {s β Λ : ℝ} (hs : 0 < s) (hsR : s ≤ R) (hβ : 0 < β) (hΛ : 0 ≤ Λ)
    (hdecay : ∀ y ∈ closedBall x (s / 2), ∀ r : ℝ, 0 < r → r ≤ s / 2 →
      (∫ z in closedBall y r, ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) ≤
        Λ * r ^ (2 * β)) : ContDiffAt ℝ 1 X.value x := by
  classical
  let K := closedBall x (2 * R)
  let U := ball x (s / 16)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKsub : K ⊆ ball x (8 * R) := closedBall_subset_ball (by linarith)
  have hUsub : U ⊆ K := (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith)))
  have hsSub : closedBall x s ⊆ ball x (8 * R) := closedBall_subset_ball (by linarith)
  obtain ⟨v, H, hH, hvc, hvAE, hholder⟩ :=
    X.local_holder_of_energy_decay isOpen_ball x hs hsSub hβ hΛ hdecay
  have hb8 : ball x (s / 8) ⊆ ball x (8 * R) := ball_subset_ball (by linarith)
  have heqv : EqOn X.value v (ball x (s / 8)) :=
    Measure.eqOn_open_of_ae_eq
      (ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hvAE.symm)
      isOpen_ball (hXc.mono hb8) (hvc.mono ball_subset_closedBall)
  have hU8 : U ⊆ ball x (s / 8) := ball_subset_ball (by linarith)
  have hHolder (y : LoopPlane) (hy : y ∈ U) (z : LoopPlane) (hz : z ∈ U) (j : Fin N) :
      |X.value z j - X.value y j| ≤ H * ‖z - y‖ ^ β := by
    have hcoord : |X.value z j - X.value y j| ≤ ‖X.value z - X.value y‖ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
        PiLp.norm_apply_le (X.value z - X.value y) j
    apply hcoord.trans
    rw [heqv (hU8 hz), heqv (hU8 hy)]
    simpa only [dist_eq_norm] using
      hholder y (ball_subset_closedBall (hU8 hy)) z (ball_subset_closedBall (hU8 hz))
  obtain ⟨θ, hθc, hθs, hθ⟩ := M65Interior.exists_disk_cutoff isOpen_ball x
    (show 0 ≤ 2 * R by positivity) hKsub
  choose u d hu hd hw using fun j : Fin N => X.cutoff_global j θ hθc hθs
  have huK (j : Fin N) : (u j : LoopPlane → ℝ) =ᵐ[volume.restrict K]
      fun z => X.value z j := by
    filter_upwards [ae_restrict_of_ae (hu j), ae_restrict_mem hK.measurableSet] with z hz hzK
    rw [hz, (hθ z hzK).2.1, one_mul]
  have hdK (j : Fin N) (i : Fin 2) : (d j i : LoopPlane → ℝ) =ᵐ[volume.restrict K]
      fun z => X.derivative i z j := by
    filter_upwards [ae_restrict_of_ae (hd j i), ae_restrict_mem hK.measurableSet] with z hz hzK
    rw [hz, (hθ z hzK).2.1, (hθ z hzK).2.2]
    simp only [one_mul, zero_apply, zero_mul, add_zero]
  have hsumK : (fun z => ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2)
      =ᵐ[volume.restrict K] fun z => ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2 := by
    filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (hdK j))] with z hz
    simp only [hz]
    rw [Finset.sum_comm]
    simp only [EuclideanSpace.real_norm_sq_eq]
  obtain ⟨Bθ, hBθ⟩ := hθc.exists_bound_of_continuous θ.continuous
  let B := max Bθ 0 * (‖a‖ + ε)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hub (j : Fin N) : ∀ᵐ z ∂volume, ‖u j z‖ ≤ B := by
    filter_upwards [hu j] with z hz
    rw [hz]
    by_cases hzt : z ∈ tsupport θ
    · have hn : ‖X.value z‖ ≤ ‖a‖ + ε :=
        (norm_le_of_mem_closedBall (ball_subset_closedBall (hXcap (hθs hzt)))).trans
          (by linarith)
      rw [norm_mul]
      exact mul_le_mul ((hBθ z).trans (le_max_left _ _))
        ((PiLp.norm_apply_le (X.value z) j).trans hn) (norm_nonneg _) (le_max_right _ _)
    · rw [image_eq_zero_of_notMem_tsupport hzt, zero_mul, norm_zero]
      exact hB
  let Q := fun (j : Fin N) z => ∑ i : Fin 2,
    (M65Gauss.connectionCoefficient D (X.value z) (X.derivative i z) (X.derivative i z)) j
  let f := fun j => K.indicator (fun z => -Q j z)
  have hXm := X.value_memLp K hK hKsub
  have hAm (i : Fin 2) := X.derivative_memLp i K hK hKsub
  have hcap : ∀ᵐ z ∂volume.restrict K, X.value z ∈ closedBall a (ε / 2) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact ball_subset_closedBall (hXcap (hKsub hz))
  have hQI (j : Fin N) : IntegrableOn (Q j) K := by
    apply integrable_finsetSum
    intro i _
    exact (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp
      (connection_quadratic_integrable D X.value (X.derivative i) hXm.1 (hAm i)
        (isCompact_closedBall _ _) hcap)
  have hfI (j : Fin N) : Integrable (f j) :=
    (integrable_indicator_iff hK.measurableSet).mpr (hQI j).neg
  have hfs (j : Fin N) : Function.support (f j) ⊆ closedBall (0 : LoopPlane) (‖x‖ + 2 * R) := by
    apply Set.support_indicator_subset.trans
    exact closedBall_subset_closedBall' (by rw [dist_zero_right]; linarith)
  have hweak : ∀ j i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d j i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)) := by
    simpa only [EuclideanSpace.basisFun_apply] using hw
  have hEq0 (j : Fin N) (φ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport φ)
      (hφ : tsupport φ ⊆ U) :
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f j z * φ z) := by
    have hφK := hφ.trans hUsub
    have hterm (i : Fin 2) :
        ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ =
          ∫ z in K, fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * X.derivative i z j := by
      rw [DeTurckDomainRegularityNative.inner_schwartz]
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (fun z hz => by
        rw [fderiv_of_notMem_tsupport ℝ (fun ht => hz (hφK ht)), zero_apply, mul_zero])]
      apply integral_congr_ae
      filter_upwards [hdK j i] with z hz
      rw [hz, EuclideanSpace.basisFun_apply, mul_comm]
    have hterms (i : Fin 2) : IntegrableOn
        (fun z => fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * X.derivative i z j) K :=
      (((∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} φ).memLp 2 volume).restrict K).integrable_mul
        ((hAm i).eval_piLp j)
    have hfEq : (fun z => f j z * φ z) = K.indicator (fun z => -(φ z * Q j z)) := by
      funext z
      by_cases hz : z ∈ K
      · simp only [f, indicator_of_mem hz]
        ring
      · simp only [f, indicator_of_notMem hz, zero_mul]
    simp_rw [hterm]
    rw [← integral_finsetSum _ (fun i _ => hterms i), hfEq,
      integral_indicator hK.measurableSet, integral_neg, neg_neg]
    exact hEq j φ hc (hφ.trans (ball_subset_ball (by linarith)))
  obtain ⟨C, hC, hcoef⟩ := connection_quadratic_bound D (isCompact_closedBall a (ε / 2))
  have hgrowth (j : Fin N) : ∀ᵐ z ∂volume, z ∈ U →
      |f j z| ≤ C * (∑ k : Fin N, ∑ i : Fin 2, (d k i z) ^ 2) := by
    filter_upwards [(ae_restrict_iff' hK.measurableSet).mp hsumK] with z hz hzU
    have hzK := hUsub hzU
    rw [hz hzK, show f j z = -Q j z from indicator_of_mem hzK _, abs_neg]
    change |∑ i : Fin 2,
      (M65Gauss.connectionCoefficient D (X.value z) (X.derivative i z) (X.derivative i z)) j| ≤ _
    calc
      _ ≤ ∑ i : Fin 2,
          |(M65Gauss.connectionCoefficient D (X.value z)
            (X.derivative i z) (X.derivative i z)) j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 2, C * ‖X.derivative i z‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hn : |(M65Gauss.connectionCoefficient D (X.value z)
            (X.derivative i z) (X.derivative i z)) j| ≤
              ‖M65Gauss.connectionCoefficient D (X.value z)
                (X.derivative i z) (X.derivative i z)‖ := by
          simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le
            (M65Gauss.connectionCoefficient D (X.value z)
              (X.derivative i z) (X.derivative i z)) j)
        exact hn.trans (hcoef _ (ball_subset_closedBall (hXcap (hKsub hzK))) _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hv (j : Fin N) : ContinuousOn (fun z => X.value z j) U :=
    (by fun_prop : Continuous (fun y : EuclideanSpace ℝ (Fin N) => y j)).comp_continuousOn
      (hXc.mono (hUsub.trans hKsub))
  have huv (j : Fin N) : (u j : LoopPlane → ℝ) =ᵐ[volume.restrict U]
      fun z => X.value z j := ae_restrict_of_ae_restrict_of_subset hUsub (huK j)
  have hdecay0 (y : LoopPlane) (hy : y ∈ ball x (s / 16)) (r : ℝ)
      (hr : 0 < r) (hrsmall : r ≤ s / 16) :
      (∫ z in closedBall y r, ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) ≤
        Λ * r ^ (2 * β) := by
    have hsub : closedBall y r ⊆ K := closedBall_subset_closedBall' (by
      have hy' : dist y x < s / 16 := hy
      linarith)
    rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hsub hsumK)]
    exact hdecay y (ball_subset_closedBall
      (ball_subset_ball (by linarith : s / 16 ≤ s / 2) hy)) r hr (by linarith)
  have hC1 := M65Boundary.quadratic_holder_contDiffAt u d f
    (fun j z => X.value z j) hfI isOpen_ball hfs hweak hEq0 hC hH.le hβ hΛ
    (show 0 < s / 16 by positivity) hgrowth hub hv huv hHolder
    (mem_ball_self (show 0 < s / 16 by positivity)) hdecay0
  exact contDiffAt_euclidean.mpr hC1

end PoincareConjecture.M65Euler
