import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetUnframing
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetCauchyHolder
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceHalfDisk










noncomputable section

set_option autoImplicit false

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch





theorem gauged_halfDisk_unframed_residual_holder
    {n : ℕ} [Nonempty (Fin n)]
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B) (hsmall : 8 * R * B < 1 / 2)
    (hAC1 : ContDiffOn ℝ 1 A (ball (0 : ℂ) R ∩ {z | z.im ≠ 0}))
    {u : ℂ → Fin n → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    {L : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {r : ℝ} (hr : 0 < r)
    (hL : ContDiffOn ℝ 1 L (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hunit : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}, IsUnit (L z)) :
    let q := fun z => Ring.inverse (L z) (cauchyGauge A z (u z))
    ∃ d : ℝ, 0 < d ∧ d < min r R ∧
      ContinuousOn q (closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) ∧
      ContDiffOn ℝ 1 q (ball (0 : ℂ) d ∩ {z | 0 < z.im}) ∧
      (∀ z ∈ closedBall (0 : ℂ) d ∩ {w | 0 ≤ w.im}, q z ≠ 0) ∧
      MemLp (fun z => fderiv ℝ q z 1)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) ∧
      MemLp (fun z => fderiv ℝ q z I)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im},
        ∀ w ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im},
          ‖q z - q w‖ ≤ C * Real.sqrt ‖z - w‖ := by
  let E := Fin n → ℂ
  let Q := fun z => cauchyGauge A z (u z)
  let q := fun z => Ring.inverse (L z) (Q z)
  obtain ⟨d0, hd0, hd0R, hQc, hQne, hQ1, hQI⟩ :=
    cauchyGauge_analytic_residual_local_memLp hR hB hA hs hb hsmall hAC1 hu hu0
  obtain ⟨s, hs0, hsa⟩ := Metric.mem_nhds_iff.mp hu.eventually_analyticAt
  let d := min (min d0 r) s / 2
  have hd : 0 < d := half_pos (lt_min (lt_min hd0 hr) hs0)
  have hdd0 : d < d0 := (half_lt_self (lt_min (lt_min hd0 hr) hs0)).trans_le
    ((min_le_left _ _).trans (min_le_left _ _))
  have hdr : d < r := (half_lt_self (lt_min (lt_min hd0 hr) hs0)).trans_le
    ((min_le_left _ _).trans (min_le_right _ _))
  have hds : d < s := (half_lt_self (lt_min (lt_min hd0 hr) hs0)).trans_le
    (min_le_right _ _)
  let K := closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}
  let U := ball (0 : ℂ) d ∩ {z | 0 < z.im}
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) d).inter_right
    (isClosed_le continuous_const continuous_im)
  have hKU := (M65StrictTrace.halfDisk_differential_domain hd).2.2.1
  have hU : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hUK : U ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  have hKr : K ⊆ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter (closedBall_subset_closedBall hdr.le) Subset.rfl
  have hKd0 : K ⊆ closedBall (0 : ℂ) d0 :=
    inter_subset_left.trans (closedBall_subset_closedBall hdd0.le)
  have hLU : ContDiffOn ℝ 1 L U := hL.mono (hUK.trans hKr)
  have huC : ContDiffOn ℝ 1 u (ball (0 : ℂ) s) := fun z hz =>
    (((hsa hz).contDiffAt : ContDiffAt ℂ 1 u z).restrict_scalars ℝ).contDiffWithinAt
  have hUs : U ⊆ ball (0 : ℂ) s := inter_subset_left.trans (ball_subset_ball hds.le)
  have hUA : U ⊆ ball (0 : ℂ) R ∩ {z | z.im ≠ 0} := fun z hz =>
    ⟨ball_subset_ball (hdd0.trans hd0R).le hz.1, hz.2.ne'⟩
  have hAU : IsOpen (ball (0 : ℂ) R ∩ {z : ℂ | z.im ≠ 0}) :=
    isOpen_ball.inter (isOpen_ne_fun continuous_im continuous_const)
  have hGauge := (cauchyGauge_contDiffOn_of_C1_coefficient
    hR hB hA hs hb hsmall hAU hAC1).1.mono hUA
  let S := ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
  have hQU : ContDiffOn ℝ 1 Q U :=
    (S.contDiff.comp_contDiffOn hGauge).clm_apply (huC.mono hUs)
  have hQK : ContinuousOn Q K := hQc.mono hKd0
  have hInvK : ContinuousOn (fun z => Ring.inverse (L z)) K := by
    intro z hz
    obtain ⟨a, ha⟩ := hunit z (hKr hz)
    have hInv : ContDiffAt ℝ 1 Ring.inverse (L z) := by
      simpa only [ha] using contDiffAt_ringInverse ℝ (n := 1) a
    exact hInv.continuousAt.comp_continuousWithinAt ((hL.continuousOn.mono hKr) z hz)
  have hInvU : ContDiffOn ℝ 1 (fun z => Ring.inverse (L z)) U := by
    intro z hz
    obtain ⟨a, ha⟩ := hunit z (hKr (hUK hz))
    have hInv : ContDiffAt ℝ 1 Ring.inverse (L z) := by
      simpa only [ha] using contDiffAt_ringInverse ℝ (n := 1) a
    exact (hInv.comp z (hLU.contDiffAt (hU.mem_nhds hz))).contDiffWithinAt
  have hqC : ContinuousOn q K := hInvK.clm_apply hQK
  have hqU : ContDiffOn ℝ 1 q U :=
    (S.contDiff.comp_contDiffOn hInvU).clm_apply hQU
  have hqne (z : ℂ) (hz : z ∈ K) : q z ≠ 0 := by
    intro hzero
    apply hQne z (hKd0 hz)
    have he := congrArg (fun w => L z w) hzero
    change (L z * Ring.inverse (L z)) (Q z) = L z 0 at he
    rw [Ring.mul_inverse_cancel _ (hunit z (hKr hz))] at he
    simpa using he
  have hmem (v : ℂ) (hv : v = 1 ∨ v = I) :
      MemLp (fun z => fderiv ℝ q z v) 2 (volume.restrict U) := by
    have hraw : MemLp (fun z => fderiv ℝ Q z v) 2 (volume.restrict (K ∩ U)) := by
      have hsub : K ∩ U ⊆ closedBall (0 : ℂ) d0 ∩ {z | z.im ≠ 0} :=
        fun z hz => ⟨hKd0 hz.1, (show 0 < z.im from hz.2.2).ne'⟩
      have hraw0 : MemLp (fun z => fderiv ℝ Q z v) 2
          (volume.restrict (closedBall (0 : ℂ) d0 ∩ {z | z.im ≠ 0})) :=
        hv.elim (fun h => h ▸ hQ1) (fun h => h ▸ hQI)
      exact hraw0.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hh := inverse_frame_residual_derivative_memLp hK hKU hU hUK (hL.mono hKr)
      (fun z hz => hunit z (hKr hz)) hQK hQU v hraw
    simpa only [inter_eq_right.mpr hUK] using hh
  refine ⟨d, hd, lt_min hdr (hdd0.trans hd0R), hqC, hqU, hqne,
    hmem 1 (Or.inl rfl), hmem I (Or.inr rfl), ?_⟩
  exact cauchyGauge_unframed_halfDisk_holder hR hB hA hs hb hsmall hd
    (huC.mono (inter_subset_left.trans (closedBall_subset_ball hds)))
    (hL.mono hKr) (fun z hz => hunit z (hKr hz))





theorem gauged_halfDisk_unframed_residual
    {n : ℕ} [Nonempty (Fin n)]
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B) (hsmall : 8 * R * B < 1 / 2)
    (hAC1 : ContDiffOn ℝ 1 A (ball (0 : ℂ) R ∩ {z | z.im ≠ 0}))
    {u : ℂ → Fin n → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    {L : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {r : ℝ} (hr : 0 < r)
    (hL : ContDiffOn ℝ 1 L (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hunit : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}, IsUnit (L z)) :
    let q := fun z => Ring.inverse (L z) (cauchyGauge A z (u z))
    ∃ d : ℝ, 0 < d ∧ d < min r R ∧
      ContinuousOn q (closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) ∧
      ContDiffOn ℝ 1 q (ball (0 : ℂ) d ∩ {z | 0 < z.im}) ∧
      (∀ z ∈ closedBall (0 : ℂ) d ∩ {w | 0 ≤ w.im}, q z ≠ 0) ∧
      MemLp (fun z => fderiv ℝ q z 1)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) ∧
      MemLp (fun z => fderiv ℝ q z I)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) := by
  obtain ⟨d, hd, hdr, hc, hC1, hn, h1, hI, _⟩ :=
    gauged_halfDisk_unframed_residual_holder hR hB hA hs hb hsmall hAC1 hu hu0 hr hL hunit
  exact ⟨d, hd, hdr, hc, hC1, hn, h1, hI⟩

end PoincareConjecture.M65Branch
