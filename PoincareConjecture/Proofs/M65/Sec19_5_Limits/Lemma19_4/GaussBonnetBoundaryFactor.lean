import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetHalfDiskResidual
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.HartmanWintner

noncomputable section

set_option autoImplicit false

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

theorem halfDisk_differential_factor_holder
    {n : ℕ} [Nonempty (Fin n)]
    (J : (Fin n → ℂ) ≃ₗᵢ[ℝ] (Fin n → ℂ))
    (hJ : ∀ (s : ℂ) v, J (s • v) = star s • J v) (hJJ : Function.Involutive J)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    {L : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hHi : ContDiffOn ℝ ∞ H (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hL : ContDiffOn ℝ 1 L (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hunit : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}, IsUnit (L z))
    (hA : ContinuousOn A (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hAi : ContDiffOn ℝ 1 A (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (heq : ∀ z ∈ ball (0 : ℂ) r, 0 < z.im →
      dbar (fun w => L w (M65StrictTrace.halfDiskGradient H r w)) z =
        A z (L z (M65StrictTrace.halfDiskGradient H r z)))
    (hreal : ∀ z ∈ closedBall (0 : ℂ) r, z.im = 0 →
      J (L z (M65StrictTrace.halfDiskGradient H r z)) =
        L z (M65StrictTrace.halfDiskGradient H r z))
    (hnot : ¬∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0,
      fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z = 0) :
    ∃ (d : ℝ) (m : ℕ) (q : ℂ → Fin n → ℂ), 0 < d ∧ d < r ∧
      ContinuousOn q (closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) ∧
      ContDiffOn ℝ 1 q (ball (0 : ℂ) d ∩ {z | 0 < z.im}) ∧
      (∀ z ∈ closedBall (0 : ℂ) d ∩ {w | 0 ≤ w.im}, q z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) d ∩ {w | 0 ≤ w.im},
        M65StrictTrace.halfDiskGradient H r z = z ^ m • q z) ∧
      MemLp (fun z => fderiv ℝ q z 1)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) ∧
      MemLp (fun z => fderiv ℝ q z I)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im},
        ∀ w ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im},
          ‖q z - q w‖ ≤ C * Real.sqrt ‖z - w‖ := by
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let U := ball (0 : ℂ) r ∩ {z | 0 < z.im}
  let F := fun z => L z (M65StrictTrace.halfDiskGradient H r z)
  have hKU := M65StrictTrace.halfDisk_differential_domain hr
  have hUK : U ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  have hDc := hH.continuousOn_fderivWithin hKU.2.2.1 le_rfl
  have hGc : ContinuousOn (M65StrictTrace.halfDiskGradient H r) K :=
    (coordinateComplexification.continuous.comp_continuousOn
      (hDc.clm_apply continuousOn_const)).sub
        ((coordinateComplexification.continuous.comp_continuousOn
          (hDc.clm_apply continuousOn_const)).const_smul I)
  have hGi : ContDiffOn ℝ 1 (M65StrictTrace.halfDiskGradient H r) U := by
    apply (contDiffOn_complexGradient hKU.1 hHi).congr
    intro z hz
    simp only [M65StrictTrace.halfDiskGradient,
      fderivWithin_of_mem_nhds (M65StrictTrace.halfDisk_mem_nhds hz), complexGradient]
  have hFc : ContinuousOn F K := hL.continuousOn.clm_apply hGc
  let S := ContinuousLinearMap.restrictScalarsL ℂ (Fin n → ℂ) (Fin n → ℂ) ℝ ℝ
  have hFi : ContDiffOn ℝ 1 F U :=
    (S.contDiff.comp_contDiffOn (hL.mono hUK)).clm_apply hGi
  obtain ⟨A0, R, B, hR, hRr, hB, hA0, hs0, hb0, hsmall, hA0i, _, hcases⟩ :=
    exists_half_disk_power_factor J hJ hJJ hr hFc hFi hA hAi heq hreal
  have hnearK : ∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0, z ∈ K := by
    have hball : ∀ᶠ z : ℂ in 𝓝 0, z ∈ ball (0 : ℂ) r :=
      isOpen_ball.mem_nhds (mem_ball_self hr)
    filter_upwards [hball.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hi
    exact ⟨ball_subset_closedBall hz, hi⟩
  rcases hcases with hzero | ⟨m, u, hu, hu0, _, _, hfactor⟩
  · exfalso
    apply hnot
    filter_upwards [hzero, hnearK] with z hz hzK
    apply (M65StrictTrace.halfDiskGradient_eq_zero_iff H r z).mp
    have hh := congrArg (fun w => Ring.inverse (L z) w) hz
    change (Ring.inverse (L z) * L z) (M65StrictTrace.halfDiskGradient H r z) = _ at hh
    rw [Ring.inverse_mul_cancel _ (hunit z hzK)] at hh
    simpa using hh
  · obtain ⟨d0, hd0, hd0rR, hqc, hqi, hqne, hq1, hqI, C, hC, hholder⟩ :=
      gauged_halfDisk_unframed_residual_holder hR hB hA0 hs0 hb0 hsmall hA0i hu hu0
        hr hL hunit
    let q := fun z => Ring.inverse (L z) (cauchyGauge A0 z (u z))
    obtain ⟨V, hV, hVfac⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hfactor
    obtain ⟨s, hs, hVs⟩ := Metric.mem_nhds_iff.mp hV
    let d := min s d0 / 2
    have hd : 0 < d := half_pos (lt_min hs hd0)
    have hds : d < s := (half_lt_self (lt_min hs hd0)).trans_le (min_le_left _ _)
    have hdd0 : d < d0 := (half_lt_self (lt_min hs hd0)).trans_le (min_le_right _ _)
    have hdr : d < r := (hdd0.trans hd0rR).trans_le (min_le_left _ _)
    have hKsmall : closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im} ⊆
        closedBall (0 : ℂ) d0 ∩ {z | 0 ≤ z.im} :=
      inter_subset_inter (closedBall_subset_closedBall hdd0.le) Subset.rfl
    have hUsmall : ball (0 : ℂ) d ∩ {z | 0 < z.im} ⊆
        ball (0 : ℂ) d0 ∩ {z | 0 < z.im} :=
      inter_subset_inter (ball_subset_ball hdd0.le) Subset.rfl
    refine ⟨d, m, q, hd, hdr, hqc.mono hKsmall, hqi.mono hUsmall,
      fun z hz => hqne z (hKsmall hz), ?_,
      hq1.mono_measure (Measure.restrict_mono hUsmall le_rfl),
      hqI.mono_measure (Measure.restrict_mono hUsmall le_rfl),
      C, hC, fun z hz w hw => hholder z (hKsmall hz) w (hKsmall hw)⟩
    intro z hz
    have hzK : z ∈ K :=
      ⟨closedBall_subset_closedBall hdr.le hz.1, hz.2⟩
    have hzfac := hVfac ⟨hVs (closedBall_subset_ball hds hz.1), hz.2⟩
    have hh := congrArg (fun w => Ring.inverse (L z) w) hzfac
    change (Ring.inverse (L z) * L z) (M65StrictTrace.halfDiskGradient H r z) = _ at hh
    rw [Ring.inverse_mul_cancel _ (hunit z hzK), map_smul] at hh
    exact hh

theorem halfDisk_differential_factor_memLp
    {n : ℕ} [Nonempty (Fin n)]
    (J : (Fin n → ℂ) ≃ₗᵢ[ℝ] (Fin n → ℂ))
    (hJ : ∀ (s : ℂ) v, J (s • v) = star s • J v) (hJJ : Function.Involutive J)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    {L : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hHi : ContDiffOn ℝ ∞ H (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hL : ContDiffOn ℝ 1 L (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hunit : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}, IsUnit (L z))
    (hA : ContinuousOn A (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hAi : ContDiffOn ℝ 1 A (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (heq : ∀ z ∈ ball (0 : ℂ) r, 0 < z.im →
      dbar (fun w => L w (M65StrictTrace.halfDiskGradient H r w)) z =
        A z (L z (M65StrictTrace.halfDiskGradient H r z)))
    (hreal : ∀ z ∈ closedBall (0 : ℂ) r, z.im = 0 →
      J (L z (M65StrictTrace.halfDiskGradient H r z)) =
        L z (M65StrictTrace.halfDiskGradient H r z))
    (hnot : ¬∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0,
      fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z = 0) :
    ∃ (d : ℝ) (m : ℕ) (q : ℂ → Fin n → ℂ), 0 < d ∧ d < r ∧
      ContinuousOn q (closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) ∧
      ContDiffOn ℝ 1 q (ball (0 : ℂ) d ∩ {z | 0 < z.im}) ∧
      (∀ z ∈ closedBall (0 : ℂ) d ∩ {w | 0 ≤ w.im}, q z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) d ∩ {w | 0 ≤ w.im},
        M65StrictTrace.halfDiskGradient H r z = z ^ m • q z) ∧
      MemLp (fun z => fderiv ℝ q z 1)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) ∧
      MemLp (fun z => fderiv ℝ q z I)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) := by
  obtain ⟨d, m, q, hd, hdr, hc, hC1, hn, hf, h1, hI, _⟩ :=
    halfDisk_differential_factor_holder J hJ hJJ hr hH hHi hL hunit hA hAi heq hreal hnot
  exact ⟨d, m, q, hd, hdr, hc, hC1, hn, hf, h1, hI⟩

end PoincareConjecture.M65Branch
