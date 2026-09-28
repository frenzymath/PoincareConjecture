import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NoConjugate

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

theorem m64Intrinsic_jacobi_ratio_monotone
    {R : ℝ} (hR : 0 < R) {J J' J'' M M' M'' : ℝ → ℝ}
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hM : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt M (M' t) t)
    (hM' : ContinuousOn M' (Icc (0 : ℝ) R))
    (hM'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt M' (M'' t) t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) R, 0 < M t)
    (hinitial : 0 ≤ J' 0 * M 0 - J 0 * M' 0)
    (hineq : ∀ t ∈ Ioo (0 : ℝ) R, 0 ≤ J'' t * M t - J t * M'' t) :
    MonotoneOn (fun t => J t / M t) (Icc (0 : ℝ) R) := by
  have hJc : ContinuousOn J (Icc (0 : ℝ) R) :=
    fun t ht => (hJ t ht).continuousAt.continuousWithinAt
  have hMc : ContinuousOn M (Icc (0 : ℝ) R) :=
    fun t ht => (hM t ht).continuousAt.continuousWithinAt
  have hWd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R) :
      HasDerivAt (fun s => J' s * M s - J s * M' s)
        (J'' t * M t - J t * M'' t) t := by
    convert! ((hJ'' t ht).mul (hM t ⟨ht.1.le, ht.2.le⟩)).sub
      ((hJ t ⟨ht.1.le, ht.2.le⟩).mul (hM'' t ht)) using 1
    ring
  have hWmono : MonotoneOn (fun t => J' t * M t - J t * M' t)
      (Icc (0 : ℝ) R) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      ((hJ'.mul hMc).sub (hJc.mul hM'))
      (fun t ht => (hWd t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt)
    intro t ht
    exact hineq t (by simpa only [interior_Icc] using ht)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (hJc.div hMc (fun t ht => (hpos t ht).ne'))
    (fun t ht => ((hJ t (interior_subset ht)).div
      (hM t (interior_subset ht)) (hpos t (interior_subset ht)).ne').hasDerivWithinAt)
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) R := interior_subset ht
  exact div_nonneg (hinitial.trans (hWmono ⟨le_rfl, hR.le⟩ ht' ht'.1)) (sq_nonneg _)

theorem m64Intrinsic_jacobi_ge_positive_model
    {R kappa : ℝ} (hR : 0 < R) {J J' J'' M M' M'' k : ℝ → ℝ}
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hM : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt M (M' t) t)
    (hM' : ContinuousOn M' (Icc (0 : ℝ) R))
    (hM'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt M' (M'' t) t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) R, 0 < M t)
    (hzero : J 0 = M 0) (hinitial : M' 0 ≤ J' 0)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) R, J'' t + k t * J t = 0)
    (hmodel : ∀ t ∈ Ioo (0 : ℝ) R, M'' t + kappa ^ 2 * M t = 0)
    (hk : ∀ t ∈ Ioo (0 : ℝ) R, k t ≤ kappa ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) R, M t ≤ J t := by
  have hM0 := hpos 0 ⟨le_rfl, hR.le⟩
  have hJc : ContinuousOn J (Icc (0 : ℝ) R) :=
    fun t ht => (hJ t ht).continuousAt.continuousWithinAt
  have hW0 : 0 ≤ J' 0 * M 0 - J 0 * M' 0 := by
    rw [hzero]
    nlinarith [mul_le_mul_of_nonneg_right hinitial hM0.le]
  have hineq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R) (hjt : 0 ≤ J t) :
      0 ≤ J'' t * M t - J t * M'' t := by
    have hJval : J'' t = -k t * J t := by linarith [hjac t ht]
    have hMval : M'' t = -kappa ^ 2 * M t := by linarith [hmodel t ht]
    rw [hJval, hMval]
    have hp := mul_nonneg (mul_nonneg (sub_nonneg.mpr (hk t ht)) hjt)
      (hpos t ⟨ht.1.le, ht.2.le⟩).le
    nlinarith
  have hpositive : ∀ t ∈ Icc (0 : ℝ) R, 0 < J t := by
    intro t ht
    by_contra hnot
    let S : Set ℝ := Icc 0 t ∩ J ⁻¹' Iic 0
    have hSc : IsCompact S := by
      apply (isCompact_Icc : IsCompact (Icc (0 : ℝ) t)).of_isClosed_subset
      · exact (hJc.mono (Icc_subset_Icc le_rfl ht.2)).preimage_isClosed_of_isClosed
          isClosed_Icc isClosed_Iic
      · exact inter_subset_left
    have hSne : S.Nonempty := ⟨t, ⟨⟨ht.1, le_rfl⟩, le_of_not_gt hnot⟩⟩
    obtain ⟨c, hc, hmin⟩ := hSc.exists_isLeast hSne
    have hcpos : 0 < c := by
      refine lt_of_le_of_ne hc.1.1 ?_
      intro heq
      have hbad := hc.2
      change J c ≤ 0 at hbad
      rw [← heq, hzero] at hbad
      exact hM0.not_ge hbad
    have hcR : c ≤ R := hc.1.2.trans ht.2
    have hbefore (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) c) : 0 < J s := by
      by_contra hnot
      have hsS : s ∈ S := ⟨⟨hs.1.le, hs.2.le.trans hc.1.2⟩, le_of_not_gt hnot⟩
      exact hs.2.not_ge (hmin hsS)
    have hratio := m64Intrinsic_jacobi_ratio_monotone hcpos
      (fun s hs => hJ s ⟨hs.1, hs.2.trans hcR⟩)
      (hJ'.mono (Icc_subset_Icc le_rfl hcR))
      (fun s hs => hJ'' s ⟨hs.1, hs.2.trans_le hcR⟩)
      (fun s hs => hM s ⟨hs.1, hs.2.trans hcR⟩)
      (hM'.mono (Icc_subset_Icc le_rfl hcR))
      (fun s hs => hM'' s ⟨hs.1, hs.2.trans_le hcR⟩)
      (fun s hs => hpos s ⟨hs.1, hs.2.trans hcR⟩) hW0
      (fun s hs => hineq s ⟨hs.1, hs.2.trans_le hcR⟩ (hbefore s hs).le)
    have hquot := hratio ⟨le_rfl, hcpos.le⟩ ⟨hcpos.le, le_rfl⟩ hcpos.le
    change J 0 / M 0 ≤ J c / M c at hquot
    rw [hzero, div_self hM0.ne'] at hquot
    have hnonpos := div_nonpos_of_nonpos_of_nonneg hc.2 (hpos c ⟨hcpos.le, hcR⟩).le
    linarith
  have hratio := m64Intrinsic_jacobi_ratio_monotone hR hJ hJ' hJ'' hM hM' hM'' hpos
    hW0 (fun t ht => hineq t ht (hpositive t ⟨ht.1.le, ht.2.le⟩).le)
  intro t ht
  have hquot := hratio ⟨le_rfl, hR.le⟩ ht ht.1
  change J 0 / M 0 ≤ J t / M t at hquot
  rw [hzero, div_self hM0.ne'] at hquot
  exact (one_le_div (hpos t ht)).mp hquot

end PoincareConjecture
