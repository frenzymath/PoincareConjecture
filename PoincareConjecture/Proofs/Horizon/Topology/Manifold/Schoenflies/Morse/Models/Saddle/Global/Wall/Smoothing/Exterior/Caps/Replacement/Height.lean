import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Parameters

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Replacement

private def lineDilation (a : Real) (ha : a ≠ 0) : Real ≃ₘ[Real] Real where
  toFun t := a*t
  invFun t := t/a
  left_inv t := by field_simp
  right_inv t := by field_simp
  contMDiff_toFun := (contDiff_const.mul contDiff_id).contMDiff
  contMDiff_invFun := (contDiff_id.div_const a).contMDiff

theorem exists_cylindrical_height_diffeomorph {b : Real} (hb : 0 < b) :
    ∃ σ : Real, 0 < σ ∧ σ < b ∧ σ < 1/2 ∧ ∃ H : Real ≃ₘ[Real] Real,
      StrictMono H ∧ H 0 = 0 ∧
      (∀ t, |t| ≤ σ → H t = t / Real.sqrt (1-t^2)) ∧
      (∀ t, b ≤ |t| → H t = t) := by
  let K : Set Real := Icc (-(1/2)) (1/2)
  let U : Set Real := Ioo (-1) 1
  obtain ⟨χ,hχ,hχc,hχU,hχone⟩ :=
    Poincare.Parabolic.Interior.exists_contDiff_compact_cutoff
      (show IsCompact K from isCompact_Icc) (show IsOpen U from isOpen_Ioo)
      (by intro s hs; constructor <;> linarith [hs.1,hs.2])
  let α : Real × Real → Real := fun z => z.2 / Real.sqrt (1-z.1*z.2^2)
  let W : Set (Real × Real) := {z | 0 < 1-z.1*z.2^2}
  have hW : IsOpen W := isOpen_lt continuous_const
    (continuous_const.sub (continuous_fst.mul (continuous_snd.pow 2)))
  have hα : ContDiffOn Real ∞ α W := by
    apply contDiff_snd.contDiffOn.div
      ((contDiff_const.sub (contDiff_fst.mul (contDiff_snd.pow 2))).contDiffOn.sqrt
        (fun z hz => ne_of_gt hz))
    intro z hz
    exact (Real.sqrt_pos.mpr hz).ne'
  obtain ⟨ε,hε,T,hTzero,hT,hTi,hTfix,hTform⟩ :=
    exists_cutoff_parameter_family_on α hW χ hχ hχc
      (by intro s hs; norm_num [W]) hα (by intro s hs; simp [α])
  let u := min ε (min (b^2/4) (1/4)) / 2
  have hu : 0 < u := by dsimp [u]; positivity
  have huε : u < ε := by
    dsimp [u]
    linarith [min_le_left ε (min (b^2/4) (1/4))]
  have hub : u ≤ b^2/4 := by
    have h := (min_le_right ε (min (b^2/4) (1/4))).trans (min_le_left _ _)
    dsimp [u]
    nlinarith [sq_pos_of_pos hb]
  have husmall : u < 1/4 := by
    have h := (min_le_right ε (min (b^2/4) (1/4))).trans (min_le_right _ _)
    dsimp [u]
    linarith
  let a := Real.sqrt u
  have ha : 0 < a := Real.sqrt_pos.mpr hu
  have hasq : a^2 = u := Real.sq_sqrt hu.le
  have hab : a ≤ b/2 := by nlinarith
  have hasmall : a < 1/2 := by nlinarith
  let S := lineDilation a ha.ne'
  let H := (S.symm.trans (T u)).trans S
  have hH (t : Real) : H t = a*T u (t/a) := rfl
  have huI : u ∈ Icc (-ε) ε := ⟨by linarith,huε.le⟩
  have hformula (t : Real) (ht : |t| ≤ a/2) : H t = t / Real.sqrt (1-t^2) := by
    have hta : t/a ∈ K := by
      have ht' := abs_le.mp ht
      constructor
      · apply (le_div_iff₀ ha).mpr
        linarith
      · apply (div_le_iff₀ ha).mpr
        linarith
    rw [hH,hTform u huI,(hχone (t/a) hta).self_of_nhds,one_mul]
    have he : u*(t/a)^2 = t^2 := by rw [← hasq]; field_simp
    dsimp only [α]
    rw [he]
    field_simp
    ring
  have hfix (t : Real) (ht : b ≤ |t|) : H t = t := by
    have hnot : t/a ∉ tsupport χ := by
      intro hs
      have h := abs_lt.mpr (hχU hs)
      rw [abs_div,abs_of_pos ha] at h
      have hh := (div_lt_iff₀ ha).mp h
      linarith
    rw [hH,hTfix u (t/a) hnot]
    field_simp
  have hzero : H 0 = 0 := by
    rw [hformula 0 (by simpa using (half_pos ha).le)]
    simp
  have hmono : StrictMono H := by
    rcases H.continuous.strictMono_of_inj H.injective with hm | hm
    · exact hm
    · have hh := hm hb
      rw [hzero,hfix b (by rw [abs_of_pos hb])] at hh
      linarith
  exact ⟨a/2,half_pos ha,by linarith,by linarith,H,hmono,hzero,hformula,hfix⟩

theorem exists_cylindrical_height_and_radius {b : Real} (hb : 0 < b) :
    ∃ σ : Real, 0 < σ ∧ σ < b ∧ σ < 1/2 ∧
      ∃ (H : Real ≃ₘ[Real] Real) (r : Real → Real),
      StrictMono H ∧ H 0 = 0 ∧ ContDiff Real ∞ r ∧ (∀ t, 0 < r t) ∧
      (∀ t, H t = r t*t) ∧
      (∀ t, |t| ≤ σ → H t = t / Real.sqrt (1-t^2)) ∧
      (∀ t, |t| ≤ σ → r t = (Real.sqrt (1-t^2))⁻¹) ∧
      (∀ t, b ≤ |t| → H t = t ∧ r t = 1) := by
  obtain ⟨σ,hσ,hσb,hσsmall,H,hmono,hzero,hlocal,hfix⟩ :=
    exists_cylindrical_height_diffeomorph hb
  let r : Real → Real := fun t => if t = 0 then 1 else H t/t
  have hrformula (t : Real) (ht : |t| ≤ σ) : r t = (Real.sqrt (1-t^2))⁻¹ := by
    by_cases ht0 : t = 0
    · simp [r,ht0]
    · simp only [r,if_neg ht0,hlocal t ht]
      field_simp
  have hr : ContDiff Real ∞ r := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t = 0
    · subst t
      have hnear : r =ᶠ[𝓝 (0 : Real)] (fun t => (Real.sqrt (1-t^2))⁻¹) := by
        filter_upwards [Metric.ball_mem_nhds (0 : Real) hσ] with t ht
        apply hrformula
        exact (show |t| < σ by simpa only [mem_ball,Real.dist_eq,sub_zero] using ht).le
      apply ContDiffAt.congr_of_eventuallyEq _ hnear
      apply ContDiffAt.inv
      · apply ContDiffAt.sqrt
        · exact (contDiff_const.sub (contDiff_id.pow 2)).contDiffAt
        · norm_num
      · norm_num
    · have hnear : r =ᶠ[𝓝 t] (fun t => H t/t) := by
        filter_upwards [eventually_ne_nhds ht] with s hs
        simp only [r,if_neg hs]
      exact (H.contDiff.contDiffAt.div contDiffAt_id ht).congr_of_eventuallyEq hnear
  have hrpos (t : Real) : 0 < r t := by
    by_cases ht : t = 0
    · simp [r,ht]
    · change 0 < if t = 0 then 1 else H t/t
      rw [if_neg ht]
      rcases lt_or_gt_of_ne ht with hn | hp
      · exact div_pos_of_neg_of_neg (by simpa only [hzero] using hmono hn) hn
      · exact div_pos (by simpa only [hzero] using hmono hp) hp
  refine ⟨σ,hσ,hσb,hσsmall,H,r,hmono,hzero,hr,hrpos,?_,hlocal,hrformula,?_⟩
  · intro t
    by_cases ht : t = 0
    · simp [ht,hzero]
    · simp only [r,if_neg ht]
      exact (div_mul_cancel₀ (H t) ht).symm
  · intro t ht
    have ht0 : t ≠ 0 := by intro hz; rw [hz,abs_zero] at ht; linarith
    exact ⟨hfix t ht,by simp [r,ht0,hfix t ht]⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Replacement
