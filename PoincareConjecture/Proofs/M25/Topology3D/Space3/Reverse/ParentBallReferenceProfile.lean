import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlatCapProfile
import Mathlib.Analysis.SpecialFunctions.SmoothTransition














set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D



noncomputable def referenceCapScale (a : ℝ) : ℝ :=
  Real.sqrt ((1 + a) / (1 - a))


theorem referenceCapScale_pos (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1) :
    0 < referenceCapScale a := by
  apply Real.sqrt_pos.mpr
  exact div_pos (by linarith [ha.1]) (by linarith [ha.2])



theorem referenceCapScale_sq (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1) :
    (referenceCapScale a) ^ 2 * (1 - a) = 1 + a := by
  have hden : 0 < 1 - a := by linarith [ha.2]
  have hnum : 0 < 1 + a := by linarith [ha.1]
  rw [referenceCapScale, Real.sq_sqrt (div_pos hnum hden).le]
  exact div_mul_cancel₀ _ hden.ne'

private theorem profile_base_radial (H : ℝ) (hH : 0 ≤ H) (f : ℝ → ℝ)
    (hfrad : ∀ z, |z| < 1 → f z ≤ (Real.sqrt (1 - z ^ 2))⁻¹)
    (z : ℝ) (hz : |z| < 1) :
    (H * f z) * Real.sqrt (1 - z ^ 2) ≤ H := by
  have hr : 0 < 1 - z ^ 2 := by
    nlinarith only [hz, sq_abs z, abs_nonneg z]
  have hs : 0 < Real.sqrt (1 - z ^ 2) := Real.sqrt_pos.mpr hr
  have hprod : f z * Real.sqrt (1 - z ^ 2) ≤ 1 := by
    calc
      f z * Real.sqrt (1 - z ^ 2) ≤
          (Real.sqrt (1 - z ^ 2))⁻¹ * Real.sqrt (1 - z ^ 2) :=
        mul_le_mul_of_nonneg_right (hfrad z hz) hs.le
      _ = 1 := inv_mul_cancel₀ hs.ne'
  calc
    (H * f z) * Real.sqrt (1 - z ^ 2) =
        H * (f z * Real.sqrt (1 - z ^ 2)) := by ring
    _ ≤ H * 1 := mul_le_mul_of_nonneg_left hprod hH
    _ = H := mul_one H

private theorem profile_rational_radial (c H c₁ z : ℝ)
    (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hcut : c ^ 2 - H ^ 2 < c₁ * (c ^ 2 + H ^ 2))
    (hz : |z| < 1) (hzc : c₁ ≤ z) :
    (c / (1 + z)) * Real.sqrt (1 - z ^ 2) ≤ H := by
  have hzp : 0 < 1 + z := by linarith only [(abs_lt.mp hz).1]
  have hr : 0 ≤ 1 - z ^ 2 := by
    nlinarith only [hz, sq_abs z, abs_nonneg z]
  have hquad : c ^ 2 * (1 - z) ≤ H ^ 2 * (1 + z) := by
    have hmul := mul_le_mul_of_nonneg_right hzc
      (add_nonneg (sq_nonneg c) (sq_nonneg H))
    nlinarith only [hcut, hmul]
  have hcross : c * Real.sqrt (1 - z ^ 2) ≤ H * (1 + z) := by
    apply (sq_le_sq₀ (mul_nonneg hc (Real.sqrt_nonneg _))
      (mul_nonneg hH hzp.le)).mp
    simp only [mul_pow, Real.sq_sqrt hr]
    have hmul := mul_le_mul_of_nonneg_right hquad hzp.le
    nlinarith only [hmul]
  calc
    (c / (1 + z)) * Real.sqrt (1 - z ^ 2) =
        (c * Real.sqrt (1 - z ^ 2)) / (1 + z) := by ring
    _ ≤ H := (div_le_iff₀ hzp).mpr hcross

private theorem profile_base_comparison (c H a c₂ : ℝ)
    (hc : 0 ≤ c) (hH : 0 ≤ H) (hH3sq : 3 * H ^ 2 < c ^ 2)
    (hHac : H * (1 + a) < c) (hc₂a : c₂ < a) (f : ℝ → ℝ)
    (hfrad : ∀ z, |z| < 1 → f z ≤ (Real.sqrt (1 - z ^ 2))⁻¹)
    (hffar : ∀ z, 1 / 2 ≤ ‖z‖ → f z = 1)
    (z : ℝ) (hzl : -1 < z) (hzu : z < c₂) :
    H * f z ≤ c / (1 + z) := by
  have hzp : 0 < 1 + z := by linarith only [hzl]
  by_cases hzhalf : z ≤ 1 / 2
  · have hzabs : |z| < 1 := abs_lt.mpr ⟨hzl, by linarith only [hzhalf]⟩
    have hr : 0 < 1 - z ^ 2 := by
      nlinarith only [hzabs, sq_abs z, abs_nonneg z]
    have hs : 0 < Real.sqrt (1 - z ^ 2) := Real.sqrt_pos.mpr hr
    have hquad : H ^ 2 * (1 + z) ≤ c ^ 2 * (1 - z) := by
      have hfirst : H ^ 2 * (1 + z) ≤ (3 * H ^ 2) * (1 - z) := by
        have hmul := mul_nonneg (sq_nonneg H)
          (show 0 ≤ 2 - 4 * z by linarith only [hzhalf])
        nlinarith only [hmul]
      have hsecond := mul_le_mul_of_nonneg_right hH3sq.le
        (show 0 ≤ 1 - z by linarith only [hzhalf])
      exact hfirst.trans hsecond
    have hcross : H * (1 + z) ≤ c * Real.sqrt (1 - z ^ 2) := by
      apply (sq_le_sq₀ (mul_nonneg hH hzp.le) (mul_nonneg hc hs.le)).mp
      simp only [mul_pow, Real.sq_sqrt hr.le]
      have hmul := mul_le_mul_of_nonneg_right hquad hzp.le
      nlinarith only [hmul]
    calc
      H * f z ≤ H * (Real.sqrt (1 - z ^ 2))⁻¹ :=
        mul_le_mul_of_nonneg_left (hfrad z hzabs) hH
      _ = H / Real.sqrt (1 - z ^ 2) := (div_eq_mul_inv _ _).symm
      _ ≤ c / (1 + z) := (div_le_div_iff₀ hs hzp).mpr hcross
  · have hzf : f z = 1 := hffar z (by
      rw [Real.norm_eq_abs, abs_of_pos (show 0 < z by linarith only [hzhalf])]
      exact (lt_of_not_ge hzhalf).le)
    rw [hzf, mul_one]
    apply (le_div_iff₀ hzp).mpr
    have hmul := mul_le_mul_of_nonneg_left
      (show 1 + z ≤ 1 + a by linarith only [hzu, hc₂a]) hH
    exact hmul.trans hHac.le






theorem exists_reference_cap_profile (a ε : ℝ)
    (ha : a ∈ Ioo (1 / 2 : ℝ) 1) (hε : 0 < ε) :
    ∃ H c₁ c₂ : ℝ,
      1 < H ∧ H < 1 + ε ∧
      H < referenceCapScale a / Real.sqrt 3 ∧
      H < referenceCapScale a / (1 + a) ∧
      1 / 2 < c₁ ∧ c₁ < c₂ ∧ c₂ < a ∧
      ∃ α : ℝ → ℝ, ContDiff ℝ ∞ α ∧ (∀ z, 0 < α z) ∧
        (∀ z, c₂ ≤ z → α z = referenceCapScale a / (1 + z)) ∧
        (∀ z, |z| < 1 → α z * Real.sqrt (1 - z ^ 2) ≤ H) ∧
        ∀ z, -1 < z → z ≤ 1 → α z ≤ referenceCapScale a / (1 + z) := by
  let c := referenceCapScale a
  have hc : 0 < c := referenceCapScale_pos a ha
  have hcsq : c ^ 2 * (1 - a) = 1 + a := referenceCapScale_sq a ha
  have ha0 : 0 < a := by linarith [ha.1]
  have h1a : 0 < 1 + a := by linarith
  have hden : 0 < 1 - a := by linarith [ha.2]
  have hc3 : 3 < c ^ 2 := by
    by_contra h
    have hmul := mul_nonneg (sub_nonneg.mpr (le_of_not_gt h)) hden.le
    nlinarith [ha.1]
  have hs3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs3sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3c : Real.sqrt (3 : ℝ) < c := by
    apply (sq_lt_sq₀ hs3.le hc.le).mp
    rwa [hs3sq]
  have h1ac : 1 + a < c := by
    apply (sq_lt_sq₀ h1a.le hc.le).mp
    by_contra h
    have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt h) hden.le
    have hpos := mul_pos (sq_pos_of_pos ha0) h1a
    nlinarith
  have hbound : 1 < min (1 + ε) (min (c / Real.sqrt 3) (c / (1 + a))) := by
    exact lt_min (by linarith) (lt_min ((one_lt_div hs3).mpr hs3c)
      ((one_lt_div h1a).mpr h1ac))
  obtain ⟨H, hH1, hHbound⟩ := exists_between hbound
  obtain ⟨hHε, hHother⟩ := lt_min_iff.mp hHbound
  obtain ⟨hH3, hHa⟩ := lt_min_iff.mp hHother
  have hH : 0 < H := lt_trans zero_lt_one hH1
  have hHsq : 1 < H ^ 2 := by nlinarith
  have hH3sq : 3 * H ^ 2 < c ^ 2 := by
    have h := (sq_lt_sq₀ (mul_nonneg hH.le hs3.le) hc.le).mpr
      ((lt_div_iff₀ hs3).mp hH3)
    rw [mul_pow, hs3sq] at h
    nlinarith
  have hHac : H * (1 + a) < c := (lt_div_iff₀ h1a).mp hHa
  have hsum : 0 < c ^ 2 + H ^ 2 := by positivity
  have hthreshold : (c ^ 2 - H ^ 2) / (c ^ 2 + H ^ 2) < a := by
    apply (div_lt_iff₀ hsum).mpr
    have hpos := mul_pos (sub_pos.mpr hHsq) h1a
    nlinarith
  obtain ⟨c₁, hc₁lower, hc₁a⟩ :=
    exists_between (max_lt ha.1 hthreshold)
  have hc₁ : 1 / 2 < c₁ :=
    lt_of_le_of_lt (le_max_left _ _) hc₁lower
  have hcut : c ^ 2 - H ^ 2 < c₁ * (c ^ 2 + H ^ 2) := by
    apply (div_lt_iff₀ hsum).mp
    exact lt_of_le_of_lt (le_max_right _ _) hc₁lower
  obtain ⟨c₂, hc₁c₂, hc₂a⟩ := exists_between hc₁a
  have hwidth : 0 < c₂ - c₁ := sub_pos.mpr hc₁c₂
  obtain ⟨f, hf, hf1, _, hffar, hfbound⟩ := exists_bounded_flatCap_profile (E := ℝ)
  have hfpos (z : ℝ) : 0 < f z := lt_of_lt_of_le zero_lt_one (hf1 z)
  have hfrad (z : ℝ) (hz : |z| < 1) :
      f z ≤ (Real.sqrt (1 - z ^ 2))⁻¹ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      hfbound z (by simpa only [Real.norm_eq_abs] using hz)
  let χ : ℝ → ℝ := fun z => Real.smoothTransition ((z - c₁) / (c₂ - c₁))
  have hχ : ContDiff ℝ ∞ χ :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  have hχ0 (z : ℝ) : 0 ≤ χ z := Real.smoothTransition.nonneg _
  have hχ1 (z : ℝ) : χ z ≤ 1 := Real.smoothTransition.le_one _
  have hχzero (z : ℝ) (hz : z ≤ c₁) : χ z = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) hwidth.le)
  have hχone (z : ℝ) (hz : c₂ ≤ z) : χ z = 1 := by
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ hwidth).mpr
    linarith
  have hχsupport : Function.support χ ⊆ Ici c₁ := by
    intro z hz
    by_contra h
    exact hz (hχzero z (le_of_lt (lt_of_not_ge h)))
  have hχclosed : tsupport χ ⊆ Ici c₁ := closure_minimal hχsupport isClosed_Ici
  have hχdomain : tsupport χ ⊆ Ioi (1 / 2 : ℝ) :=
    fun _ hz => hc₁.trans_le (hχclosed hz)
  have hrat : ContDiffOn ℝ ∞ (fun z : ℝ => c / (1 + z)) (Ioi (1 / 2 : ℝ)) := by
    apply contDiffOn_const.div (contDiffOn_const.add contDiffOn_id)
    intro z hz
    change (1 / 2 : ℝ) < z at hz
    change (1 + z : ℝ) ≠ 0
    exact ne_of_gt (by linarith only [hz])
  have hbase : ContDiff ℝ ∞ (fun z => H * f z) := contDiff_const.mul hf
  let α : ℝ → ℝ := fun z => H * f z + χ z * (c / (1 + z) - H * f z)
  have hα : ContDiff ℝ ∞ α := hbase.add
    (contDiff_cutoff_smul isOpen_Ioi χ hχ hχdomain
      (fun z => c / (1 + z) - H * f z) (hrat.sub hbase.contDiffOn))
  have hαeq (z : ℝ) :
      α z = (1 - χ z) * (H * f z) + χ z * (c / (1 + z)) := by
    dsimp only [α]
    ring
  have hαleft (z : ℝ) (hz : z ≤ c₁) : α z = H * f z := by
    dsimp only [α]
    rw [hχzero z hz, zero_mul, add_zero]
  have hαright (z : ℝ) (hz : c₂ ≤ z) : α z = c / (1 + z) := by
    dsimp only [α]
    rw [hχone z hz, one_mul]
    ring
  have hαpos (z : ℝ) : 0 < α z := by
    by_cases hz : z ≤ c₁
    · rw [hαleft z hz]
      exact mul_pos hH (hfpos z)
    · have hzc : c₁ < z := lt_of_not_ge hz
      have hzp : 0 < 1 + z := by linarith
      rw [hαeq]
      by_cases hχeq : χ z = 1
      · rw [hχeq, sub_self, zero_mul, one_mul, zero_add]
        exact div_pos hc hzp
      · have hχlt : χ z < 1 := lt_of_le_of_ne (hχ1 z) hχeq
        exact add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr hχlt) (mul_pos hH (hfpos z)))
          (mul_nonneg (hχ0 z) (div_pos hc hzp).le)
  have hbaserad (z : ℝ) (hz : |z| < 1) :
      (H * f z) * Real.sqrt (1 - z ^ 2) ≤ H :=
    profile_base_radial H hH.le f hfrad z hz
  have hratrad (z : ℝ) (hz : |z| < 1) (hzc : c₁ ≤ z) :
      (c / (1 + z)) * Real.sqrt (1 - z ^ 2) ≤ H :=
    profile_rational_radial c H c₁ z hc.le hH.le hcut hz hzc
  have hαrad (z : ℝ) (hz : |z| < 1) :
      α z * Real.sqrt (1 - z ^ 2) ≤ H := by
    by_cases hzc : z ≤ c₁
    · rw [hαleft z hzc]
      exact hbaserad z hz
    · have hzc' : c₁ ≤ z := (lt_of_not_ge hzc).le
      calc
        α z * Real.sqrt (1 - z ^ 2) =
            (1 - χ z) * ((H * f z) * Real.sqrt (1 - z ^ 2)) +
              χ z * ((c / (1 + z)) * Real.sqrt (1 - z ^ 2)) := by
          rw [hαeq]
          ring
        _ ≤ (1 - χ z) * H + χ z * H := add_le_add
          (mul_le_mul_of_nonneg_left (hbaserad z hz) (sub_nonneg.mpr (hχ1 z)))
          (mul_le_mul_of_nonneg_left (hratrad z hz hzc') (hχ0 z))
        _ = H := by ring
  have hbasecompare (z : ℝ) (hzl : -1 < z) (hzu : z < c₂) :
      H * f z ≤ c / (1 + z) :=
    profile_base_comparison c H a c₂ hc.le hH.le hH3sq hHac hc₂a f hfrad hffar z hzl hzu
  have hαcompare (z : ℝ) (hzl : -1 < z) (_hzu : z ≤ 1) :
      α z ≤ c / (1 + z) := by
    by_cases hz : c₂ ≤ z
    · exact (hαright z hz).le
    · have hbasez := hbasecompare z hzl (lt_of_not_ge hz)
      calc
        α z = (1 - χ z) * (H * f z) + χ z * (c / (1 + z)) := hαeq z
        _ ≤ (1 - χ z) * (c / (1 + z)) + χ z * (c / (1 + z)) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hbasez (sub_nonneg.mpr (hχ1 z))) le_rfl
        _ = c / (1 + z) := by ring
  exact ⟨H, c₁, c₂, hH1, hHε, hH3, hHa, hc₁, hc₁c₂, hc₂a,
    α, hα, hαpos, hαright, hαrad, hαcompare⟩




theorem reference_profile_horizontal_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ → ℝ) (H : ℝ) (hα : ∀ z, 0 < α z) (hH : 0 ≤ H)
    (hbound : ∀ z, |z| < 1 → α z * Real.sqrt (1 - z ^ 2) ≤ H)
    (x : E) (z : ℝ) (hball : ‖x‖ ^ 2 + z ^ 2 ≤ 1) :
    ‖α z • x‖ ≤ H := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hα z)]
  by_cases hz : |z| < 1
  · have hx : ‖x‖ ≤ Real.sqrt (1 - z ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
    exact (mul_le_mul_of_nonneg_left hx (hα z).le).trans (hbound z hz)
  · have hx : ‖x‖ = 0 := by
      have h := le_of_not_gt hz
      nlinarith [sq_abs z, norm_nonneg x, sq_nonneg ‖x‖]
    rw [hx, mul_zero]
    exact hH

end PoincareConjecture.M25.Topology3D
