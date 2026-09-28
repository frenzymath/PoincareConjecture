import PoincareConjecture.Proofs.M34.Mathlib.FirstExitLevel
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring











set_option autoImplicit false

open Set




theorem ContinuousOn.lt_two_mul_of_guarded_quadratic_deriv
    {f : ℝ → ℝ} {a b A B R : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b))
    (hA : 0 ≤ A) (hB : 0 < B) (hRB : R ≤ B) (hinit : f a ≤ B)
    (hderiv : ∀ t ∈ Ioo a b, R ≤ f t → deriv f t ≤ A * (f t) ^ 2)
    (htime : 4 * A * B * (b - a) < 1) :
    ∀ t ∈ Icc a b, f t < 2 * B := by
  intro t ht
  by_contra hlarge
  obtain ⟨sigma, hsigma, hfsigma, hbefore⟩ :=
    (hf.mono (Icc_subset_Icc_right ht.2)).exists_first_eq_of_le ht.1
      (hinit.trans (by linarith : B ≤ 2 * B)) (le_of_not_gt hlarge)
  have hfsmall : ContinuousOn f (Icc a sigma) :=
    hf.mono (Icc_subset_Icc_right (hsigma.2.trans ht.2))
  have hlevel : (Icc a sigma ∩ f ⁻¹' {B}).Nonempty := by
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hsigma.1 hfsmall
      ⟨hinit, by rw [hfsigma]; linarith⟩
    exact ⟨s, hs, hfs⟩
  have hcompact : IsCompact (Icc a sigma ∩ f ⁻¹' {B}) :=
    isCompact_Icc.of_isClosed_subset
      (hfsmall.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨alpha, halpha⟩ := hcompact.exists_isGreatest hlevel
  have haalpha : a ≤ alpha := halpha.1.1.1
  have halphasigma : alpha ≤ sigma := halpha.1.1.2
  have hfalpha : f alpha = B := halpha.1.2
  have hsigmab : sigma ≤ b := hsigma.2.trans ht.2
  have hinterior : interior (Icc alpha sigma) ⊆ Ioo a b := by
    rw [interior_Icc]
    intro s hs
    exact ⟨haalpha.trans_lt hs.1, hs.2.trans_le hsigmab⟩
  have hbound : ∀ s ∈ interior (Icc alpha sigma), deriv f s ≤ 4 * A * B ^ 2 := by
    intro s hs
    have hs' : s ∈ Ioo alpha sigma := by simpa only [interior_Icc] using hs
    have hlo : B < f s := by
      by_contra hlow
      obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc hs'.2.le
        (hfsmall.mono (Icc_subset_Icc_left (haalpha.trans hs'.1.le)))
        ⟨le_of_not_gt hlow, by rw [hfsigma]; linarith⟩
      have hra : r ≤ alpha := halpha.2
        ⟨⟨haalpha.trans (hs'.1.le.trans hr.1), hr.2⟩, hfr⟩
      exact (not_le_of_gt (hs'.1.trans_le hr.1)) hra
    have hup : f s < 2 * B := hbefore s ⟨haalpha.trans hs'.1.le, hs'.2⟩
    calc
      deriv f s ≤ A * (f s) ^ 2 := hderiv s (hinterior hs) (hRB.trans hlo.le)
      _ ≤ A * (2 * B) ^ 2 := mul_le_mul_of_nonneg_left (by
        simpa only [pow_two] using mul_self_le_mul_self (hB.le.trans hlo.le) hup.le) hA
      _ = 4 * A * B ^ 2 := by ring
  have hgrowth := (convex_Icc alpha sigma).image_sub_le_mul_sub_of_deriv_le
    (hf.mono (Icc_subset_Icc haalpha hsigmab)) (hd.mono hinterior) hbound
    alpha ⟨le_rfl, halphasigma⟩ sigma ⟨halphasigma, le_rfl⟩ halphasigma
  have hlength : 4 * A * B ^ 2 * (sigma - alpha) ≤ 4 * A * B ^ 2 * (b - a) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsmall := mul_lt_mul_of_pos_right htime hB
  rw [hfsigma, hfalpha] at hgrowth
  nlinarith [hgrowth.trans hlength]
