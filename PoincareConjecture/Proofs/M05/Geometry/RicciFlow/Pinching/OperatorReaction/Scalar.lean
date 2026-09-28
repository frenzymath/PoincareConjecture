
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.ReactionInvariance











namespace Poincare.HamiltonIvey

open Set

private theorem linear_ode_nonneg
    {a b : ℝ} (hab : a ≤ b) {f c : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hc : ContinuousOn c (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (c t * f t) t)
    (ha : 0 ≤ f a) : ∀ t ∈ Icc a b, 0 ≤ f t := by
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc
  let K := c u + 1
  let g : ℝ → ℝ := fun t => Real.exp (-K * t) * f t
  have hgc : ContinuousOn g (Icc a b) := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hf
  have hga : 0 ≤ g a := mul_nonneg (Real.exp_pos _).le ha
  have hg := Poincare.nonneg_of_deriv_pos_on_neg hab hgc hga (by
    intro t ht hneg
    have hft : f t < 0 := by
      by_contra hn
      exact (not_lt_of_ge (mul_nonneg (Real.exp_pos _).le (le_of_not_gt hn))) hneg
    have hct : c t - K < 0 := by
      have : c t ≤ c u := hmax (Ioo_subset_Icc_self ht)
      dsimp [K]
      linarith
    refine ⟨Real.exp (-K * t) * ((c t - K) * f t), ?_,
      mul_pos (Real.exp_pos _) (mul_pos_of_neg_of_neg hct hft)⟩
    convert! ((((hasDerivAt_id t).const_mul (-K)).exp).mul (hd t ht)) using 1
    simp only [id_eq]
    ring)
  intro t ht
  exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp (hg t ht)


theorem reaction_two_order
    {a b : ℝ} (hab : a ≤ b) {lam mu nu : ℝ → ℝ}
    (hlam : ContinuousOn lam (Icc a b))
    (hmu : ContinuousOn mu (Icc a b))
    (hnu : ContinuousOn nu (Icc a b))
    (hdlam : ∀ t ∈ Ioo a b,
      HasDerivAt lam (2 * (lam t ^ 2 + mu t * nu t)) t)
    (hdmu : ∀ t ∈ Ioo a b,
      HasDerivAt mu (2 * (mu t ^ 2 + lam t * nu t)) t)
    (hdnu : ∀ t ∈ Ioo a b,
      HasDerivAt nu (2 * (nu t ^ 2 + lam t * mu t)) t)
    (hinit : mu a ≤ lam a ∧ nu a ≤ mu a) :
    ∀ t ∈ Icc a b, mu t ≤ lam t ∧ nu t ≤ mu t := by
  have hfirst := linear_ode_nonneg hab (hlam.sub hmu)
    (continuousOn_const.mul ((hlam.add hmu).sub hnu))
    (c := fun t => 2 * (lam t + mu t - nu t))
    (by
      intro t ht
      convert! (hdlam t ht).sub (hdmu t ht) using 1
      simp only [Pi.sub_apply]
      ring)
    (sub_nonneg.mpr hinit.1)
  have hsecond := linear_ode_nonneg hab (hmu.sub hnu)
    (continuousOn_const.mul ((hmu.add hnu).sub hlam))
    (c := fun t => 2 * (mu t + nu t - lam t))
    (by
      intro t ht
      convert! (hdmu t ht).sub (hdnu t ht) using 1
      simp only [Pi.sub_apply]
      ring)
    (sub_nonneg.mpr hinit.2)
  exact fun t ht => ⟨sub_nonneg.mp (hfirst t ht), sub_nonneg.mp (hsecond t ht)⟩


theorem scalarRegion_antitone_time {s t : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    scalarRegion s ⊆ scalarRegion t := by
  intro p hp
  have htt : 0 < 1 + t := by linarith
  have hss : 0 < 1 + s := by linarith
  have hden : 1 + t ≤ 1 + s := by linarith
  have hcut : cutoff s ≤ cutoff t :=
    div_le_div_of_nonneg_left baseCutoff_pos.le htt hden
  refine ⟨?_, ?_⟩
  · have hh : -3 / (1 + t) ≤ -3 / (1 + s) := by
      have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) htt hden
      simpa only [neg_div] using neg_le_neg hdiv
    exact hh.trans hp.1
  · intro hx
    have hpos : 0 ≤ p.2 := (cutoff_pos ht).le.trans hx
    have hlog := Real.log_le_log htt hden
    have hbar : logBarrier t p.2 ≤ logBarrier s p.2 := by
      unfold logBarrier
      exact mul_le_mul_of_nonneg_left (by linarith) hpos
    exact hbar.trans (hp.2 (hcut.trans hx))



theorem reaction_two_invariance
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {lam mu nu : ℝ → ℝ}
    (hlam : ContinuousOn lam (Icc a b))
    (hmu : ContinuousOn mu (Icc a b))
    (hnu : ContinuousOn nu (Icc a b))
    (hdlam : ∀ t ∈ Ioo a b,
      HasDerivAt lam (2 * (lam t ^ 2 + mu t * nu t)) t)
    (hdmu : ∀ t ∈ Ioo a b,
      HasDerivAt mu (2 * (mu t ^ 2 + lam t * nu t)) t)
    (hdnu : ∀ t ∈ Ioo a b,
      HasDerivAt nu (2 * (nu t ^ 2 + lam t * mu t)) t)
    (horder : mu a ≤ lam a ∧ nu a ≤ mu a)
    (hinit : (lam a + mu a + nu a, max (-nu a) 0) ∈ scalarRegion a) :
    ∀ t ∈ Icc a b,
      (lam t + mu t + nu t, max (-nu t) 0) ∈ scalarRegion t := by
  let B : ℝ := a + 2 * (b - a)
  let τ : ℝ → ℝ := fun s => a + (s - a) / 2
  have hab' : a ≤ B := by dsimp [B]; linarith
  have hτa : τ a = a := by dsimp [τ]; ring
  have hτcc : MapsTo τ (Icc a B) (Icc a b) := by
    intro s hs
    dsimp [τ, B] at *
    constructor <;> linarith [hs.1, hs.2]
  have hτoo : MapsTo τ (Ioo a B) (Ioo a b) := by
    intro s hs
    dsimp [τ, B] at *
    constructor <;> linarith [hs.1, hs.2]
  have hτc : Continuous τ := by fun_prop
  have hτd : ∀ s : ℝ, HasDerivAt τ (1 / 2) s := by
    intro s
    simpa [τ] using (((hasDerivAt_id s).sub_const a).div_const 2).const_add a
  have hord := reaction_two_order hab hlam hmu hnu hdlam hdmu hdnu horder
  have hscaled := reaction_invariance ha hab'
    (hlam.comp hτc.continuousOn hτcc)
    (hmu.comp hτc.continuousOn hτcc)
    (hnu.comp hτc.continuousOn hτcc)
    (fun s hs => hord (τ s) (hτcc hs))
    (by
      intro s hs
      convert! (hdlam (τ s) (hτoo hs)).comp s (hτd s) using 1
      simp only [Function.comp_apply]
      ring)
    (by
      intro s hs
      convert! (hdmu (τ s) (hτoo hs)).comp s (hτd s) using 1
      simp only [Function.comp_apply]
      ring)
    (by
      intro s hs
      convert! (hdnu (τ s) (hτoo hs)).comp s (hτd s) using 1
      simp only [Function.comp_apply]
      ring)
    (by simpa only [Function.comp_apply, hτa] using hinit)
  intro t ht
  have hst : a + 2 * (t - a) ∈ Icc a B := by
    dsimp [B]
    constructor <;> linarith [ht.1, ht.2]
  have hback : τ (a + 2 * (t - a)) = t := by dsimp [τ]; ring
  have hmem := hscaled (a + 2 * (t - a)) hst
  simp only [Function.comp_apply, hback] at hmem
  exact scalarRegion_antitone_time (ha.trans ht.1) (by linarith [ht.1]) hmem

end Poincare.HamiltonIvey
