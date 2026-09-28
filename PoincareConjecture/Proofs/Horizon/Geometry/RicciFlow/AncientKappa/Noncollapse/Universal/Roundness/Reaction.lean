import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.OperatorReaction.Scalar











set_option autoImplicit false

open Set

namespace PoincareConjecture.AncientKappaRoundness


theorem reaction_ratio_boundary {c μ ν : ℝ} (hc : 1 ≤ c) (hν : 0 ≤ ν)
    (horder : ν ≤ μ) :
    2 * ((c * ν) ^ 2 + μ * ν) - c * (2 * (ν ^ 2 + c * ν * μ)) ≤
      -2 * (c - 1) * ν ^ 2 := by
  have hp : 0 ≤ 2 * (c - 1) * ν * (c + 1) * (μ - ν) := by
    positivity
  nlinarith


private theorem nonneg_of_linear_supersolution {a b : ℝ} (hab : a ≤ b)
    {f c d : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hc : ContinuousOn c (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (d t) t)
    (hineq : ∀ t ∈ Ioo a b, f t < 0 → c t * f t ≤ d t)
    (hinit : 0 ≤ f a) : ∀ t ∈ Icc a b, 0 ≤ f t := by
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc
  let C := c u + 1
  let g : ℝ → ℝ := fun t => Real.exp (-C * t) * f t
  have hgc : ContinuousOn g (Icc a b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hf
  have hga : 0 ≤ g a := mul_nonneg (Real.exp_pos _).le hinit
  have hg := Poincare.nonneg_of_deriv_pos_on_neg hab hgc hga (by
    intro t ht hneg
    have hft : f t < 0 := by
      by_contra hn
      exact (not_lt_of_ge (mul_nonneg (Real.exp_pos _).le (le_of_not_gt hn))) hneg
    have hct : c t - C < 0 := by
      have : c t ≤ c u := hmax (Ioo_subset_Icc_self ht)
      dsimp [C]
      linarith
    have hpos : 0 < d t - C * f t := by
      have := mul_pos_of_neg_of_neg hct hft
      nlinarith [hineq t ht hft]
    refine ⟨Real.exp (-C * t) * (d t - C * f t), ?_,
      mul_pos (Real.exp_pos _) hpos⟩
    convert! ((((hasDerivAt_id t).const_mul (-C)).exp).mul (hd t ht)) using 1
    simp only [id_eq]
    ring)
  intro t ht
  exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp (hg t ht)


theorem reaction_nonneg {a b : ℝ} (hab : a ≤ b) {lam mu nu : ℝ → ℝ}
    (hlam : ContinuousOn lam (Icc a b))
    (hmu : ContinuousOn mu (Icc a b))
    (hnu : ContinuousOn nu (Icc a b))
    (hdlam : ∀ t ∈ Ioo a b,
      HasDerivAt lam (2 * (lam t ^ 2 + mu t * nu t)) t)
    (hdmu : ∀ t ∈ Ioo a b,
      HasDerivAt mu (2 * (mu t ^ 2 + lam t * nu t)) t)
    (hdnu : ∀ t ∈ Ioo a b,
      HasDerivAt nu (2 * (nu t ^ 2 + lam t * mu t)) t)
    (horder : mu a ≤ lam a ∧ nu a ≤ mu a) (hinit : 0 ≤ nu a) :
    ∀ t ∈ Icc a b, 0 ≤ nu t := by
  have hord := Poincare.HamiltonIvey.reaction_two_order hab hlam hmu hnu
    hdlam hdmu hdnu horder
  apply nonneg_of_linear_supersolution hab hnu
    (continuousOn_const.mul hlam.abs) hdnu (c := fun t => 2 * |lam t|) ?_ hinit
  intro t ht hneg
  have ho := hord t (Ioo_subset_Icc_self ht)
  have hp : |lam t| * nu t ≤ lam t * mu t := by
    by_cases hlam0 : 0 ≤ lam t
    · rw [abs_of_nonneg hlam0]
      exact mul_le_mul_of_nonneg_left ho.2 hlam0
    · have hlam0 := le_of_not_ge hlam0
      have hmu0 : mu t ≤ 0 := ho.1.trans hlam0
      exact (mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hneg.le).trans
        (mul_nonneg_of_nonpos_of_nonpos hlam0 hmu0)
  nlinarith [sq_nonneg (nu t)]



theorem reaction_pinching {a b c : ℝ} (hab : a ≤ b) (hc : 1 ≤ c)
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
    (hnonneg : 0 ≤ nu a) (hpinch : lam a ≤ c * nu a) :
    ∀ t ∈ Icc a b,
      0 ≤ nu t ∧ nu t ≤ mu t ∧ mu t ≤ lam t ∧ lam t ≤ c * nu t := by
  have hord := Poincare.HamiltonIvey.reaction_two_order hab hlam hmu hnu
    hdlam hdmu hdnu horder
  have hpos := reaction_nonneg hab hlam hmu hnu hdlam hdmu hdnu horder hnonneg
  have hratio := nonneg_of_linear_supersolution hab
    ((continuousOn_const.mul hnu).sub hlam)
    (continuousOn_const.mul ((hlam.add (continuousOn_const.mul hnu)).sub
      (continuousOn_const.mul hmu)))
    (f := fun t => c * nu t - lam t)
    (c := fun t => 2 * (lam t + c * nu t - c * mu t))
    (d := fun t => c * (2 * (nu t ^ 2 + lam t * mu t)) -
      2 * (lam t ^ 2 + mu t * nu t))
    (fun t ht => ((hdnu t ht).const_mul c).sub (hdlam t ht)) (by
      intro t ht _
      have hn := hpos t (Ioo_subset_Icc_self ht)
      have ho := (hord t (Ioo_subset_Icc_self ht)).2
      have hfactor : 0 ≤ (c + 1) * mu t - c * nu t := by
        nlinarith [mul_nonneg (show 0 ≤ c + 1 by linarith) (sub_nonneg.mpr ho)]
      have hp : 0 ≤ 2 * (c - 1) * nu t * ((c + 1) * mu t - c * nu t) := by
        positivity
      nlinarith)
    (sub_nonneg.mpr hpinch)
  intro t ht
  exact ⟨hpos t ht, (hord t ht).2, (hord t ht).1, sub_nonneg.mp (hratio t ht)⟩

end PoincareConjecture.AncientKappaRoundness
