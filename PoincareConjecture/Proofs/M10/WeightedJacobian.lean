import PoincareConjecture.Proofs.M10.Density

set_option autoImplicit false

namespace PoincareConjecture.M10

theorem weightedJacobian_hasDerivAt {n : ℕ} {a J : ℝ → ℝ} {d R L t : ℝ}
    (ht : 0 < t) (ha : HasDerivAt a d t) (hJ : HasDerivAt J (J t * (R + L)) t) :
    HasDerivAt (fun s ↦ Real.rpow s (-(n : ℝ) / 2) * Real.exp (-a s) * J s)
      ((Real.rpow t (-(n : ℝ) / 2) * Real.exp (-a t) * J t) *
        (R + L - d - (n : ℝ) / (2 * t))) t := by
  have hp := Real.hasDerivAt_rpow_const (p := -(n : ℝ) / 2) (Or.inl ht.ne')
  apply ((hp.mul ha.neg.exp).mul hJ).congr_deriv
  rw [Real.rpow_sub_one ht.ne']
  simp only [Pi.neg_apply, Real.rpow_eq_pow, Pi.mul_apply]
  ring

theorem weightedJacobian_deriv_nonpos {n : ℕ} {a J : ℝ → ℝ} {D Q R L t : ℝ}
    (ht : 0 < t) (ha : HasDerivAt a (D + Q) t)
    (hJ : HasDerivAt J (J t * (R + L)) t) (hJnonneg : 0 ≤ J t)
    (hres : 0 ≤ D - L + Q - R + (n : ℝ) / (2 * t)) :
    deriv (fun s ↦ Real.rpow s (-(n : ℝ) / 2) * Real.exp (-a s) * J s) t ≤ 0 := by
  rw [(weightedJacobian_hasDerivAt ht ha hJ).deriv]
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact mul_nonneg (mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)).le hJnonneg
  · linarith

end PoincareConjecture.M10
