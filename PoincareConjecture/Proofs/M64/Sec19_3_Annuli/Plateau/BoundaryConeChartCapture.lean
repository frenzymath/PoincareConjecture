import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeH1Radius

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Metric

namespace PoincareConjecture.M64BoundaryCone

theorem semicircle_chart_capture {M E C : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup C]
    (e : M → E) (H : E → C) (A : C → M) (q0 : M)
    {rho delta : ℝ} (hdelta : 0 < delta)
    (hcap : ∀ q : M, dist (e q) (e q0) < delta →
      ‖H (e q)‖ < rho / 4 ∧ A (H (e q)) = q)
    (gamma : ℝ → M) (W : ℝ → E)
    (hW : MemLp W 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hFTC : ∀ theta ∈ Icc (0 : ℝ) Real.pi,
      e (gamma theta) - e (gamma 0) = ∫ s in (0 : ℝ)..theta, W s)
    (hfirst : dist (e (gamma 0)) (e q0) < delta / 2)
    (hsmall : Real.pi * (∫ theta in Icc (0 : ℝ) Real.pi, ‖W theta‖ ^ 2) <
      (delta / 2) ^ 2) :
    MapsTo (H ∘ e ∘ gamma) (Icc (0 : ℝ) Real.pi) (ball 0 (rho / 4)) ∧
      ∀ theta ∈ Icc (0 : ℝ) Real.pi, A (H (e (gamma theta))) = gamma theta := by
  have hnear (theta : ℝ) (htheta : theta ∈ Icc (0 : ℝ) Real.pi) :
      dist (e (gamma theta)) (e q0) < delta := by
    have hs := m64H1Trace_radius_sq_le (e ∘ gamma) W hW hFTC htheta
    have hd : dist (e (gamma theta)) (e (gamma 0)) < delta / 2 := by
      rw [dist_eq_norm]
      change ‖e (gamma theta) - e (gamma 0)‖ ^ 2 ≤ _ at hs
      nlinarith [norm_nonneg (e (gamma theta) - e (gamma 0))]
    exact (dist_triangle _ (e (gamma 0)) _).trans_lt
      ((add_lt_add hd hfirst).trans_eq (by ring))
  refine ⟨fun theta htheta => ?_, fun theta htheta => (hcap _ (hnear theta htheta)).2⟩
  simpa only [Function.comp_apply, mem_ball, dist_zero_right] using
    (hcap _ (hnear theta htheta)).1

end PoincareConjecture.M64BoundaryCone
