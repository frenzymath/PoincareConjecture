import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingTransport

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

theorem m64Intrinsic_pushed_focusing_norm_le_inv_kappa
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    {x : AnnulusCoordinates} (hx : 0 < ‖x‖) {kappa : ℝ}
    (hkappa : 0 < kappa) (hpi : kappa * ‖x‖ < Real.pi)
    (hgauss : ∀ v : AnnulusCoordinates,
      N.metric.pullbackCoefficients e x x v = inner ℝ x v) :
    N.metric.tangentNorm (e x)
        (fderiv ℝ e x
          ((Real.sin (kappa * ‖x‖) / (kappa * ‖x‖)) • x)) ≤
      kappa⁻¹ := by
  rw [m64Intrinsic_pushed_focusing_norm N e hx hkappa hpi hgauss]
  simpa only [inv_eq_one_div] using
    (div_le_div_of_nonneg_right (Real.sin_le_one (kappa * ‖x‖)) hkappa.le)

end PoincareConjecture
