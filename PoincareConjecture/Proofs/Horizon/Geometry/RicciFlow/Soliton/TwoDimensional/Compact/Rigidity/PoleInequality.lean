import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.Degenerate
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.CriticalValues










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}



theorem four_scale_lt_scalar_sum_at_critical_points (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {p q : M} (hp : D.gradient f p = 0) (hq : D.gradient f q = 0)
    (hpq : f p < f q) : 4 * lambda < D.scalarCurvature p + D.scalarCurvature q := by
  obtain ⟨C, hC⟩ := D.exists_hamilton_conservation_of_surface_soliton hf hsol
  have he := (hC q).trans (hC p).symm
  rw [hp, hq] at he
  simp only [map_zero, add_zero] at he
  have hR := D.scalar_eq_exp_potential_difference_of_surface_soliton hf hsol p q
  have hdiff : 0 < f q - f p := sub_pos.mpr hpq
  have henergy : D.scalarCurvature p * (Real.exp (f q - f p) - 1) =
      2 * lambda * (f q - f p) := by
    rw [hR] at he
    nlinarith
  have hexp : 0 < Real.exp (f q - f p) - 1 := by
    have h := Real.exp_lt_exp.mpr hdiff
    rw [Real.exp_zero] at h
    linarith
  have hpos : 0 < D.scalarCurvature p := by
    apply pos_of_mul_pos_left (b := Real.exp (f q - f p) - 1) _ hexp.le
    rw [henergy]
    positivity
  have hstrict := mul_lt_mul_of_pos_left
    (SurfaceSoliton.exp_secant_lt_endpoint_average hdiff) hpos
  have hleft : D.scalarCurvature p * (2 * (Real.exp (f q - f p) - 1)) =
      (f q - f p) * (4 * lambda) := by nlinarith [henergy]
  have hright : D.scalarCurvature p * ((f q - f p) * (Real.exp (f q - f p) + 1)) =
      (f q - f p) * (D.scalarCurvature p + D.scalarCurvature q) := by
    rw [hR]
    ring
  rw [hleft, hright] at hstrict
  exact (mul_lt_mul_iff_right₀ hdiff).mp hstrict

end PoincareConjecture.LeviCivitaData
