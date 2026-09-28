import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Conservation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.Extrema

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem scalar_eq_exp_potential_difference_of_surface_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (p x : M) : D.scalarCurvature x =
      D.scalarCurvature p * Real.exp (f x - f p) := by
  obtain ⟨A, hA⟩ := D.exists_scalar_conservation_of_surface_soliton hf hsol
  calc
    D.scalarCurvature x = (D.scalarCurvature x * Real.exp (-f x)) * Real.exp (f x) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = (D.scalarCurvature p * Real.exp (-f p)) * Real.exp (f x) := by rw [hA x, hA p]
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem potential_eq_of_degenerate_critical_point (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {p : M} (hcrit : D.gradient f p = 0) (hR : D.scalarCurvature p = 2 * lambda)
    (x : M) : f x = f p := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨C, hC⟩ := D.exists_hamilton_conservation_of_surface_soliton hf hsol
  have he := (hC x).trans (hC p).symm
  rw [hcrit] at he
  simp only [map_zero, add_zero] at he
  rw [D.scalar_eq_exp_potential_difference_of_surface_soliton hf hsol p x, hR] at he
  have hnorm : 0 ≤ g.inner x (D.gradient f x) (D.gradient f x) := by
    change 0 ≤ inner ℝ (D.gradient f x) (D.gradient f x)
    exact real_inner_self_nonneg
  by_contra hne
  have hexp := Real.add_one_lt_exp (sub_ne_zero.mpr hne)
  have hmul := mul_lt_mul_of_pos_left hexp (show 0 < 2 * lambda by positivity)
  nlinarith

theorem round_of_degenerate_critical_point (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {p : M} (hcrit : D.gradient f p = 0) (hR : D.scalarCurvature p = 2 * lambda) :
    ConstantPositiveSectionalCurvature g D := by
  refine ⟨lambda, hlambda, fun x u v hu hv huv => ?_⟩
  have hfx := D.potential_eq_of_degenerate_critical_point hlambda hf hsol hcrit hR x
  have hRx := D.scalar_eq_exp_potential_difference_of_surface_soliton hf hsol p x
  rw [hfx, sub_self, Real.exp_zero, mul_one, hR] at hRx
  rw [D.sectionalCurvature_eq_half_scalarCurvature x u v (by simp [hu, hv, huv]), hRx]
  ring

end PoincareConjecture.LeviCivitaData
