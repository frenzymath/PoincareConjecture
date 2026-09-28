import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.Degenerate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem gradient_normSq_eq_at_critical_point (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {p : M} (hp : D.gradient f p = 0) (x : M) :
    g.inner x (D.gradient f x) (D.gradient f x) =
      2 * lambda * (f x - f p) -
        D.scalarCurvature p * (Real.exp (f x - f p) - 1) := by
  obtain ⟨C, hC⟩ := D.exists_hamilton_conservation_of_surface_soliton hf hsol
  have he := (hC x).trans (hC p).symm
  rw [hp] at he
  simp only [map_zero, add_zero] at he
  rw [D.scalar_eq_exp_potential_difference_of_surface_soliton hf hsol p x] at he
  nlinarith

theorem isMinOn_of_critical_scalar_le (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {p : M} (hp : D.gradient f p = 0)
    (hR : 0 ≤ D.scalarCurvature p) (hbound : D.scalarCurvature p ≤ 2 * lambda) :
    IsMinOn f univ p := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro x _
  have he := D.gradient_normSq_eq_at_critical_point hf hsol hp x
  have hnorm : 0 ≤ g.inner x (D.gradient f x) (D.gradient f x) := by
    change 0 ≤ inner ℝ (D.gradient f x) (D.gradient f x)
    exact real_inner_self_nonneg
  by_contra h
  have hneg : f x - f p < 0 := sub_neg.mpr (lt_of_not_ge h)
  rcases eq_or_lt_of_le hR with hz | hpos
  · rw [← hz] at he
    have hm := mul_neg_of_pos_of_neg (show 0 < 2 * lambda by positivity) hneg
    nlinarith
  · have hexp := mul_lt_mul_of_pos_left (Real.add_one_lt_exp hneg.ne) hpos
    have hsign := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hbound) hneg.le
    nlinarith

theorem isMaxOn_of_critical_scalar_ge (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {p : M} (hp : D.gradient f p = 0) (hbound : 2 * lambda ≤ D.scalarCurvature p) :
    IsMaxOn f univ p := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro x _
  have he := D.gradient_normSq_eq_at_critical_point hf hsol hp x
  have hnorm : 0 ≤ g.inner x (D.gradient f x) (D.gradient f x) := by
    change 0 ≤ inner ℝ (D.gradient f x) (D.gradient f x)
    exact real_inner_self_nonneg
  by_contra h
  have hpos : 0 < f x - f p := sub_pos.mpr (lt_of_not_ge h)
  have hR : 0 < D.scalarCurvature p := (by positivity : 0 < 2 * lambda).trans_le hbound
  have hexp := mul_lt_mul_of_pos_left (Real.add_one_lt_exp hpos.ne') hR
  have hsign := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbound) hpos.le
  nlinarith

theorem isMinOn_or_isMaxOn_of_critical_point (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {p : M} (hp : D.gradient f p = 0) (hR : 0 ≤ D.scalarCurvature p) :
    IsMinOn f univ p ∨ IsMaxOn f univ p := by
  rcases le_total (D.scalarCurvature p) (2 * lambda) with h | h
  · exact Or.inl (D.isMinOn_of_critical_scalar_le hlambda hf hsol hp hR h)
  · exact Or.inr (D.isMaxOn_of_critical_scalar_ge hlambda hf hsol hp h)

end PoincareConjecture.LeviCivitaData
