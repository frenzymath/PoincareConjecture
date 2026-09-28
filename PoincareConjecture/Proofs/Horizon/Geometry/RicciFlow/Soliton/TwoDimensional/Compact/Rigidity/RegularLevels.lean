import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.GlobalExtrema
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.PoleInequality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem scalar_lt_twice_scale_at_min_of_not_round (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (hnot : ¬ ConstantPositiveSectionalCurvature g D)
    {p : M} (hp : IsLocalMin f p) : D.scalarCurvature p < 2 * lambda := by
  have hfs := D.contMDiff_of_C2_surface_soliton hf hsol
  apply lt_of_le_of_ne (D.scalar_le_twice_scale_of_potential_min hfs hsol hp)
  intro heq
  exact hnot (D.round_of_degenerate_critical_point hlambda hf hsol
    (D.gradient_eq_zero_of_potential_min hfs hp) heq)

theorem twice_scale_lt_scalar_at_max_of_not_round (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (hnot : ¬ ConstantPositiveSectionalCurvature g D)
    {p : M} (hp : IsLocalMax f p) : 2 * lambda < D.scalarCurvature p := by
  have hfs := D.contMDiff_of_C2_surface_soliton hf hsol
  apply lt_of_le_of_ne (D.twice_scale_le_scalar_of_potential_max hfs hsol hp)
  intro heq
  exact hnot (D.round_of_degenerate_critical_point hlambda hf hsol
    (D.gradient_eq_zero_of_potential_max hfs hp) heq.symm)

theorem gradient_ne_zero_at_intermediate_value (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {p q x : M} (hpx : f p < f x) (hxq : f x < f q)
    (hR : 0 ≤ D.scalarCurvature x) : D.gradient f x ≠ 0 := by
  intro hx
  rcases D.isMinOn_or_isMaxOn_of_critical_point hlambda hf hsol hx hR with hmin | hmax
  · exact (not_lt_of_ge (hmin (mem_univ p))) hpx
  · exact (not_lt_of_ge (hmax (mem_univ q))) hxq

theorem exists_strict_extrema_of_compact_not_round [CompactSpace M] [Nonempty M]
    (D : LeviCivitaData g) {f : M → ℝ} {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (hnot : ¬ ConstantPositiveSectionalCurvature g D) :
    ∃ p q : M, (∀ x, f p ≤ f x ∧ f x ≤ f q) ∧
      D.gradient f p = 0 ∧ D.gradient f q = 0 ∧ f p < f q ∧
      D.scalarCurvature p < 2 * lambda ∧ 2 * lambda < D.scalarCurvature q ∧
      4 * lambda < D.scalarCurvature p + D.scalarCurvature q := by
  have hfs := D.contMDiff_of_C2_surface_soliton hf hsol
  obtain ⟨z⟩ := ‹Nonempty M›
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn ⟨z, mem_univ z⟩ hf.continuous.continuousOn
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMaxOn ⟨z, mem_univ z⟩ hf.continuous.continuousOn
  have hp' := hp.isLocalMin Filter.univ_mem
  have hq' := hq.isLocalMax Filter.univ_mem
  have hgp := D.gradient_eq_zero_of_potential_min hfs hp'
  have hgq := D.gradient_eq_zero_of_potential_max hfs hq'
  have hRp := D.scalar_lt_twice_scale_at_min_of_not_round hlambda hf hsol hnot hp'
  have hRq := D.twice_scale_lt_scalar_at_max_of_not_round hlambda hf hsol hnot hq'
  have hpq : f p < f q := by
    apply lt_of_le_of_ne (hp (mem_univ q))
    intro heq
    have hR := D.scalar_eq_exp_potential_difference_of_surface_soliton hf hsol p q
    rw [heq, sub_self, Real.exp_zero, mul_one] at hR
    linarith
  exact ⟨p, q, fun x => ⟨hp (mem_univ x), hq (mem_univ x)⟩,
    hgp, hgq, hpq, hRp, hRq,
    D.four_scale_lt_scalar_sum_at_critical_points hlambda hf hsol hgp hgq hpq⟩

end PoincareConjecture.LeviCivitaData
