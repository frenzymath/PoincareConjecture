import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ScalarEstimate
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.LowDimension
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_uniform_scalarCurvature_bound_of_reciprocal_time_bound
    {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (F : RicciFlow (m + 1) M J) {a b S K : ℝ}
    (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M,
      ∀ v : TangentSpace (𝓡 (m + 1)) x, 0 ≤ (F.connection t).ricci x v v)
    (hinitial : ∀ x : M, (F.connection a).scalarCurvature x ≤ S)
    (htime : ∀ t ∈ Ioc a b, ∀ x : M,
      (F.connection t).scalarCurvature x ≤ K / (t - a)) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).scalarCurvature x ≤ B := by
  obtain ⟨C, hCpos, hlocal⟩ := exists_local_scalar_curvature_constant_of_finite m hm
  let S₀ := max S 1
  let r := 1 / Real.sqrt S₀
  have hS₀ : 0 < S₀ := zero_lt_one.trans_le (le_max_right _ _)
  have hr : 0 < r := div_pos zero_lt_one (Real.sqrt_pos.mpr hS₀)
  have hrsq : 1 / r ^ 2 = S₀ := by
    dsimp only [r]
    rw [div_pow, one_pow, Real.sq_sqrt hS₀.le, one_div_one_div]
  refine ⟨Real.exp (C * max K 1) / r ^ 2, by positivity, ?_⟩
  intro t ht x
  have hself : (F.metric t).edist x x = 0 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    exact Manifold.riemannianEDist_self
  have hx : x ∈ (F.metric t).ball x r := by
    change (F.metric t).edist x x < ENNReal.ofReal r
    rw [hself]
    exact ENNReal.ofReal_pos.mpr hr
  have h := hlocal M hC J F a b r (max K 1) hJ hr (le_max_right _ _)
    hcomplete hRic x (fun y _ => (hinitial y).trans (hrsq ▸ le_max_left S 1))
    (fun s hs y _ => (htime s hs y).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (sub_nonneg.mpr hs.1.le))) t ht x hx
  simpa only [hself, ENNReal.toReal_zero, sub_zero] using h

theorem exists_uniform_curvatureTensorNorm_bound_on_component_of_reciprocal_time_bound
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M J) (p : M) {a b K : ℝ}
    (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a b, ∀ x ∈ connectedComponent p,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hinitial : ∃ S : ℝ, 0 ≤ S ∧ ∀ x ∈ connectedComponent p,
      (F.connection a).CurvatureOperatorBound S x)
    (htime : ∀ t ∈ Ioc a b, ∀ x ∈ connectedComponent p,
      (F.connection t).scalarCurvature x ≤ K / (t - a)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x ∈ connectedComponent p,
      (F.connection t).curvatureTensorNorm x ≤ B := by
  by_cases hn : n ≤ 1
  · exact ⟨0, le_rfl, fun t _ x _ =>
      F.curvatureTensorNorm_bound_zero_of_dimension_le_one hn t x⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm : 0 < m := by omega
  let G := F.restrictComponent p
  obtain ⟨S, hS, hinit⟩ := hinitial
  have hscalar (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin (m + 1))) p) :
      (G.connection a).scalarCurvature x ≤
        ((m + 1 : ℕ) : ℝ) ^ 2 * (((m + 1 : ℕ) : ℝ) ^ 2 * S) := by
    rw [F.restrictComponent_scalarCurvature]
    exact (le_abs_self _).trans
      (((F.connection a).abs_scalarCurvature_le_curvatureTensorNorm x).trans
        (mul_le_mul_of_nonneg_left
          ((F.connection a).curvatureTensorNorm_le_of_operator_bound x S hS
            (hinit x x.property) (hC.tensor_calculus _ M _ _)) (sq_nonneg _)))
  obtain ⟨B, hB, hb⟩ :=
    G.exists_uniform_scalarCurvature_bound_of_reciprocal_time_bound hC hm hJ
      (fun t ht => F.restrictComponent_metricComplete p t (hcomplete t ht))
      (fun t ht x v => ((G.connection t).ricci_bounds_of_nonnegative_curvatureOperator
        (hC.tensor_calculus _ _ _ _) x
        ((F.restrictComponent_nonnegativeCurvatureOperator_iff p t x).mpr
          (hoperator t ht x x.property)) v).1) hscalar (by
        intro t ht x
        rw [F.restrictComponent_scalarCurvature]
        exact htime t ht x x.property)
  refine ⟨((m + 1 : ℕ) : ℝ) ^ 2 * B, by positivity, ?_⟩
  intro t ht x hx
  have h := hb t ht ⟨x, hx⟩
  rw [F.restrictComponent_scalarCurvature] at h
  exact ((F.connection t).curvatureTensorNorm_le_scalarCurvature
    (hC.tensor_calculus _ M _ _) x (hoperator t ht x hx)).trans
      (mul_le_mul_of_nonneg_left h (sq_nonneg _))

end PoincareConjecture.RicciFlow
