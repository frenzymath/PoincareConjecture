import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Basic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison
import PoincareConjecture.Proofs.M07.Analysis.ODE.LogDerivative

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RicciFlow

theorem metric_inner_self_exp_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J I : Set ℝ} (F : RicciFlow n M J)
    (hI : Convex ℝ I) (hIJ : I ⊆ J)
    (x : M) (v : TangentSpace (𝓡 n) x) (K : ℝ)
    (hRic : ∀ t ∈ I,
      |(F.connection t).ricci x v v| ≤ K * (F.metric t).inner x v v)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    Real.exp (-(2 * K) * |b - a|) * (F.metric a).inner x v v ≤
        (F.metric b).inner x v v ∧
      (F.metric b).inner x v v ≤
        Real.exp ((2 * K) * |b - a|) * (F.metric a).inner x v v := by
  by_cases hv : v = 0
  · subst v
    simp
  apply Poincare.exp_bounds_of_abs_deriv_le_mul hI
    (fun t _ ↦ (F.metric t).pos x v hv)
    (fun t ht ↦ (F.equation t (hIJ ht) x v v).mono hIJ) ?_ ha hb
  intro t ht
  calc
    |-2 * (F.connection t).ricci x v v| =
        2 * |(F.connection t).ricci x v v| := by rw [abs_mul]; norm_num
    _ ≤ 2 * (K * (F.metric t).inner x v v) :=
      mul_le_mul_of_nonneg_left (hRic t ht) (by norm_num)
    _ = (2 * K) * (F.metric t).inner x v v := by ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem tangentNorm_le_exp_of_ricci_bound
    (F : RicciFlow n M J) {I : Set ℝ} (hI : Convex ℝ I) (hIJ : I ⊆ J)
    (x : M) (v : TangentSpace (𝓡 n) x) (K : ℝ)
    (hRic : ∀ t ∈ I,
      |(F.connection t).ricci x v v| ≤ K * (F.metric t).inner x v v)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    (F.metric t).tangentNorm x v ≤
      Real.exp (K * |t - s|) * (F.metric s).tangentNorm x v := by
  have h := (F.metric_inner_self_exp_bounds hI hIJ x v K hRic hs ht).2
  have hexp : Real.exp ((2 * K) * |t - s|) =
      Real.exp (K * |t - s|) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsqrt := Real.sqrt_le_sqrt h
  rw [hexp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_nonneg _)] at hsqrt
  exact hsqrt

theorem ball_subset_ball_of_ricci_bound
    (F : RicciFlow n M J) {I : Set ℝ} (hI : Convex ℝ I) (hIJ : I ⊆ J)
    (p : M) (r K : ℝ) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I)
    (hRic : ∀ τ ∈ I, ∀ x ∈ (F.metric s).ball p r,
      ∀ v : TangentSpace (𝓡 n) x,
        |(F.connection τ).ricci x v v| ≤ K * (F.metric τ).inner x v v) :
    (F.metric s).ball p r ⊆
      (F.metric t).ball p (Real.exp (K * |t - s|) * r) := by
  apply RiemannianMetric.ball_subset_ball_of_tangentNorm_le
    _ _ _ _ _ (Real.exp_pos _)
  intro x hx v
  exact F.tangentNorm_le_exp_of_ricci_bound hI hIJ x v K
    (fun τ hτ ↦ hRic τ hτ x hx v) hs ht

theorem edist_le_exp_mul_of_ricci_bound
    (F : RicciFlow n M J) {I : Set ℝ} (hI : Convex ℝ I) (hIJ : I ⊆ J)
    (p : M) (r K : ℝ) (hr : 0 < r) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I)
    (hRic : ∀ τ ∈ I, ∀ z ∈ (F.metric s).ball p (3 * r),
      ∀ v : TangentSpace (𝓡 n) z,
        |(F.connection τ).ricci z v v| ≤ K * (F.metric τ).inner z v v)
    {x y : M} (hx : x ∈ (F.metric s).ball p r)
    (hy : y ∈ (F.metric s).ball p r) :
    (F.metric t).edist x y ≤ ENNReal.ofReal (Real.exp (K * |t - s|)) *
      (F.metric s).edist x y := by
  apply RiemannianMetric.edist_le_mul_edist_of_tangentNorm_le_on_ball
    _ _ p r _ hr (Real.exp_pos _) _ hx hy
  intro z hz v
  exact F.tangentNorm_le_exp_of_ricci_bound hI hIJ z v K
    (fun τ hτ ↦ hRic τ hτ z hz v) hs ht

end PoincareConjecture.RicciFlow
