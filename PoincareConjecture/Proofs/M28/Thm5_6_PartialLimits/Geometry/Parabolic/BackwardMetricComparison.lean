import PoincareConjecture.Proofs.M04.LocalMetricComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {tau K : ℝ}




theorem backward_metric_comparison
    (F : RicciFlow n M (Icc (-tau) 0)) (htau : 0 < tau) (hK : 0 ≤ K)
    (x : M) (hcurv : ∀ s ∈ Icc (-tau) 0, (F.connection s).curvatureTensorNorm x ≤ K)
    {t : ℝ} (ht : t ∈ Icc (-tau) 0) (v : TangentSpace (𝓡 n) x) :
    Real.exp (-2 * (n : ℝ) * K * tau) * (F.metric 0).inner x v v ≤
        (F.metric t).inner x v v ∧
      (F.metric t).inner x v v ≤
        Real.exp (2 * (n : ℝ) * K * tau) * (F.metric 0).inner x v v := by
  have h := M04.metric_comparison_at_of_curvature_bound F ht
    ⟨by linarith, le_rfl⟩ ht.2 hK x
    (fun s hs => hcurv s ⟨ht.1.trans hs.1, hs.2⟩) v
  have h0 : 0 ≤ (F.metric 0).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((F.metric 0).pos x v hv).le
  have hback := mul_le_mul_of_nonneg_left h.2
    (Real.exp_pos (-2 * (n : ℝ) * K * (0 - t))).le
  have hforward := mul_le_mul_of_nonneg_left h.1
    (Real.exp_pos (2 * (n : ℝ) * K * (0 - t))).le
  have he : Real.exp (-2 * (n : ℝ) * K * (0 - t)) *
      Real.exp (2 * (n : ℝ) * K * (0 - t)) = 1 := by
    rw [← Real.exp_add]
    rw [show -2 * (n : ℝ) * K * (0 - t) + 2 * (n : ℝ) * K * (0 - t) = 0 by ring,
      Real.exp_zero]
  have he' : Real.exp (2 * (n : ℝ) * K * (0 - t)) *
      Real.exp (-2 * (n : ℝ) * K * (0 - t)) = 1 := by
    rw [mul_comm]
    exact he
  rw [← mul_assoc, he, one_mul] at hback
  rw [← mul_assoc, he', one_mul] at hforward
  have hfactor : 0 ≤ 2 * (n : ℝ) * K := by positivity
  have htime : (2 * (n : ℝ) * K) * (0 - t) ≤ (2 * (n : ℝ) * K) * tau :=
    mul_le_mul_of_nonneg_left (by linarith [ht.1]) hfactor
  constructor
  · apply le_trans _ hback
    apply mul_le_mul_of_nonneg_right _ h0
    apply Real.exp_le_exp.mpr
    nlinarith
  · apply hforward.trans
    apply mul_le_mul_of_nonneg_right _ h0
    exact Real.exp_le_exp.mpr htime




theorem backward_pullback_ellipticity
    (F : RicciFlow n M (Icc (-tau) 0)) (htau : 0 < tau) (hK : 0 ≤ K)
    (e : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    (hcurv : ∀ s ∈ Icc (-tau) 0, (F.connection s).curvatureTensorNorm (e x) ≤ K)
    {a b : ℝ} (hterminal : ∀ v,
      a * ‖v‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients e x v v ∧
        (F.metric 0).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2)
    {t : ℝ} (ht : t ∈ Icc (-tau) 0) (v : EuclideanSpace ℝ (Fin n)) :
    (Real.exp (-2 * (n : ℝ) * K * tau) * a) * ‖v‖ ^ 2 ≤
        (F.metric t).pullbackCoefficients e x v v ∧
      (F.metric t).pullbackCoefficients e x v v ≤
        (Real.exp (2 * (n : ℝ) * K * tau) * b) * ‖v‖ ^ 2 := by
  have h := backward_metric_comparison F htau hK (e x) hcurv ht
    (mfderiv (𝓡 n) (𝓡 n) e x v)
  change Real.exp (-2 * (n : ℝ) * K * tau) *
      (F.metric 0).pullbackCoefficients e x v v ≤ (F.metric t).pullbackCoefficients e x v v ∧
    (F.metric t).pullbackCoefficients e x v v ≤ Real.exp (2 * (n : ℝ) * K * tau) *
      (F.metric 0).pullbackCoefficients e x v v at h
  constructor
  · simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left (hterminal v).1 (Real.exp_pos _).le).trans h.1
  · simpa only [mul_assoc] using
      h.2.trans (mul_le_mul_of_nonneg_left (hterminal v).2 (Real.exp_pos _).le)

end PoincareConjecture.M28
