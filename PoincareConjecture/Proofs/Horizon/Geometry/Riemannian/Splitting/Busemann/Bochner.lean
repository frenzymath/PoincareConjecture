import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Bochner

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem connection_gradient_eq_zero_of_harmonic_of_constant_normSq
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hRic : D.NonnegativeRicciCurvature)
    (hharm : ∀ x, D.laplacian f x = 0) {c : ℝ}
    (hconst : ∀ x, g.inner x (D.gradient f x) (D.gradient f x) = c)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    D.connection (D.gradient f) x v = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hb := D.bochner_identity hf x
  have hn : (fun y => g.inner y (D.gradient f y) (D.gradient f y)) =
      fun _ => c := funext hconst
  have hl : D.laplacian f = fun _ => 0 := funext hharm
  have hclap : D.laplacian (fun _ : M => c) x = 0 := by
    simp only [laplacian, hessian, hessianOnFields, mvfderiv_const,
      zero_apply, sub_self, Finset.sum_const_zero]
  rw [hn, hl, hclap, mvfderiv_const] at hb
  simp only [zero_apply, mul_zero, add_zero] at hb
  have hsum : (∑ i, ∑ j, (D.hessian f x
      (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) = 0 := by
    have hnonneg : 0 ≤ ∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hric := hRic x (D.gradient f x)
    linarith
  have hrow (i) : (∑ j, (D.hessian f x
      (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp hsum i
        (Finset.mem_univ i)
  have hbase (i) : D.connection (D.gradient f) x (g.orthonormalBasis x i) = 0 := by
    have h := hrow i
    rw [D.sum_hessian_sq_eq_inner_connection_gradient (hf x)] at h
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp h
  have hlin : (D.connection (D.gradient f) x).toLinearMap = 0 := by
    apply (g.orthonormalBasis x).toBasis.ext
    intro i
    exact hbase i
  exact congrArg (fun L => L v) hlin

theorem hessian_eq_zero_of_harmonic_of_constant_normSq
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hRic : D.NonnegativeRicciCurvature)
    (hharm : ∀ x, D.laplacian f x = 0) {c : ℝ}
    (hconst : ∀ x, g.inner x (D.gradient f x) (D.gradient f x) = c)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    D.hessian f x v w = 0 := by
  rw [D.hessian_eq_inner_connection_gradient (hf x),
    D.connection_gradient_eq_zero_of_harmonic_of_constant_normSq hf hRic hharm hconst]
  simp

end PoincareConjecture.LeviCivitaData
