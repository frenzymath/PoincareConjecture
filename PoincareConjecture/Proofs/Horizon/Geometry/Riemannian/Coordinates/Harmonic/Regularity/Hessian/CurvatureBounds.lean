import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.RicciContraction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.NormBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private lemma abs_inner_le_intrinsic (x : EuclideanSpace ℝ (Fin n))
    (u v : TangentSpace (𝓡 n) x) :
    |g.inner x u v| ≤ g.tangentNorm x u * g.tangentNorm x v := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm (w : TangentSpace (𝓡 n) x) : g.tangentNorm x w = ‖w‖ := by
    change Real.sqrt (inner ℝ w w) = ‖w‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)]
  change |inner ℝ u v| ≤ _
  rw [hnorm, hnorm]
  exact abs_real_inner_le_norm u v

private lemma intrinsic_basis_norm (x : EuclideanSpace ℝ (Fin n))
    (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    g.tangentNorm x (g.orthonormalBasis x i) = 1 := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Real.sqrt (inner ℝ (g.orthonormalBasis x i) (g.orthonormalBasis x i)) = 1
  rw [real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one]
  norm_num

theorem abs_hessian_curvature_flux_le (D : LeviCivitaData g)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x a b c : EuclideanSpace ℝ (Fin n)) :
    |g.inner x a b * D.ricci x (D.gradient f x) c -
      mvfderiv (𝓡 n) f x (D.curvature x a b c)| ≤
      ((n : ℝ) + 1) * D.curvatureTensorNorm x * g.tangentNorm x (D.gradient f x) *
        g.tangentNorm x a * g.tangentNorm x b * g.tangentNorm x c := by
  have hnorm (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ g.tangentNorm x v :=
    Real.sqrt_nonneg _
  have hfirst := mul_le_mul
    (abs_inner_le_intrinsic (g := g) x a b)
    (D.abs_ricci_le_tangentNorm x (D.gradient f x) c)
    (abs_nonneg _) (mul_nonneg (hnorm a) (hnorm b))
  have hsecond : |mvfderiv (𝓡 n) f x (D.curvature x a b c)| ≤
      g.tangentNorm x (D.gradient f x) * (D.curvatureTensorNorm x *
        g.tangentNorm x a * g.tangentNorm x b * g.tangentNorm x c) := by
    rw [← D.inner_gradient]
    exact (abs_inner_le_intrinsic (g := g) x _ _).trans
      (mul_le_mul_of_nonneg_left (D.tangentNorm_curvature_le x a b c) (hnorm _))
  calc
    _ ≤ |g.inner x a b * D.ricci x (D.gradient f x) c| +
        |mvfderiv (𝓡 n) f x (D.curvature x a b c)| := abs_sub _ _
    _ = |g.inner x a b| * |D.ricci x (D.gradient f x) c| +
        |mvfderiv (𝓡 n) f x (D.curvature x a b c)| := by rw [abs_mul]
    _ ≤ (g.tangentNorm x a * g.tangentNorm x b) *
        ((n : ℝ) * D.curvatureTensorNorm x * g.tangentNorm x (D.gradient f x) *
          g.tangentNorm x c) + g.tangentNorm x (D.gradient f x) *
        (D.curvatureTensorNorm x * g.tangentNorm x a * g.tangentNorm x b *
          g.tangentNorm x c) := add_le_add hfirst hsecond
    _ = _ := by ring

theorem sum_sq_hessian_curvature_flux_le (D : LeviCivitaData g)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    let e := g.orthonormalBasis x
    (∑ k, ∑ i, ∑ j, (g.inner x (e k) (e i) * D.ricci x (D.gradient f x) (e j) -
      mvfderiv (𝓡 n) f x (D.curvature x (e k) (e i) (e j))) ^ 2) ≤
      (n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2 * D.curvatureTensorNorm x ^ 2 *
        g.tangentNorm x (D.gradient f x) ^ 2 := by
  let e := g.orthonormalBasis x
  let L := ((n : ℝ) + 1) * D.curvatureTensorNorm x * g.tangentNorm x (D.gradient f x)
  have hL : 0 ≤ L := by dsimp [L, curvatureTensorNorm, RiemannianMetric.tangentNorm]; positivity
  have hterm (k i j) :
      (g.inner x (e k) (e i) * D.ricci x (D.gradient f x) (e j) -
        mvfderiv (𝓡 n) f x (D.curvature x (e k) (e i) (e j))) ^ 2 ≤ L ^ 2 := by
    have h := D.abs_hessian_curvature_flux_le f x (e k) (e i) (e j)
    simp only [e, intrinsic_basis_norm, mul_one] at h
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hL).mpr h
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simp
  calc
    _ ≤ ∑ k : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          ∑ j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)), L ^ 2 :=
      Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hterm k i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hdim]
      dsimp [L]
      ring

theorem abs_two_tensor_curvature_trace_le (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hT : IsSmoothCovariantTensor T) (x a b : EuclideanSpace ℝ (Fin n)) :
    |-(∑ k, (T x ![D.curvature x (g.orthonormalBasis x k) a (g.orthonormalBasis x k), b] +
      T x ![g.orthonormalBasis x k, D.curvature x (g.orthonormalBasis x k) a b]))| ≤
      2 * (n : ℝ) * D.curvatureTensorNorm x * g.tensorNorm T x *
        g.tangentNorm x a * g.tangentNorm x b := by
  obtain ⟨A, hA⟩ := hT.1 x
  have hnorm (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ g.tangentNorm x v :=
    Real.sqrt_nonneg _
  have hTnorm : 0 ≤ g.tensorNorm T x := Real.sqrt_nonneg _
  have heval (v w : EuclideanSpace ℝ (Fin n)) :
      |T x ![v, w]| ≤ g.tensorNorm T x * g.tangentNorm x v * g.tangentNorm x w := by
    simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc] using
      abs_tensor_evaluation_le_tensorNorm g T x A hA ![v, w]
  have hterm (k) :
      |T x ![D.curvature x (g.orthonormalBasis x k) a (g.orthonormalBasis x k), b]| +
        |T x ![g.orthonormalBasis x k, D.curvature x (g.orthonormalBasis x k) a b]| ≤
      2 * D.curvatureTensorNorm x * g.tensorNorm T x * g.tangentNorm x a * g.tangentNorm x b := by
    have hR₁ := D.tangentNorm_curvature_le x (g.orthonormalBasis x k) a
      (g.orthonormalBasis x k)
    have hR₂ := D.tangentNorm_curvature_le x (g.orthonormalBasis x k) a b
    simp only [intrinsic_basis_norm, mul_one] at hR₁ hR₂
    have h₁ := (heval (D.curvature x (g.orthonormalBasis x k) a
      (g.orthonormalBasis x k)) b).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR₁ hTnorm) (hnorm b))
    have h₂ := heval (g.orthonormalBasis x k) (D.curvature x (g.orthonormalBasis x k) a b)
    simp only [intrinsic_basis_norm, mul_one] at h₂
    have h₂' := h₂.trans (mul_le_mul_of_nonneg_left hR₂ hTnorm)
    calc
      _ ≤ _ := add_le_add h₁ h₂'
      _ = _ := by ring
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simp
  rw [abs_neg]
  calc
    _ ≤ ∑ k, |T x ![D.curvature x (g.orthonormalBasis x k) a (g.orthonormalBasis x k), b] +
        T x ![g.orthonormalBasis x k, D.curvature x (g.orthonormalBasis x k) a b]| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (|T x ![D.curvature x (g.orthonormalBasis x k) a (g.orthonormalBasis x k), b]| +
        |T x ![g.orthonormalBasis x k, D.curvature x (g.orthonormalBasis x k) a b]|) :=
      Finset.sum_le_sum fun _ _ => abs_add_le _ _
    _ ≤ ∑ _k : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        2 * D.curvatureTensorNorm x * g.tensorNorm T x * g.tangentNorm x a * g.tangentNorm x b :=
      Finset.sum_le_sum fun k _ => hterm k
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hdim]
      ring

theorem sum_sq_two_tensor_curvature_trace_le (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hT : IsSmoothCovariantTensor T) (x : EuclideanSpace ℝ (Fin n)) :
    let e := g.orthonormalBasis x
    (∑ i, ∑ j, (-(∑ k, (T x ![D.curvature x (e k) (e i) (e k), e j] +
      T x ![e k, D.curvature x (e k) (e i) (e j)]))) ^ 2) ≤
      4 * (n : ℝ) ^ 4 * D.curvatureTensorNorm x ^ 2 * g.tensorNorm T x ^ 2 := by
  let e := g.orthonormalBasis x
  let L := 2 * (n : ℝ) * D.curvatureTensorNorm x * g.tensorNorm T x
  have hL : 0 ≤ L := by dsimp [L, curvatureTensorNorm, RiemannianMetric.tensorNorm]; positivity
  have hterm (i j) :
      (-(∑ k, (T x ![D.curvature x (e k) (e i) (e k), e j] +
        T x ![e k, D.curvature x (e k) (e i) (e j)]))) ^ 2 ≤ L ^ 2 := by
    have h := D.abs_two_tensor_curvature_trace_le hT x (e i) (e j)
    simp only [e, intrinsic_basis_norm, mul_one] at h
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hL).mpr h
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simp
  calc
    _ ≤ ∑ i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)), L ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hdim]
      dsimp [L]
      ring

end PoincareConjecture.LeviCivitaData
