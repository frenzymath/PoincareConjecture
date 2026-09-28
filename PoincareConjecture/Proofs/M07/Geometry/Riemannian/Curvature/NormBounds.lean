import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Bilinear

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem abs_ricci_quadratic_le_of_expansion
    (D : LeviCivitaData g) (x : M) (v : TangentSpace (𝓡 n) x)
    (hcoord : D.ricci x v v =
      let b := g.orthonormalBasis x
      ∑ a, ∑ i, ∑ j,
        (g.inner x v (b i)) * (g.inner x v (b j)) *
          D.curvatureTensor x (b i) (b a) (b j) (b a))
    (hcoeff : ∀ i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      (g.inner x v (g.orthonormalBasis x i)) ^ 2 ≤ g.inner x v v)
    (hQ : 0 ≤ g.inner x v v) :
    |D.ricci x v v| ≤
      (Fintype.card (Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) : ℝ) ^ 3 *
        D.curvatureTensorNorm x * g.inner x v v := by
  let b := g.orthonormalBasis x
  let I := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let R : I → I → I → I → ℝ :=
    fun i a j c => D.curvatureTensor x (b i) (b a) (b j) (b c)
  let N : ℝ := D.curvatureTensorNorm x
  have hN : 0 ≤ N := by
    dsimp [N, LeviCivitaData.curvatureTensorNorm]
    exact Real.sqrt_nonneg _
  have hcomp (i a j : I) : |R i a j a| ≤ N := by
    have hsq : (R i a j a) ^ 2 ≤
        ∑ p, ∑ q, ∑ r, ∑ s, (R p q r s) ^ 2 := by
      let S₂ := ∑ p : I, ∑ q : I, ∑ r : I, ∑ s : I, (R p q r s) ^ 2
      calc
        (R i a j a) ^ 2 ≤ ∑ s : I, (R i a j s) ^ 2 := by
          apply Finset.single_le_sum
            (fun s _ => sq_nonneg _)
          exact Finset.mem_univ _
        _ ≤ ∑ r : I, ∑ s : I, (R i a r s) ^ 2 := by
          apply Finset.single_le_sum
            (fun r _ => Finset.sum_nonneg (fun s _ => sq_nonneg _))
          exact Finset.mem_univ _
        _ ≤ ∑ q : I, ∑ r : I, ∑ s : I, (R i q r s) ^ 2 := by
          apply Finset.single_le_sum
            (fun q _ => Finset.sum_nonneg (fun r _ =>
              Finset.sum_nonneg (fun s _ => sq_nonneg _)))
          exact Finset.mem_univ _
        _ ≤ S₂ := by
          apply Finset.single_le_sum
            (fun p _ => Finset.sum_nonneg (fun q _ =>
              Finset.sum_nonneg (fun r _ =>
                Finset.sum_nonneg (fun s _ => sq_nonneg _))))
          exact Finset.mem_univ _
    change |R i a j a| ≤ Real.sqrt (∑ p, ∑ q, ∑ r, ∑ s, (R p q r s) ^ 2)
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    have hS : 0 ≤ ∑ p : I, ∑ q : I, ∑ r : I, ∑ s : I, (R p q r s) ^ 2 := by
      exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun q _ =>
        Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => sq_nonneg _))))
    rw [sq_abs, Real.sq_sqrt hS]
    exact hsq
  have hterm (a i j : I) :
      |(g.inner x v (b i)) * (g.inner x v (b j)) * R i a j a| ≤
        N * g.inner x v v := by
    have hi := hcoeff i
    have hj := hcoeff j
    have hi' : |g.inner x v (b i)| ^ 2 ≤ g.inner x v v := by simpa [sq_abs] using hi
    have hj' : |g.inner x v (b j)| ^ 2 ≤ g.inner x v v := by simpa [sq_abs] using hj
    have hp : |g.inner x v (b i)| * |g.inner x v (b j)| ≤ g.inner x v v := by
      nlinarith [sq_nonneg (|g.inner x v (b i)| - |g.inner x v (b j)|)]
    have hr := hcomp i a j
    rw [abs_mul, abs_mul]
    calc
      |g.inner x v (b i)| * |g.inner x v (b j)| * |R i a j a| ≤
          (g.inner x v v) * N := by
            exact mul_le_mul hp hr (abs_nonneg _) (by positivity)
      _ = N * g.inner x v v := by ring
  rw [hcoord]
  let S : ℝ := ∑ a : I, ∑ i : I, ∑ j : I,
      (g.inner x v (b i)) * (g.inner x v (b j)) * R i a j a
  have hsum : |S| ≤
      (Fintype.card I : ℝ) ^ 3 * (N * g.inner x v v) := by
    calc
      |S| ≤ ∑ a : I, ∑ i : I, ∑ j : I,
          |(g.inner x v (b i)) * (g.inner x v (b j)) * R i a j a| := by
            calc
              |∑ a : I, ∑ i : I, ∑ j : I,
                  (g.inner x v (b i)) * (g.inner x v (b j)) * R i a j a| ≤
                  ∑ a : I, |∑ i : I, ∑ j : I,
                    (g.inner x v (b i)) * (g.inner x v (b j)) * R i a j a| :=
                Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ a : I, ∑ i : I, |∑ j : I,
                    (g.inner x v (b i)) * (g.inner x v (b j)) * R i a j a| := by
                exact Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ a : I, ∑ i : I, ∑ j : I,
                    |(g.inner x v (b i)) * (g.inner x v (b j)) * R i a j a| := by
                exact Finset.sum_le_sum fun a _ =>
                  Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : I, ∑ i : I, ∑ j : I, N * g.inner x v v := by
            exact Finset.sum_le_sum fun a _ =>
              Finset.sum_le_sum fun i _ =>
                Finset.sum_le_sum fun j _ => hterm a i j
      _ = (Fintype.card I : ℝ) ^ 3 * (N * g.inner x v v) := by
            simp [Finset.card_univ, pow_succ, mul_assoc, mul_left_comm, mul_comm]
  simpa [S, N, I, b, R, mul_assoc] using hsum

private lemma orthonormal_coeff_sq_le_metric_inner
    (x : M) (v : TangentSpace (𝓡 n) x) :
    ∀ i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      (g.inner x v (g.orthonormalBasis x i)) ^ 2 ≤ g.inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro i
  change (inner ℝ v (g.orthonormalBasis x i)) ^ 2 ≤ inner ℝ v v
  have hi := abs_real_inner_le_norm v (g.orthonormalBasis x i)
  have hbi : ‖g.orthonormalBasis x i‖ = 1 :=
    (g.orthonormalBasis x).norm_eq_one i
  rw [hbi, mul_one] at hi
  have hi2 : |inner ℝ v (g.orthonormalBasis x i)| ^ 2 ≤ ‖v‖ ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hi
  simpa [sq_abs, real_inner_self_eq_norm_sq] using hi2

private lemma metric_inner_nonneg (x : M) (v : TangentSpace (𝓡 n) x) :
    0 ≤ g.inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change 0 ≤ inner ℝ v v
  rw [real_inner_self_eq_norm_sq]
  positivity

theorem abs_ricci_quadratic_le_curvatureTensorNorm [T2Space M]
    (D : LeviCivitaData g) (x : M) (v : TangentSpace (𝓡 n) x) :
    |D.ricci x v v| ≤
      (Fintype.card (Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) : ℝ) ^ 3 *
        D.curvatureTensorNorm x * g.inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hv : v = ∑ i, (g.inner x v (b i)) • b i := by
    calc
      v = ∑ i, (inner ℝ (b i) v) • b i := (b.sum_repr' v).symm
      _ = ∑ i, (g.inner x v (b i)) • b i := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        change inner ℝ (b i) v = inner ℝ v (b i)
        exact real_inner_comm _ _
  apply abs_ricci_quadratic_le_of_expansion D x v ?_
    (orthonormal_coeff_sq_le_metric_inner x v) (metric_inner_nonneg x v)
  change (∑ a, D.curvatureTensor x v (b a) v (b a)) = _
  apply Finset.sum_congr rfl
  intro a _
  let B := D.curvatureTensor_bilinear_first_third x (b a) (b a)
  change B v v = ∑ i, ∑ j, (g.inner x v (b i)) * (g.inner x v (b j)) * B (b i) (b j)
  calc
    B v v = B (∑ i, (g.inner x v (b i)) • b i)
        (∑ j, (g.inner x v (b j)) • b j) := congrArg₂ (fun u w ↦ B u w) hv hv
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_assoc, mul_comm (g.inner x v (b j)) (g.inner x v (b i)), mul_assoc]

end PoincareConjecture.LeviCivitaData
