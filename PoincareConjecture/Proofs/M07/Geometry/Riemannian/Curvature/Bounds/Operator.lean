import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanNorm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture

private theorem abs_multilinear_apply_le_sqrt_sum_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]
    (A : MultilinearMap ℝ (fun _ : σ => E) ℝ)
    (b : OrthonormalBasis ι ℝ E) (v : σ → E) :
    |A v| ≤ Real.sqrt (∑ i : σ → ι, (A (fun r => b (i r))) ^ 2) *
      ∏ r, ‖v r‖ := by
  classical
  have hcoeff : (∑ i : σ → ι, (∏ r, b.toBasis.repr (v r) (i r)) ^ 2) =
      (∏ r, ‖v r‖) ^ 2 := by
    simp_rw [← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun r i => (b.toBasis.repr (v r) i) ^ 2)]
    apply Finset.prod_congr rfl
    intro r _
    simp only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    exact b.sum_sq_inner_right (v r)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : σ → ι => ∏ r, b.toBasis.repr (v r) (i r))
    (fun i : σ → ι => A (fun r => b (i r)))
  have hexp := multilinear_apply_basis_expansion A b.toBasis v
  simp only [OrthonormalBasis.coe_toBasis] at hexp
  rw [← hexp, hcoeff] at hcs
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  nlinarith only [hcs]

private lemma sum_fin_tuple_succ {κ : Type*} [Fintype κ] {k : ℕ}
    (f : (Fin (k + 1) → κ) → ℝ) :
    (∑ a : Fin (k + 1) → κ, f a) =
      ∑ i : κ, ∑ a : Fin k → κ, f (Fin.cons i a) := by
  classical
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => κ))
      (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)).symm

namespace LeviCivitaData

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem abs_curvatureTensor_le_of_multilinear
    (D : LeviCivitaData g) (x : M)
    (A : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ)
    (hA : ∀ v, D.curvatureTensor x (v 0) (v 1) (v 2) (v 3) = A v)
    (u v w z : TangentSpace (𝓡 n) x) :
    |D.curvatureTensor x u v w z| ≤ D.curvatureTensorNorm x *
      g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w *
        g.tangentNorm x z := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hnorm (q : TangentSpace (𝓡 n) x) : g.tangentNorm x q = ‖q‖ := by
    change Real.sqrt (inner ℝ q q) = ‖q‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg q)]
  have hN : D.curvatureTensorNorm x =
      Real.sqrt (∑ i : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (A (fun r => b (i r))) ^ 2) := by
    simp_rw [← hA]
    dsimp only [curvatureTensorNorm]
    apply congrArg Real.sqrt
    simp_rw [sum_fin_tuple_succ]
    simp only [Fintype.sum_unique]
    rfl
  have h := abs_multilinear_apply_le_sqrt_sum_sq A b ![u, v, w, z]
  rw [← hN] at h
  simpa [← hA, hnorm, Fin.prod_univ_succ, mul_assoc] using h

end Manifold

section Euclidean

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem abs_curvatureTensor_le_tangentNorm
    (D : LeviCivitaData g) (x u v w z : EuclideanSpace ℝ (Fin n)) :
    |D.curvatureTensor x u v w z| ≤ D.curvatureTensorNorm x *
      g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w *
        g.tangentNorm x z := by
  obtain ⟨A, hA⟩ := D.exists_multilinear_curvatureTensor x
  exact abs_curvatureTensor_le_of_multilinear D x A hA u v w z

theorem tangentNorm_curvature_le
    (D : LeviCivitaData g) (x u v w : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm x (D.curvature x u v w) ≤ D.curvatureTensorNorm x *
      g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let R : TangentSpace (𝓡 n) x := D.curvature x u v w
  have hnorm (q : TangentSpace (𝓡 n) x) : g.tangentNorm x q = ‖q‖ := by
    change Real.sqrt (inner ℝ q q) = ‖q‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg q)]
  have h := D.abs_curvatureTensor_le_tangentNorm x u v R w
  have hself : |D.curvatureTensor x u v R w| = ‖R‖ ^ 2 := by
    change |inner ℝ R R| = ‖R‖ ^ 2
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
  rw [hself, hnorm R] at h
  rw [hnorm]
  change ‖R‖ ≤ _
  by_cases hR : ‖R‖ = 0
  · rw [hR]
    unfold RiemannianMetric.tangentNorm curvatureTensorNorm
    positivity
  · have hpos : 0 < ‖R‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hR)
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith only [h]

theorem tangentNorm_curvature_conjugate_le
    (D : LeviCivitaData g) (p x : EuclideanSpace ℝ (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hP : ∀ a b, g.inner x (P a) (P b) = g.inner p a b)
    (u v : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm p (P.symm (D.curvature x (P u) v v)) ≤
      D.curvatureTensorNorm x * (g.tangentNorm x v) ^ 2 * g.tangentNorm p u := by
  have hnorm (a) : g.tangentNorm x (P a) = g.tangentNorm p a := by
    unfold RiemannianMetric.tangentNorm
    rw [hP]
  have hinv (a) : g.tangentNorm p (P.symm a) = g.tangentNorm x a := by
    rw [← hnorm, P.apply_symm_apply]
  rw [hinv]
  have h := D.tangentNorm_curvature_le x (P u) v v
  rw [hnorm] at h
  nlinarith only [h]

theorem tangentNorm_curvature_conjugate_le_of_bound
    (D : LeviCivitaData g) (p x : EuclideanSpace ℝ (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hP : ∀ a b, g.inner x (P a) (P b) = g.inner p a b)
    (u v : EuclideanSpace ℝ (Fin n)) (K c : ℝ)
    (hK : D.curvatureTensorNorm x ≤ K) (hv : g.tangentNorm x v = c) :
    g.tangentNorm p (P.symm (D.curvature x (P u) v v)) ≤
      (K * c ^ 2) * g.tangentNorm p u := by
  have h := D.tangentNorm_curvature_conjugate_le p x P hP u v
  rw [hv] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (sq_nonneg c)) (Real.sqrt_nonneg _))

end Euclidean

end LeviCivitaData

namespace RiemannianMetric

variable {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))

noncomputable def endomorphismInMetric (p : EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    letI : Bundle.RiemannianBundle
        (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
      ⟨g.toRiemannianMetric⟩
    TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p := by
  letI : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) p
  let L : TangentSpace (𝓡 n) p →ₗ[ℝ] TangentSpace (𝓡 n) p := A
  exact L.toContinuousLinearMap

@[simp] theorem endomorphismInMetric_apply (p : EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n)) : g.endomorphismInMetric p A u = A u := rfl

theorem norm_endomorphismInMetric_le (p : EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ u, g.tangentNorm p (A u) ≤ C * g.tangentNorm p u) :
    letI : Bundle.RiemannianBundle
        (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ‖g.endomorphismInMetric p A‖ ≤ C := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm (q : TangentSpace (𝓡 n) p) : g.tangentNorm p q = ‖q‖ := by
    change Real.sqrt (inner ℝ q q) = ‖q‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg q)]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  simpa only [endomorphismInMetric_apply, hnorm] using hA u

end RiemannianMetric

namespace LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem norm_endomorphismInMetric_curvature_le
    (D : LeviCivitaData g) (p x : EuclideanSpace ℝ (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hP : ∀ a b, g.inner x (P a) (P b) = g.inner p a b)
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n))
    (hA : ∀ u, A u = P.symm (D.curvature x (P u) v v)) (K c : ℝ)
    (hK : D.curvatureTensorNorm x ≤ K) (hv : g.tangentNorm x v = c) :
    letI : Bundle.RiemannianBundle
        (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ‖g.endomorphismInMetric p A‖ ≤ K * c ^ 2 := by
  apply g.norm_endomorphismInMetric_le p A (K * c ^ 2)
  · have hnonneg : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
    exact mul_nonneg (hnonneg.trans hK) (sq_nonneg c)
  · intro u
    rw [hA]
    exact D.tangentNorm_curvature_conjugate_le_of_bound p x P hP u v K c hK hv

end LeviCivitaData

end PoincareConjecture
