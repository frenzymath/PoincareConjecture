import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Norm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators InnerProductSpace

namespace PoincareConjecture.RiemannianMetric.FactorCurvature

private theorem exists_basis_adjoin
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (L : V →ₗ[ℝ] W) (hL : ∀ u v, ⟪L u, L v⟫_ℝ = ⟪u, v⟫_ℝ)
    (N : W) (hN : ⟪N, N⟫_ℝ = 1) (hNT : ∀ u, ⟪N, L u⟫_ℝ = 0)
    (hdim : Module.finrank ℝ W = Fintype.card ι + 1) :
    ∃ B : OrthonormalBasis (Option ι) ℝ W,
      B none = N ∧ ∀ i, B (some i) = L (b i) := by
  classical
  let v : Option ι → W := fun i => i.elim N (fun j => L (b j))
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact hN
      | some j => exact hNT (b j)
    | some i =>
      cases j with
      | none => exact (real_inner_comm _ _).trans (hNT (b i))
      | some j => simpa only [v, Option.elim_some, hL, Option.some.injEq]
          using b.inner_eq_ite i j
  have hcard : Fintype.card (Option ι) = Module.finrank ℝ W := by
    simpa using hdim.symm
  let a := basisOfOrthonormalOfCardEqFinrank hv hcard
  have ha : Orthonormal ℝ a := by simpa [a] using hv
  refine ⟨a.toOrthonormalBasis ha, ?_, ?_⟩ <;> simp [a, v]

private theorem sum_fin_cons {ι : Type*} [Fintype ι] {k : ℕ}
    (f : (Fin (k + 1) → ι) → ℝ) :
    (∑ p, f p) = ∑ a, ∑ q, f (Fin.cons a q) := by
  calc
    (∑ p, f p) = ∑ p : ι × (Fin k → ι), f (Fin.cons p.1 p.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => ι)).symm _ _
        (fun p => congrArg f (Fin.cons_self_tail p).symm)
    _ = _ := Fintype.sum_prod_type _

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 (n + 1)) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric (n + 1) M} {h : RiemannianMetric n N}

private theorem norm_eq_sum_basis (D : LeviCivitaData g) (x : M)
    {ι : Type} [Fintype ι]
    (b : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace (𝓡 (n + 1)) x)) :
    D.curvatureTensorNorm x = Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
      (D.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA⟩ := D.curvatureTensor_multilinear x
  have expand {κ : Type} [Fintype κ] (c : κ → TangentSpace (𝓡 (n + 1)) x) :
      (∑ a : Fin 4 → κ, A (fun r => c (a r)) * A (fun r => c (a r))) =
        ∑ i, ∑ j, ∑ k, ∑ l, (D.curvatureTensor x (c i) (c j) (c k) (c l)) ^ 2 := by
    simp_rw [← hA, LeviCivitaData.riemannEvaluation, sum_fin_cons]
    simp only [Fintype.sum_unique, pow_two]
    rfl
  have he := multilinear_sum_mul_orthonormalBasis_eq A A (g.orthonormalBasis x) b
  rw [expand, expand] at he
  exact congrArg Real.sqrt he

theorem trace_identities
    (D : LeviCivitaData g) (Dh : LeviCivitaData h) (x : M) (y : N)
    (L : TangentSpace (𝓡 n) y →ₗ[ℝ] TangentSpace (𝓡 (n + 1)) x)
    (hL : ∀ u v, g.inner x (L u) (L v) = h.inner y u v)
    (ν : TangentSpace (𝓡 (n + 1)) x)
    (hν : g.inner x ν ν = 1) (hνT : ∀ u, g.inner x ν (L u) = 0)
    (hR : ∀ u v w z, Dh.curvatureTensor y u v w z =
      D.curvatureTensor x (L u) (L v) (L w) (L z))
    (hzero : ∀ u v w,
      D.curvatureTensor x ν u v w = 0 ∧ D.curvatureTensor x u ν v w = 0 ∧
      D.curvatureTensor x u v ν w = 0 ∧ D.curvatureTensor x u v w ν = 0) :
    (∀ u v, Dh.ricci y u v = D.ricci x (L u) (L v)) ∧
      Dh.scalarCurvature y = D.scalarCurvature x ∧
      Dh.curvatureTensorNorm y = D.curvatureTensorNorm x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let b := h.orthonormalBasis y
  obtain ⟨B, hB0, hBi⟩ := exists_basis_adjoin b L hL ν hν hνT (by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) =
      Fintype.card (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) + 1
    simp)
  have z₁ := fun u v w => (hzero u v w).1
  have z₂ := fun u v w => (hzero u v w).2.1
  have z₃ := fun u v w => (hzero u v w).2.2.1
  have z₄ := fun u v w => (hzero u v w).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    have ht := bilinear_sum_orthonormalBasis_eq
      (D.curvatureTensor_bilinear_first_third x (L u) (L v))
      (g.orthonormalBasis x) B
    simp only [LeviCivitaData.curvatureTensor_bilinear_first_third_apply] at ht
    have hs (a) : D.curvatureTensor x a (L u) a (L v) =
        D.curvatureTensor x (L u) a (L v) a := by
      rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last, neg_neg]
    simp_rw [hs] at ht
    simpa only [LeviCivitaData.ricci, hR, Fintype.sum_option, hB0, hBi,
      z₂, zero_add] using ht.symm
  · rw [D.scalarCurvature_eq_sum_orthonormalBasis x B]
    change (∑ i, ∑ j, Dh.curvatureTensor y (b i) (b j) (b i) (b j)) = _
    simp only [Fintype.sum_option, hB0, hBi, z₁, z₂, zero_add, Finset.sum_const_zero, hR]
  · rw [norm_eq_sum_basis D x B]
    change Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
      (Dh.curvatureTensor y (b i) (b j) (b k) (b l)) ^ 2) = _
    simp only [Fintype.sum_option, hB0, hBi, z₁, z₂, z₃, z₄, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, zero_add, hR]

theorem nonnegativeCurvatureOperator_of_restriction
    (D : LeviCivitaData g) (Dh : LeviCivitaData h) (x : M) (y : N)
    (L : TangentSpace (𝓡 n) y →ₗ[ℝ] TangentSpace (𝓡 (n + 1)) x)
    (hR : ∀ u v w z, Dh.curvatureTensor y u v w z =
      D.curvatureTensor x (L u) (L v) (L w) (L z))
    (hD : D.NonnegativeCurvatureOperator x) : Dh.NonnegativeCurvatureOperator y := by
  intro A hA
  have hp := D.curvatureOperator_nonneg_in_frame x hD
    (fun i => L (h.orthonormalBasis y i)) A hA
  simpa only [LeviCivitaData.curvatureOperatorQuadratic, hR] using hp

end PoincareConjecture.RiemannianMetric.FactorCurvature
