import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Norm









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter

namespace PoincareConjecture

private lemma sum_fin_tuple_succ {κ : Type*} [Fintype κ] {k : ℕ}
    (f : (Fin (k + 1) → κ) → ℝ) :
    (∑ a : Fin (k + 1) → κ, f a) =
      ∑ i : κ, ∑ a : Fin k → κ, f (Fin.cons i a) := by
  classical
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => κ))
      (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)).symm

section Curvature

open scoped Manifold ContDiff Bundle

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma curvatureTensorNorm_eq_sqrt_sum (D : LeviCivitaData g) (x : M) :
    D.curvatureTensorNorm x = Real.sqrt
      (∑ a : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (D.curvatureTensor x (g.orthonormalBasis x (a 0))
          (g.orthonormalBasis x (a 1)) (g.orthonormalBasis x (a 2))
          (g.orthonormalBasis x (a 3))) ^ 2) := by
  dsimp only [LeviCivitaData.curvatureTensorNorm]
  apply congrArg Real.sqrt
  simp_rw [sum_fin_tuple_succ]
  simp only [Fintype.sum_unique]
  rfl



theorem LeviCivitaData.curvatureTensorNorm_eq_tensorNormFromComponents
    (D : LeviCivitaData g) (x : M) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x))
    (A : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ)
    (hA : ∀ v, D.curvatureTensor x (v 0) (v 1) (v 2) (v 3) = A v) :
    D.curvatureTensorNorm x =
      tensorNormFromComponents (Matrix.of (fun i j => g.inner x (b i) (b j)))
        (fun i : Fin 4 → ι => D.curvatureTensor x (b (i 0)) (b (i 1))
          (b (i 2)) (b (i 3))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let c := g.orthonormalBasis x
  have h := multilinear_sum_mul_eq_inverse_gram A A b c
  have hs : (∑ a : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      A (fun r => c (a r)) * A (fun r => c (a r))) =
      ∑ i, ∑ j, ∑ k, ∑ l, (D.curvatureTensor x (c i) (c j) (c k) (c l)) ^ 2 := by
    simp_rw [← hA, sum_fin_tuple_succ]
    simp only [Fintype.sum_unique, pow_two]
    rfl
  rw [hs] at h
  dsimp only [LeviCivitaData.curvatureTensorNorm, tensorNormFromComponents]
  apply congrArg Real.sqrt
  change (∑ i, ∑ j, ∑ k, ∑ l, (D.curvatureTensor x (c i) (c j) (c k) (c l)) ^ 2) = _
  rw [h]
  simp_rw [← hA]
  rfl



theorem LeviCivitaData.curvatureTensorNorm_eq_tensorHilbertSchmidtNorm
    (D : LeviCivitaData g) (x : M)
    (A : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ)
    (hA : ∀ v, D.curvatureTensor x (v 0) (v 1) (v 2) (v 3) = A v) :
    letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) x
    D.curvatureTensorNorm x =
      tensorHilbertSchmidtNorm (g.toRiemannianMetric.toCore x) A := by
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := (g.orthonormalBasis x).toBasis
  rw [D.curvatureTensorNorm_eq_tensorNormFromComponents x b A hA,
    tensorHilbertSchmidtNorm_eq_tensorNormFromComponents _ _ b]
  simp_rw [← hA]
  rfl




theorem LeviCivitaData.tendsto_curvatureTensorNorm_of_components
    {α : Type*} {l : Filter α} {gseq : α → RiemannianMetric n M}
    (Dseq : ∀ a, LeviCivitaData (gseq a)) (D : LeviCivitaData g)
    (x : M) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x))
    (hAseq : ∀ a, ∃ A : MultilinearMap ℝ
        (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ,
      ∀ v, (Dseq a).curvatureTensor x (v 0) (v 1) (v 2) (v 3) = A v)
    (hA : ∃ A : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ,
      ∀ v, D.curvatureTensor x (v 0) (v 1) (v 2) (v 3) = A v)
    (hG : ∀ i j, Tendsto (fun a => (gseq a).inner x (b i) (b j)) l
      (𝓝 (g.inner x (b i) (b j))))
    (hR : ∀ i : Fin 4 → ι, Tendsto
      (fun a => (Dseq a).curvatureTensor x (b (i 0)) (b (i 1)) (b (i 2)) (b (i 3))) l
      (𝓝 (D.curvatureTensor x (b (i 0)) (b (i 1)) (b (i 2)) (b (i 3))))) :
    Tendsto (fun a => (Dseq a).curvatureTensorNorm x) l (𝓝 (D.curvatureTensorNorm x)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdet : (Matrix.of (fun i j => g.inner x (b i) (b j))).det ≠ 0 := by
    change (Matrix.gram ℝ b).det ≠ 0
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent
  have heq (a : α) := (Dseq a).curvatureTensorNorm_eq_tensorNormFromComponents x b
    (hAseq a).choose (hAseq a).choose_spec
  simp_rw [heq, D.curvatureTensorNorm_eq_tensorNormFromComponents x b hA.choose hA.choose_spec]
  exact tendsto_tensorNormFromComponents hG hR hdet



theorem LeviCivitaData.curvatureTensorNorm_eq_of_linearEquiv
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    {h : RiemannianMetric n N} (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) (y : N)
    (e : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) y)
    (hmetric : ∀ u v, h.inner y (e u) (e v) = g.inner x u v)
    (hcurv : ∀ u v w z, D'.curvatureTensor y (e u) (e v) (e w) (e z) =
      D.curvatureTensor x u v w z)
    (B : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) y) ℝ)
    (hB : ∀ v, D'.curvatureTensor y (v 0) (v 1) (v 2) (v 3) = B v) :
    D.curvatureTensorNorm x = D'.curvatureTensorNorm y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let c := g.orthonormalBasis x
  let c' := h.orthonormalBasis y
  let e' := e.isometryOfInner hmetric
  have hc := multilinear_sum_mul_orthonormalBasis_eq B B (c.map e') c'
  simp_rw [← hB, OrthonormalBasis.map_apply] at hc
  change (∑ a : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
    D'.curvatureTensor y (e (c (a 0))) (e (c (a 1))) (e (c (a 2))) (e (c (a 3))) *
      D'.curvatureTensor y (e (c (a 0))) (e (c (a 1))) (e (c (a 2))) (e (c (a 3)))) = _ at hc
  simp_rw [hcurv] at hc
  rw [curvatureTensorNorm_eq_sqrt_sum, curvatureTensorNorm_eq_sqrt_sum]
  simpa only [pow_two] using congrArg Real.sqrt hc

end Curvature

end PoincareConjecture
