import PoincareConjecture.Proofs.M01.NormalizationPinching
import PoincareConjecture.Proofs.M01.CurvatureCalculusTensorial
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

theorem m01_multilinear_sq_le {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b : OrthonormalBasis ι ℝ V) (A : MultilinearMap ℝ (fun _ : κ => V) ℝ)
    (v : κ → V) :
    (A v) ^ 2 ≤ (∑ p : κ → ι, (A (fun j => b (p j))) ^ 2) * ∏ j, ‖v j‖ ^ 2 := by
  classical
  have hexpand : A v = ∑ p : κ → ι,
      (∏ j, b.repr (v j) (p j)) * A (fun j => b (p j)) := by
    conv_lhs => rw [show v = (fun j => ∑ i, b.repr (v j) i • b i) by
      funext j
      exact (b.sum_repr (v j)).symm]
    rw [A.map_sum]
    simp only [A.map_smul_univ, smul_eq_mul]
  have hparseval (j : κ) : (∑ i, (b.repr (v j) i) ^ 2) = ‖v j‖ ^ 2 := by
    simpa only [b.repr_apply_apply, Real.norm_eq_abs, sq_abs] using
      b.sum_sq_norm_inner_right (v j)
  have hcoeff : (∑ p : κ → ι, (∏ j, b.repr (v j) (p j)) ^ 2) = ∏ j, ‖v j‖ ^ 2 := by
    simp_rw [← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun j i => (b.repr (v j) i) ^ 2)]
    simp_rw [hparseval]
  rw [hexpand]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : κ → ι => ∏ j, b.repr (v j) (p j))
    (fun p : κ → ι => A (fun j => b (p j)))
  rw [hcoeff, mul_comm] at h
  exact h

theorem m01_sum_fin_succ {ι : Type*} [Fintype ι] {n : ℕ}
    (f : (Fin (n + 1) → ι) → ℝ) :
    (∑ p, f p) = ∑ a, ∑ q, f (Fin.cons a q) := by
  calc
    (∑ p, f p) = ∑ p : ι × (Fin n → ι), f (Fin.cons p.1 p.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => ι)).symm _ _
        (fun p => congrArg f (Fin.cons_self_tail p).symm)
    _ = _ := Fintype.sum_prod_type _

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

open LeviCivitaData

theorem m01_curvatureTensor_orthonormalPair_sq_le (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 3) x) (huv : IsOrthonormalPair g x u v) :
    (D.curvatureTensor x u v u v) ^ 2 ≤ (D.curvatureTensorNorm x) ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA⟩ := D.curvatureTensor_multilinear x
  let b := g.orthonormalBasis x
  have hu : ‖u‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact huv.1
  have hv : ‖v‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact huv.2.1
  have h := m01_multilinear_sq_le b A ![u, v, u, v]
  simp only [← hA, riemannEvaluation] at h
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, hu, hv, mul_one] at h
  have hsum : (∑ p : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
      (D.curvatureTensor x (b (p 0)) (b (p 1)) (b (p 2)) (b (p 3))) ^ 2) =
      (D.curvatureTensorNorm x) ^ 2 := by
    unfold curvatureTensorNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)))))]
    simp only [m01_sum_fin_succ, Fin.cons_zero, Fintype.sum_unique]
    rfl
  rw [hsum] at h
  exact h

theorem m01HamiltonIveyPinchedAt_zero_of_norm_le (D : LeviCivitaData g)
    (hRm : ∀ x : M, D.curvatureTensorNorm x ≤ 1) : HamiltonIveyPinchedAt D 0 := by
  apply m01HamiltonIveyPinchedAt_zero
  intro x u v huv
  have h := m01_curvatureTensor_orthonormalPair_sq_le D x u v huv
  have hn : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
  nlinarith [hRm x]

end PoincareConjecture
