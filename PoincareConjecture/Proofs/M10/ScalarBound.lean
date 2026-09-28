import PoincareConjecture.Definitions.Ch06.LGeometry

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 800000 in

theorem abs_curvatureTensor_basis_le (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (q : M)
    (i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q))) :
    |D.curvatureTensor q (g.orthonormalBasis q i) (g.orthonormalBasis q j)
      (g.orthonormalBasis q k) (g.orthonormalBasis q l)| ≤ D.curvatureTensorNorm q := by
  let N := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q))
  let a : N → N → N → N → ℝ := fun i j k l ↦
    D.curvatureTensor q (g.orthonormalBasis q i)
    (g.orthonormalBasis q j) (g.orthonormalBasis q k) (g.orthonormalBasis q l)
  change |a i j k l| ≤ Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, a i j k l ^ 2)
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  calc
    a i j k l ^ 2 ≤ ∑ l, a i j k l ^ 2 :=
      Finset.single_le_sum (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ l)
    _ ≤ ∑ k, ∑ l, a i j k l ^ 2 :=
      Finset.single_le_sum (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
        (Finset.mem_univ k)
    _ ≤ ∑ j, ∑ k, ∑ l, a i j k l ^ 2 :=
      Finset.single_le_sum (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦
        Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, ∑ k, ∑ l, a i j k l ^ 2 :=
      Finset.single_le_sum (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦
        Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))))
        (Finset.mem_univ i)

theorem abs_scalarCurvature_le (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (q : M) :
    |D.scalarCurvature q| ≤ (n : ℝ) ^ 2 * D.curvatureTensorNorm q := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) q) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  calc
    |D.scalarCurvature q| ≤ ∑ i, |D.ricci q (g.orthonormalBasis q i)
        (g.orthonormalBasis q i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |D.curvatureTensor q (g.orthonormalBasis q i)
        (g.orthonormalBasis q j) (g.orthonormalBasis q i)
        (g.orthonormalBasis q j)| :=
      Finset.sum_le_sum (fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q)), D.curvatureTensorNorm q :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦
        abs_curvatureTensor_basis_le g D q i j i j))
    _ = (n : ℝ) ^ 2 * D.curvatureTensorNorm q := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim, nsmul_eq_mul]
      ring

theorem exists_uniform_scalarCurvature_bound {J I : Set ℝ} (F : RicciFlow n M J)
    [T3Space M] (hcurvature : CompleteBoundedCurvatureOn F I) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∀ q : M, |(F.connection t).scalarCurvature q| ≤ C := by
  obtain ⟨K, hK, hbound⟩ := hcurvature.2
  refine ⟨(n : ℝ) ^ 2 * K, mul_nonneg (sq_nonneg _) hK, ?_⟩
  intro t ht q
  exact (abs_scalarCurvature_le (F.metric t) (F.connection t) q).trans
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hbound t ht q)) (sq_nonneg _))

end PoincareConjecture.M10
