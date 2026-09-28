import PoincareConjecture.Proofs.M10.BilinearCoefficientBound
import PoincareConjecture.Proofs.M10.BackwardMetricDerivative
import PoincareConjecture.Proofs.M10.ScalarBound










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem abs_ricci_basis_le (g : RiemannianMetric n M) (D : LeviCivitaData g) (q : M)
    (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q))) :
    |D.ricci q (g.orthonormalBasis q i) (g.orthonormalBasis q j)| ≤
      (n : ℝ) * D.curvatureTensorNorm q := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) q) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  calc
    _ ≤ ∑ k, |D.curvatureTensor q (g.orthonormalBasis q i) (g.orthonormalBasis q k)
        (g.orthonormalBasis q j) (g.orthonormalBasis q k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q)),
        D.curvatureTensorNorm q :=
      Finset.sum_le_sum (fun k _ ↦ abs_curvatureTensor_basis_le g D q i k j k)
    _ = (n : ℝ) * D.curvatureTensorNorm q := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim, nsmul_eq_mul]

variable {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

set_option backward.isDefEq.respectTransparency false in

theorem abs_twice_ricci_self_le
    (hwindow : Icc (T - τmax) T ⊆ J) {τ K : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (q : M) (hK : (F.connection (T - τ)).curvatureTensorNorm q ≤ K)
    (v : TangentSpace (𝓡 n) q) :
    |2 * (F.connection (T - τ)).ricci q v v| ≤
      (2 * (n : ℝ) ^ 3 * K) * (F.metric (T - τ)).inner q v v := by
  let g := F.metric (T - τ)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B : TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (𝓡 n) q →L[ℝ] ℝ :=
    fderiv ℝ (coordinateBackwardMetric F T q) (extChartAt (𝓡 n) q q, τ) (0, 1)
  have hB (u w : TangentSpace (𝓡 n) q) :
      B u w = 2 * (F.connection (T - τ)).ricci q u w :=
    coordinateBackwardMetric_time_derivative hwindow hτ hmax q u w
  have hcoeff (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q))) :
      |B (g.orthonormalBasis q i) (g.orthonormalBasis q j)| ≤ 2 * (n : ℝ) * K := by
    rw [hB, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hr := (abs_ricci_basis_le g (F.connection (T - τ)) q i j).trans
      (mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg n))
    nlinarith only [hr]
  have h := abs_bilinear_self_le_of_basis_bound (g.orthonormalBasis q) B hcoeff v
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) q) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  have hnorm : ‖v‖ ^ 2 = g.inner q v v := (real_inner_self_eq_norm_sq v).symm
  rw [hB, Fintype.card_fin, hdim, hnorm] at h
  convert h using 1
  ring

end PoincareConjecture.M10
