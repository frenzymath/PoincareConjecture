import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.CurvatureCarrier
import PoincareConjecture.Proofs.M04.SectionalRayleigh

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Poincare.Geometry.Curvature.Operator
open scoped Manifold ContDiff Bundle BigOperators Matrix

universe u

namespace PoincareConjecture.LeviCivitaData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem curvatureTensor_plane_ge_leastSectional_mul_gram
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (u v : TangentSpace (𝓡 3) x) :
    D.leastSectionalCurvature x * M04.metricGram g x u v ≤
      D.curvatureTensor x u v u v := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 3)), finrank_euclideanSpace]
    simp
  let b := (g.orthonormalBasis x).reindex (finCongr hdim)
  obtain ⟨A, hA⟩ := hD.1.1 x
  have heq (a b c d : TangentSpace (𝓡 3) x) :
      A ![a, b, c, d] = D.curvatureTensor x a b c d := (hA ![a, b, c, d]).symm
  have hfirst : ∀ a b c d, A ![a, b, c, d] = -A ![b, a, c, d] := by
    intro a b c d
    rw [heq, heq, (hD.2.2.2.1 x a b c d).2.1,
      (hD.2.2.2.1 x c d a b).1, (hD.2.2.2.1 x c d b a).2.1]
  have hlast : ∀ a b c d, A ![a, b, c, d] = -A ![a, b, d, c] := by
    intro a b c d
    simpa only [heq] using (hD.2.2.2.1 x a b c d).1
  let R := fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)
  let T := curvatureOperator R
  have hT : T.IsSymmetric := curvatureOperator_isSymmetric R
    (fun i j k l => (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).2.1)
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  let w : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (crossProduct (b.repr u) (b.repr v))
  have hrepr (a c : TangentSpace (𝓡 3) x) :
      dotProduct (b.repr a) (b.repr c) = g.inner x a c := by
    change dotProduct (b.repr a) (b.repr c) = inner ℝ a c
    rw [← b.repr.inner_map_map a c, EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial, dotProduct_comm]
  have hgram : ‖w‖ ^ 2 = M04.metricGram g x u v := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    change dotProduct (crossProduct (b.repr u) (b.repr v))
      (crossProduct (b.repr u) (b.repr v)) = _
    rw [cross_dot_cross, hrepr, hrepr, hrepr, hrepr, g.symm x v u]
    simp only [M04.metricGram, pow_two]
  have hplane : D.curvatureTensor x u v u v = inner ℝ w (T w) := by
    simpa only [heq] using multilinear_plane_eq_curvatureOperator_rayleigh A b hfirst hlast u v
  have hleast : D.leastSectionalCurvature x = hT.eigenvalues hn 2 :=
    D.leastSectionalCurvature_eq_operator_eigenvalue hD x b
  rw [hleast, ← hgram, hplane, Poincare.symmetric_rayleigh_eq_sum_eigenvalues hT hn]
  calc
    hT.eigenvalues hn 2 * ‖w‖ ^ 2 =
        ∑ i, hT.eigenvalues hn 2 * (inner ℝ (hT.eigenvectorBasis hn i) w) ^ 2 := by
      rw [← Finset.mul_sum, (hT.eigenvectorBasis hn).sum_sq_inner_right w]
    _ ≤ ∑ i, hT.eigenvalues hn i * (inner ℝ (hT.eigenvectorBasis hn i) w) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (hT.eigenvalues_antitone hn (by omega)) (sq_nonneg _)

theorem curvatureTensor_plane_ge_negativePart_mul_gram
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (u v : TangentSpace (𝓡 3) x) :
    -(D.negativeCurvaturePart x) * M04.metricGram g x u v ≤
      D.curvatureTensor x u v u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hgram : 0 ≤ M04.metricGram g x u v := by
    have h := real_inner_mul_inner_self_le u v
    change g.inner x u v * g.inner x u v ≤ g.inner x u u * g.inner x v v at h
    exact sub_nonneg.mpr (by simpa only [pow_two] using h)
  have hnegative : -(D.negativeCurvaturePart x) ≤ D.leastSectionalCurvature x := by
    unfold negativeCurvaturePart
    linarith [le_max_left (-D.leastSectionalCurvature x) 0]
  exact (mul_le_mul_of_nonneg_right hnegative hgram).trans
    (D.curvatureTensor_plane_ge_leastSectional_mul_gram hD x u v)

end PoincareConjecture.LeviCivitaData
