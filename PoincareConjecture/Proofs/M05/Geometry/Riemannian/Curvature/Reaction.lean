import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Curvature
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.Bilinear
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Contraction
import PoincareConjecture.Proofs.M05.Geometry.Curvature.Operator.Contraction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

private theorem bilinear_product_contraction_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ i, ∑ j, A (b i) (b j) * B (b i) (b j)) =
      ∑ i, ∑ j, A (c i) (c j) * B (c i) (c j) := by
  have hright (v : E) :
      (∑ j, A v (b j) * B v (b j)) = ∑ j, A v (c j) * B v (c j) := by
    exact bilinear_sum_orthonormalBasis_eq ((A v).smulRight (B v)) b c
  simp_rw [hright]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => A (c i) (c j) * B (c i) (c j))]
  apply Finset.sum_congr rfl
  intro j _
  exact bilinear_sum_orthonormalBasis_eq
    ((A.flip (c j)).smulRight (B.flip (c j))) b c

end PoincareConjecture

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvatureB_eq_sum_orthonormalBasis [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) x))
      (u v w z : TangentSpace (𝓡 n) x),
      D.curvatureB x u v w z =
        ∑ i, ∑ j, D.curvatureTensor x u (b i) v (b j) *
          D.curvatureTensor x w (b i) z (b j) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro ι _ b u v w z
  have hswap (a b c d : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x a b c d = D.curvatureTensor x b a d c := by
    rw [(hD.2.2.2.1 x a b c d).2.1, (hD.2.2.2.1 x c d a b).1,
      (hD.2.2.2.1 x c d b a).2.1, (hD.2.2.2.1 x b a c d).1, neg_neg]
  have h := bilinear_product_contraction_eq
    (D.curvatureTensor_bilinear_first_third x u v)
    (D.curvatureTensor_bilinear_first_third x w z) (g.orthonormalBasis x) b
  simpa only [curvatureB, curvatureTensor_bilinear_first_third_apply,
    hswap _ u _ v, hswap _ w _ z] using h

theorem movingInput_curvatureB_reaction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureReaction x u v w z +
      D.curvatureTensor x (PoincareConjecture.RicciFlow.ricciSharp D x u) v w z +
      D.curvatureTensor x u (PoincareConjecture.RicciFlow.ricciSharp D x v) w z +
      D.curvatureTensor x u v (PoincareConjecture.RicciFlow.ricciSharp D x w) z +
      D.curvatureTensor x u v w (PoincareConjecture.RicciFlow.ricciSharp D x z) =
        2 * (D.curvatureB x u v w z - D.curvatureB x u v z w -
          D.curvatureB x u z v w + D.curvatureB x u w v z) := by
  exact PoincareConjecture.RicciFlow.curvatureReaction_add_ricciSharp_eq D hD x u v w z

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.LeviCivitaData

open Poincare.Geometry.Curvature.Operator

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem curvatureB_cyclic_reaction [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x)) (i j : Fin 3),
      2 * (D.curvatureB x (b (pairFirst i)) (b (pairSecond i))
          (b (pairFirst j)) (b (pairSecond j)) -
        D.curvatureB x (b (pairFirst i)) (b (pairSecond i))
          (b (pairSecond j)) (b (pairFirst j)) -
        D.curvatureB x (b (pairFirst i)) (b (pairSecond j))
          (b (pairSecond i)) (b (pairFirst j)) +
        D.curvatureB x (b (pairFirst i)) (b (pairFirst j))
          (b (pairSecond i)) (b (pairSecond j))) =
        Poincare.Geometry.Curvature.Operator.curvatureReaction
          (curvatureMatrix (fun i j k l =>
            D.curvatureTensor x (b i) (b j) (b k) (b l))) i j := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro b i j
  rw [D.curvatureB_eq_sum_orthonormalBasis hD x b (b (pairFirst i))
      (b (pairSecond i)) (b (pairFirst j)) (b (pairSecond j)),
    D.curvatureB_eq_sum_orthonormalBasis hD x b (b (pairFirst i))
      (b (pairSecond i)) (b (pairSecond j)) (b (pairFirst j)),
    D.curvatureB_eq_sum_orthonormalBasis hD x b (b (pairFirst i))
      (b (pairSecond j)) (b (pairSecond i)) (b (pairFirst j)),
    D.curvatureB_eq_sum_orthonormalBasis hD x b (b (pairFirst i))
      (b (pairFirst j)) (b (pairSecond i)) (b (pairSecond j))]
  apply cyclic_curvature_contraction_eq
    (fun p q r s => D.curvatureTensor x (b p) (b q) (b r) (b s))
  · intro i j k l
    rw [(hD.2.2.2.1 x (b i) (b j) (b k) (b l)).2.1,
      (hD.2.2.2.1 x (b k) (b l) (b i) (b j)).1,
      (hD.2.2.2.1 x (b k) (b l) (b j) (b i)).2.1]
  · intro i j k l
    exact (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).1
  · intro i j k l
    exact (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).2.1

end PoincareConjecture.LeviCivitaData
