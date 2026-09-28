import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Tensors
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.ContractedBianchi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Derivative









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



noncomputable def hamiltonPPreAntisym (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) : ℝ :=
  let b := g.orthonormalBasis x
  2 * ∑ d, ∑ e,
      (D.covariantTensorDerivative D.riemannEvaluation x ![u, v, b d, w, b e] *
          D.ricci x (b d) (b e) +
        D.curvatureTensor x v (b d) w (b e) *
          D.covariantTensorDerivative D.ricciEvaluation x ![u, b d, b e] +
        D.curvatureTensor x u (b d) v (b e) *
          D.covariantTensorDerivative D.ricciEvaluation x ![b d, b e, w] +
        D.curvatureTensor x u (b d) w (b e) *
          D.covariantTensorDerivative D.ricciEvaluation x ![b d, v, b e])



lemma hamiltonPPreAntisym_sub_swap
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    hamiltonPPreAntisym D x u v w - hamiltonPPreAntisym D x v u w =
      2 * ∑ d, ∑ e,
        (D.curvatureTensor x u (g.orthonormalBasis x d) v (g.orthonormalBasis x e) *
            hamiltonP D x (g.orthonormalBasis x d) (g.orthonormalBasis x e) w +
          D.curvatureTensor x u (g.orthonormalBasis x d) w (g.orthonormalBasis x e) *
            hamiltonP D x (g.orthonormalBasis x d) v (g.orthonormalBasis x e) +
          D.curvatureTensor x v (g.orthonormalBasis x d) w (g.orthonormalBasis x e) *
            hamiltonP D x u (g.orthonormalBasis x d) (g.orthonormalBasis x e)) -
      2 * ∑ d, ∑ e,
        D.ricci x (g.orthonormalBasis x d) (g.orthonormalBasis x e) *
          D.covariantTensorDerivative D.riemannEvaluation x
            ![g.orthonormalBasis x d, u, v, w, g.orthonormalBasis x e] := by
  let b := g.orthonormalBasis x
  have hRm₁ (a c d e : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x a c d e = -D.curvatureTensor x a c e d :=
    (hD.2.2.2.1 x a c d e).1
  have hRm₂ (a c d e : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x a c d e = D.curvatureTensor x d e a c :=
    (hD.2.2.2.1 x a c d e).2.1
  have hK₁ (a c d e f : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative D.riemannEvaluation x ![a, c, d, e, f] =
        -D.covariantTensorDerivative D.riemannEvaluation x ![a, d, c, e, f] :=
    D.covariantTensorDerivative_riemannEvaluation_skew_first hD x a c d e f
  have hS (a c d : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative D.ricciEvaluation x ![a, c, d] =
        D.covariantTensorDerivative D.ricciEvaluation x ![a, d, c] :=
    D.covariantTensorDerivative_ricciEvaluation_symm hD x a c d
  have hB (a c d e f : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative D.riemannEvaluation x ![a, c, d, e, f] +
        D.covariantTensorDerivative D.riemannEvaluation x ![c, d, a, e, f] +
        D.covariantTensorDerivative D.riemannEvaluation x ![d, a, c, e, f] = 0 :=
    D.covariantTensorDerivative_curvature_second_bianchi hD x a c d e f
  have hpoint (d e : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      (D.covariantTensorDerivative D.riemannEvaluation x ![u, v, b d, w, b e] *
          D.ricci x (b d) (b e) +
        D.curvatureTensor x v (b d) w (b e) *
          D.covariantTensorDerivative D.ricciEvaluation x ![u, b d, b e] +
        D.curvatureTensor x u (b d) v (b e) *
          D.covariantTensorDerivative D.ricciEvaluation x ![b d, b e, w] +
        D.curvatureTensor x u (b d) w (b e) *
          D.covariantTensorDerivative D.ricciEvaluation x ![b d, v, b e]) -
      (D.covariantTensorDerivative D.riemannEvaluation x ![v, u, b d, w, b e] *
          D.ricci x (b d) (b e) +
        D.curvatureTensor x u (b d) w (b e) *
          D.covariantTensorDerivative D.ricciEvaluation x ![v, b d, b e] +
        D.curvatureTensor x v (b e) u (b d) *
          D.covariantTensorDerivative D.ricciEvaluation x ![b e, b d, w] +
        D.curvatureTensor x v (b d) w (b e) *
          D.covariantTensorDerivative D.ricciEvaluation x ![b d, u, b e]) =
        (D.curvatureTensor x u (b d) v (b e) *
          hamiltonP D x (b d) (b e) w +
          D.curvatureTensor x u (b d) w (b e) *
          hamiltonP D x (b d) v (b e) +
          D.curvatureTensor x v (b d) w (b e) *
          hamiltonP D x u (b d) (b e)) -
      D.ricci x (b d) (b e) *
        D.covariantTensorDerivative D.riemannEvaluation x ![b d, u, v, w, b e] := by
    have hK :
        D.covariantTensorDerivative D.riemannEvaluation x ![u, v, b d, w, b e] -
            D.covariantTensorDerivative D.riemannEvaluation x ![v, u, b d, w, b e] =
          -D.covariantTensorDerivative D.riemannEvaluation x ![b d, u, v, w, b e] := by
      have hb := hB u v (b d) w (b e)
      rw [hK₁ v (b d) u w (b e)] at hb
      linarith
    simp only [hamiltonP]
    rw [hS, hS, hRm₂, hRm₂, hRm₂, hRm₂,
      hRm₂ v (b e) u (b d)]
    linear_combination D.ricci x (b d) (b e) * hK
  dsimp only [hamiltonPPreAntisym, b]
  simp only [Finset.sum_add_distrib]
  rw [show (∑ x_1, ∑ x_2,
      D.curvatureTensor x v (b x_1) u (b x_2) *
        D.covariantTensorDerivative D.ricciEvaluation x ![b x_1, b x_2, w]) =
      ∑ x_1, ∑ x_2,
      D.curvatureTensor x v (b x_2) u (b x_1) *
        D.covariantTensorDerivative D.ricciEvaluation x ![b x_2, b x_1, w] by
    rw [Finset.sum_comm]]
  simp_rw [← Finset.sum_add_distrib]
  have hs : (∑ d, ∑ e,
      ((D.covariantTensorDerivative D.riemannEvaluation x ![u, v, b d, w, b e] *
          D.ricci x (b d) (b e) +
        D.curvatureTensor x v (b d) w (b e) *
          D.covariantTensorDerivative D.ricciEvaluation x ![u, b d, b e] +
        D.curvatureTensor x u (b d) v (b e) *
          D.covariantTensorDerivative D.ricciEvaluation x ![b d, b e, w] +
        D.curvatureTensor x u (b d) w (b e) *
          D.covariantTensorDerivative D.ricciEvaluation x ![b d, v, b e]) -
      (D.covariantTensorDerivative D.riemannEvaluation x ![v, u, b d, w, b e] *
          D.ricci x (b d) (b e) +
        D.curvatureTensor x u (b d) w (b e) *
          D.covariantTensorDerivative D.ricciEvaluation x ![v, b d, b e] +
        D.curvatureTensor x v (b e) u (b d) *
          D.covariantTensorDerivative D.ricciEvaluation x ![b e, b d, w] +
        D.curvatureTensor x v (b d) w (b e) *
          D.covariantTensorDerivative D.ricciEvaluation x ![b d, u, b e]))) =
      ∑ d, ∑ e, ((D.curvatureTensor x u (b d) v (b e) *
          hamiltonP D x (b d) (b e) w +
        D.curvatureTensor x u (b d) w (b e) *
          hamiltonP D x (b d) v (b e) +
        D.curvatureTensor x v (b d) w (b e) *
          hamiltonP D x u (b d) (b e)) -
      D.ricci x (b d) (b e) *
        D.covariantTensorDerivative D.riemannEvaluation x ![b d, u, v, w, b e]) := by
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    exact hpoint d e
  convert congrArg (fun z : ℝ => 2 * z) hs using 1 <;>
    simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, b] <;> ring_nf

end Poincare.RicciFlow.Harnack
