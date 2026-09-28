import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.QuadraticCancellation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Reaction.Contractions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma hamiltonM_geometric_prescribed_jet_cancellation
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (τ : ℝ) (x : M)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    let b := g.orthonormalBasis x
    let R := fun a c d e => D.curvatureTensor x (b a) (b c) (b d) (b e)
    let Ric := fun a c => D.ricci x (b a) (b c)
    let dP := fun e a c d => D.covariantTensorDerivative
      (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![b e, b a, b c, b d]
    let k := (2 * τ)⁻¹
    let V := fun e a c =>
      ((Ric e a + k * (if e = a then 1 else 0)) * W c -
        W a * (Ric e c + k * (if e = c then 1 else 0))) / 2
    2 * (∑ e, ∑ a, ∑ c, ∑ d, Ric e a * (dP e a c d + dP e a d c) * W c * W d) -
      4 * (∑ e, ∑ a, ∑ c, ∑ d, dP e a c d * V e a c * W d) +
      4 * k * (∑ a, ∑ c, hamiltonM D τ x (b a) (b c) * W a * W c) -
      2 * k ^ 2 * (∑ a, ∑ c, Ric a c * W a * W c) +
      2 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f, R a c d f * Ric e a * W c * Ric e d * W f) -
      2 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f, R a c d f * V e a c * V e d f) = 0 := by
  let b := g.orthonormalBasis x
  let R := fun a c d e => D.curvatureTensor x (b a) (b c) (b d) (b e)
  let Ric := fun a c => D.ricci x (b a) (b c)
  have hfirst (a c d e) : R a c d e = -R c a d e := by
    dsimp [R]
    rw [(hD.2.2.2.1 x (b a) (b c) (b d) (b e)).2.1,
      (hD.2.2.2.1 x (b d) (b e) (b a) (b c)).1,
      (hD.2.2.2.1 x (b d) (b e) (b c) (b a)).2.1]
  have hlast (a c d e) : R a c d e = -R a c e d :=
    (hD.2.2.2.1 x (b a) (b c) (b d) (b e)).1
  have hRic (c e) : (∑ a, R a c a e) = Ric c e := by
    change (∑ a, R a c a e) = ∑ a, R c a e a
    apply Finset.sum_congr rfl
    intro a _
    rw [hfirst a c a e, hlast c a a e, neg_neg]
  apply hamiltonM_prescribed_jet_cancellation R _ Ric
    (fun a c => hamiltonM D τ x (b a) (b c)) W ((2 * τ)⁻¹)
    hfirst hlast hRic
    (fun a c => (hD.2.2.2.1 x (b a) (b c) (b a) (b c)).2.2.2)
    (fun e a c d => covariantTensorDerivative_hamiltonP_skew D hD x
      (b e) (b a) (b c) (b d))
  intro c e
  have h := hamiltonM_eq_divergence_hamiltonP D hD τ x (b c) (b e)
  dsimp only at h
  dsimp only [R, Ric]
  rw [div_eq_mul_inv] at h
  linarith only [h]

lemma hamiltonP_geometric_prescribed_jet_cancellation
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (k : ℝ) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    let b := g.orthonormalBasis x
    let Ric := fun a c => D.ricci x (b a) (b c)
    let P := fun a c d => hamiltonP D x (b a) (b c) (b d)
    let dR := fun e a c d f => D.covariantTensorDerivative D.riemannEvaluation
      x ![b e, b a, b c, b d, b f]
    let V := fun e a c =>
      ((Ric e a + k * (if e = a then 1 else 0)) * W c -
        W a * (Ric e c + k * (if e = c then 1 else 0))) / 2;
    -(4 * (∑ a, ∑ c, ∑ d, ∑ e, ∑ f, Ric e f * dR e a c d f * U a c * W d)) +
      4 * k * (∑ a, ∑ c, ∑ d, P a c d * U a c * W d) -
      4 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f, dR e a c d f * V e a c * U d f) = 0 := by
  let b := g.orthonormalBasis x
  apply hamiltonP_prescribed_jet_cancellation
  · intro e a c d f
    exact D.covariantTensorDerivative_riemannEvaluation_skew_first hD x
      (b e) (b a) (b c) (b d) (b f)
  · intro e a c d f
    exact D.covariantTensorDerivative_riemannEvaluation_pair_swap hD x
      (b e) (b a) (b c) (b d) (b f)
  · intro e a c d f
    exact D.covariantTensorDerivative_riemannEvaluation_skew_last hD x
      (b e) (b a) (b c) (b d) (b f)
  · intro c d f
    exact sum_covariantTensorDerivative_riemann_eq_hamiltonP D hD x (b c) (b d) (b f)

end Poincare.RicciFlow.Harnack
