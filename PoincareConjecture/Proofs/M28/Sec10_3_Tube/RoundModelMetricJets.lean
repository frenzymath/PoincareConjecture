import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundModelJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FiniteOrder.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FiniteOrder.Frame












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M28.tube

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

open PoincareConjecture.CoordinateExponential
open Poincare.Riemannian.RadialTransport






theorem exists_round_model_pullback_metric_jet_bound
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    (m : ℕ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (e : EuclideanSpace ℝ (Fin 3) → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (h0 : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ,
        ‖iteratedFDeriv ℝ m
          (N.model_metric.pullbackCoefficients e) x‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ :=
    CoordinateExponential.exists_uniform_pullback_metric_jet_bound
      3 m hρ hρR (fun _ : ℕ => (9 : ℝ))
        (fun _ => by norm_num)
  refine ⟨B, hB, ?_⟩
  intro x hx
  refine hbound N.model_metric N.model_connection e he hi h0 hgauss ?_ x hx
  intro l hl y hy
  exact singularRound_curvatureDerivativeNorm_le_nine N l (e y)





theorem exists_round_model_pullback_metric_two_jet_bound
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (e : EuclideanSpace ℝ (Fin 3) → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (h0 : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ,
        ‖iteratedFDeriv ℝ 2
          (N.model_metric.pullbackCoefficients e) x‖ ≤ B := by
  simpa using exists_round_model_pullback_metric_jet_bound N 2 hρ hρR e he hi h0 hgauss







theorem exists_C9_radial_connection_jet_bound
    (r : ℝ) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
        (D : LeviCivitaData g)
        (b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))),
        (∀ v w : EuclideanSpace ℝ (Fin 3),
          g.inner 0 v w = inner ℝ v w) →
        (∀ x : EuclideanSpace ℝ (Fin 3), ∀ t : ℝ,
          christoffelBilinear g.euclideanCoefficients (t • x) x x = 0) →
        ∀ T : EuclideanSpace ℝ (Fin 3) →
          EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3),
          ContDiff ℝ ∞ T → (∀ x, (T x).IsInvertible) →
          (∀ x v, T x v =
            field (christoffelBilinear g.euclideanCoefficients) v x) →
          (∀ l ≤ m, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) r,
            D.curvatureDerivativeNorm l x ≤ 9) →
          ∀ q ≤ m, ∀ j a u,
            ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) r,
              ‖iteratedFDeriv ℝ q (fun y => radialConnectionCoeff b
                (christoffelBilinear g.euclideanCoefficients) T j a y u) x‖ ≤
                B * ‖u‖ := by
  obtain ⟨A, B, K, hA, hB, hK, hbound⟩ :=
    CoordinateExponential.exists_uniform_radial_frame_jet_bounds_through
      3 r (fun _ : ℕ => (9 : ℝ)) (fun _ => by norm_num) m m le_rfl
  refine ⟨B, hB, ?_⟩
  intro g D b h0 hgeo T hT hTi hTv hcurv q hq j a u x hx
  exact (hbound g D b h0 hgeo T hT hTi hTv hcurv).2.2 q hq j a u x hx

end PoincareConjecture.M28.tube
