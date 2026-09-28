import PoincareConjecture.Proofs.M08.ContinuationPath
import PoincareConjecture.Proofs.M08.ContinuationBackward
import PoincareConjecture.Proofs.M08.ContinuationUniqueness

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

theorem exists_backward_geodesic_extension {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₁ : 0 < τ₁) (hτ₂ : τ₂ ≤ τmax) (p : BackwardTimePath F T τ₁ τ₂)
    (hp : IsBackwardLGeodesic F T τ₁ τ₂ p) :
    ∃ q : BackwardTimePath F T 0 τ₂,
      (∀ τ ∈ Icc τ₁ τ₂, q.curve τ = p.curve τ) ∧ IsBackwardLGeodesic F T 0 τ₂ q ∧
      ∀ q' : BackwardTimePath F T 0 τ₂,
        (∀ τ ∈ Icc τ₁ τ₂, q'.curve τ = p.curve τ) →
        IsBackwardLGeodesic F T 0 τ₂ q' → ∀ τ ∈ Icc 0 τ₂, q'.curve τ = q.curve τ := by
  obtain ⟨R⟩ := nonempty_regularizedLGeodesicData hM04 hwindow hcurvature hτ₂ p hp
  obtain ⟨α, hαC, hα, hαR⟩ := exists_extended_square_continuation
    hM04 hwindow hcurvature hτ₁ hτ₂ p R
  obtain ⟨q, hqα, hq⟩ := exists_backward_geodesic_of_continuation F hM04 T τmax τ₂
    (hτ₁.trans p.ordered) hτ₂ hwindow α hαC hα
  have hqp : ∀ τ ∈ Icc τ₁ τ₂, q.curve τ = p.curve τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := hτ₁.le.trans hτ.1
    have hs : Real.sqrt τ ∈ sqrtParameterInterval τ₁ τ₂ :=
      ⟨Real.sqrt_le_sqrt hτ.1, Real.sqrt_le_sqrt hτ.2⟩
    exact (hqα ⟨hτ0, hτ.2⟩).trans ((hαR hs).trans (sqrtRegularPath_point_eq R.path hτ))
  refine ⟨q, hqp, hq, ?_⟩
  intro q' hq'p hq'
  exact backward_geodesic_eqOn_of_terminal_agreement hM04 hwindow hcurvature
    hτ₁ p.ordered hτ₂ q' q hq' hq (fun τ hτ ↦ (hq'p τ hτ).trans (hqp τ hτ).symm)

end PoincareConjecture.M08
