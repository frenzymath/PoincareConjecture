import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.Exponential.Metric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem reducedPotential_heat_weak_inequality
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source)
    {u v : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u (closure O)) (τ : ℝ)
    (hHJ : ∀ᵐ x ∂volume.restrict O,
      2 * v x + fderiv ℝ u x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)) -
        D.scalarCurvature (e x) + u x / τ = 0)
    (hweak : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ O → (∀ x, 0 ≤ ψ x) →
      (∫ x in O, (ψ x *
        (-fderiv ℝ u x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)) +
          D.scalarCurvature (e x) + (u x - (n : ℝ)) / τ) -
        2 * fderiv ℝ ψ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x))) *
        g.pullbackVolumeDensity e x) ≤ 0)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) :
    let B := fun x => g.pullbackVolumeDensity e x * Real.exp (-u x) *
      ((-v x + D.scalarCurvature (e x) - (n : ℝ) / (2 * τ)) * φ x -
        fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)))
    IntegrableOn B O ∧ (∫ x in O, B x) ≤ 0 := by
  obtain ⟨hi, hw⟩ := D.reducedPotential_exponential_weak_inequality
    e he hei hO hOc hOs hu τ hweak hφ hφc hφO hφ0
  have heq : (fun x => g.pullbackVolumeDensity e x * Real.exp (-u x) *
      (φ x * (fderiv ℝ u x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)) +
        D.scalarCurvature (e x) + (u x - (n : ℝ)) / τ) / 2 -
        fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x))))
      =ᵐ[volume.restrict O]
      (fun x => g.pullbackVolumeDensity e x * Real.exp (-u x) *
        ((-v x + D.scalarCurvature (e x) - (n : ℝ) / (2 * τ)) * φ x -
          fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)))) := by
    filter_upwards [hHJ] with x hx
    congr 2
    linear_combination (φ x / 2) * hx
  exact ⟨hi.congr heq, (integral_congr_ae heq) ▸ hw⟩

end PoincareConjecture.LeviCivitaData
