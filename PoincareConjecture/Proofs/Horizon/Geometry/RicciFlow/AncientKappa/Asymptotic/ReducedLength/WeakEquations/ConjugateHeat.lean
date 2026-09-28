import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.WeakEquations.Exponential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u
namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

open LeviCivitaData.Dirichlet

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

theorem ae_reducedLength_hamiltonJacobi_coordinates
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) :
    let g := K.flow.metric (0 - τ)
    let l := fun x => reducedLength K.flow 0 p (e x) τ
    ∀ᵐ x, x ∈ e.source →
      2 * deriv (fun s => reducedLength K.flow 0 p (e x) s) τ +
        fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) -
        (K.flow.connection (0 - τ)).scalarCurvature (e x) + l x / τ = 0 := by
  obtain ⟨V⟩ := P.reduced_volume (τ + 1) (by linarith)
  obtain ⟨R⟩ := V.measure_regularity p
  filter_upwards [ae_regular_in_coordinates R hτ (by linarith) e he hei,
    P.reducedLengthGradientNormSq_coordinates_ae p hτ e he hei] with x hr hg hx
  obtain ⟨r⟩ := R.regular_points (e x, τ) (hr hx)
  have h := P.regular_reducedLength_hamiltonJacobi r
  rw [hg hx] at h
  exact h

theorem reducedLength_conjugateHeat_weak_coordinate_gradient
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) :
    let g := K.flow.metric (0 - τ)
    let l := fun x => reducedLength K.flow 0 p (e x) τ
    let B := fun x => g.pullbackVolumeDensity e x * Real.exp (-l x) *
      ((-deriv (fun s => reducedLength K.flow 0 p (e x) s) τ +
        (K.flow.connection (0 - τ)).scalarCurvature (e x) - (n : ℝ) / (2 * τ)) * φ x -
        fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)))
    IntegrableOn B O ∧ (∫ x in O, B x) ≤ 0 := by
  obtain ⟨hi, hw⟩ := P.reducedLength_exponential_weak_coordinate_inequality
    p hτ e he hei hO hOc hOs hφ hφc hφO hφ0
  have heq : (fun x => (K.flow.metric (0 - τ)).pullbackVolumeDensity e x *
      Real.exp (-reducedLength K.flow 0 p (e x) τ) *
      (φ x * (fderiv ℝ (fun y => reducedLength K.flow 0 p (e y) τ) x
        (((K.flow.metric (0 - τ)).pullbackCoefficients e x).inverse
          (fderiv ℝ (fun y => reducedLength K.flow 0 p (e y) τ) x)) +
        (K.flow.connection (0 - τ)).scalarCurvature (e x) +
          (reducedLength K.flow 0 p (e x) τ - (n : ℝ)) / τ) / 2 -
        fderiv ℝ φ x (((K.flow.metric (0 - τ)).pullbackCoefficients e x).inverse
          (fderiv ℝ (fun y => reducedLength K.flow 0 p (e y) τ) x)))) =ᵐ[volume.restrict O]
      (fun x => (K.flow.metric (0 - τ)).pullbackVolumeDensity e x *
        Real.exp (-reducedLength K.flow 0 p (e x) τ) *
        ((-deriv (fun s => reducedLength K.flow 0 p (e x) s) τ +
          (K.flow.connection (0 - τ)).scalarCurvature (e x) - (n : ℝ) / (2 * τ)) * φ x -
          fderiv ℝ φ x (((K.flow.metric (0 - τ)).pullbackCoefficients e x).inverse
            (fderiv ℝ (fun y => reducedLength K.flow 0 p (e y) τ) x)))) := by
    filter_upwards [ae_restrict_mem hO.measurableSet,
      ae_restrict_of_ae (P.ae_reducedLength_hamiltonJacobi_coordinates p hτ e he hei)]
      with x hx hh
    have h := hh (hOs (subset_closure hx))
    congr 2
    linear_combination (φ x / 2) * h
  exact ⟨hi.congr heq, (integral_congr_ae heq) ▸ hw⟩

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
