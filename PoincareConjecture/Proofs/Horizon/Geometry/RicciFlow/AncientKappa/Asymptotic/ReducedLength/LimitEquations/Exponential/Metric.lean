import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.Exponential.Bounds
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.WeakExponential


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.LeviCivitaData

open Dirichlet

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem reducedPotential_exponential_weak_inequality
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u (closure O)) (τ : ℝ)
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
      (φ x * (fderiv ℝ u x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)) +
        D.scalarCurvature (e x) + (u x - (n : ℝ)) / τ) / 2 -
        fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)))
    IntegrableOn B O ∧ (∫ x in O, B x) ≤ 0 := by
  let F := fun (i : Fin n) x => -(∑ j, divergenceCoefficients g e x i j *
    fderiv ℝ u x (EuclideanSpace.single j 1))
  let f := fun x => (fderiv ℝ u x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)) -
    D.scalarCurvature (e x) - (u x - (n : ℝ)) / τ) * g.pullbackVolumeDensity e x / 2
  obtain ⟨hF, hf⟩ := D.reducedPotential_flux_source_memLp e he hei hO hOc hOs hu τ
  have hflux (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
      (∑ i, F i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
        -g.pullbackVolumeDensity e x *
          fderiv ℝ ψ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)) := by
    dsimp only [F]
    simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
    rw [sum_divergenceCoefficients_eq_inverse_pairing]
  have hlinear : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ O → (∀ x, 0 ≤ ψ x) →
      (∫ x in O, ∑ i, F i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) ≤
        ∫ x in O, f x * ψ x := by
    intro ψ hψ hψc hψO hψ0
    have hψ2 : MemLp ψ 2 (volume.restrict O) :=
      (hψ.continuous.memLp_of_hasCompactSupport hψc).restrict O
    have hdψ (i : Fin n) : MemLp
        (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) 2 (volume.restrict O) := by
      have hc : Continuous (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) :=
        (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
      exact (hc.memLp_of_hasCompactSupport (hψc.fderiv_apply ℝ _)).restrict O
    have hleft : IntegrableOn
        (fun x => ∑ i, F i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) O :=
      integrable_finsetSum Finset.univ (fun i _ => (hF i).integrable_mul (hdψ i))
    have hright : IntegrableOn (fun x => f x * ψ x) O := hf.integrable_mul hψ2
    have heq : (fun x => (ψ x *
        (-fderiv ℝ u x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)) +
          D.scalarCurvature (e x) + (u x - (n : ℝ)) / τ) -
        2 * fderiv ℝ ψ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x))) *
        g.pullbackVolumeDensity e x) =
        (fun x => 2 * ((∑ i, F i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) -
          f x * ψ x)) := by
      funext x
      rw [hflux]
      dsimp only [f]
      ring
    have h := hweak ψ hψ hψc hψO hψ0
    rw [heq, integral_const_mul, integral_sub hleft hright] at h
    linarith
  obtain ⟨hi, hw⟩ := Poincare.Analysis.Elliptic.weakInequality_exponential_test
    hO hOc hu hF hf hlinear hφ hφc hφO hφ0
  have heq : (fun x => Real.exp (-u x) *
      ((∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) -
        φ x * ((∑ i, F i x * fderiv ℝ u x (EuclideanSpace.single i 1)) + f x))) =
      (fun x => g.pullbackVolumeDensity e x * Real.exp (-u x) *
        (φ x * (fderiv ℝ u x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)) +
          D.scalarCurvature (e x) + (u x - (n : ℝ)) / τ) / 2 -
          fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)))) := by
    funext x
    rw [hflux, hflux]
    dsimp only [f]
    ring
  rw [heq] at hi hw
  exact ⟨hi, hw⟩

end PoincareConjecture.LeviCivitaData
