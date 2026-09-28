import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.Exponential.Derivatives
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.WeakFlux

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
  (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)

include he hei

theorem normalized_exp_neg_heatFlux_eq
    {u φ : Spacetime n → ℝ} {z : Spacetime n}
    (hu : DifferentiableAt ℝ u z) (hφ : DifferentiableAt ℝ φ z)
    (hz : z ∈ domain J e) (hτ : 0 < z.2) :
    let v := fun y : Spacetime n => y.2 ^ (-(n : ℝ) / 2) * Real.exp (-u y)
    Canonical.timeDeriv (fun y => density F e y * v y) z * φ z +
      (∑ i, Canonical.spatialDeriv i v z *
        ∑ j, weightedPrincipal F e i j z * Canonical.spatialDeriv j φ z) =
    z.2 ^ (-(n : ℝ) / 2) * (density F e z * Real.exp (-u z) *
      ((-deriv (fun τ => u (z.1, τ)) z.2 +
        (F.connection (-z.2)).scalarCurvature (e z.1) -
          (n : ℝ) / (2 * z.2)) * φ z -
        fderiv ℝ (fun x => φ (x, z.2)) z.1
          (((F.metric (-z.2)).pullbackCoefficients e z.1).inverse
            (fderiv ℝ (fun x => u (x, z.2)) z.1)))) := by
  dsimp only
  have ht : Canonical.timeDeriv u z = deriv (fun τ => u (z.1, τ)) z.2 := by
    exact (hu.hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv.symm
  have hs (i : Fin n) : Canonical.spatialDeriv i
      (fun y : Spacetime n => y.2 ^ (-(n : ℝ) / 2) * Real.exp (-u y)) z =
      -(z.2 ^ (-(n : ℝ) / 2) * Real.exp (-u z)) * Canonical.spatialDeriv i u z := by
    change fderiv ℝ _ z (EuclideanSpace.single i 1, 0) = _
    rw [fderiv_normalized_exp_neg_apply hu hτ]
    simp only [mul_zero, zero_sub, mul_neg, Canonical.spatialDeriv,
      Canonical.spatialDirection, neg_mul]
  have hpair : (∑ i, Canonical.spatialDeriv i u z *
      ∑ j, weightedPrincipal F e i j z * Canonical.spatialDeriv j φ z) =
      density F e z * fderiv ℝ (fun x => φ (x, z.2)) z.1
        (((F.metric (-z.2)).pullbackCoefficients e z.1).inverse
          (fderiv ℝ (fun x => u (x, z.2)) z.1)) := by
    calc
      _ = ∑ i, ∑ j, weightedPrincipal F e i j z *
          Canonical.spatialDeriv j u z * Canonical.spatialDeriv i φ z := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have hsymm := LeviCivitaData.Dirichlet.divergenceCoefficients_symm
          (g := F.metric (-z.2)) e he hei hz.1 j i
        change _ * (LeviCivitaData.Dirichlet.divergenceCoefficients
          (F.metric (-z.2)) e z.1 j i * _) = _
        rw [hsymm]
        dsimp only [weightedPrincipal]
        ring
      _ = _ := by
        have hsu (i) : fderiv ℝ (fun x => u (x, z.2)) z.1
            (EuclideanSpace.single i 1) = Canonical.spatialDeriv i u z :=
          partialDeriv_spatialSlice hu i
        have hsφ (i) : fderiv ℝ (fun x => φ (x, z.2)) z.1
            (EuclideanSpace.single i 1) = Canonical.spatialDeriv i φ z :=
          partialDeriv_spatialSlice hφ i
        simpa only [hsu, hsφ, weightedPrincipal, density] using
          (LeviCivitaData.Dirichlet.sum_divergenceCoefficients_eq_inverse_pairing
            (g := F.metric (-z.2)) e z.1
              (fderiv ℝ (fun x => u (x, z.2)) z.1)
              (fderiv ℝ (fun x => φ (x, z.2)) z.1))
  rw [timeDeriv_density_normalized_exp_neg F e he hei hu hz hτ, ht]
  simp only [hs, mul_assoc, ← Finset.mul_sum]
  rw [hpair]
  ring

end PoincareConjecture.RicciFlow.BackwardCoordinates
