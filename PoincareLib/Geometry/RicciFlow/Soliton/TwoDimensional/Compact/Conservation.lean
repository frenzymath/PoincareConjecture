import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Differential
import PoincareLib.Geometry.Manifold.ContDiff.Constancy

/-!
# Conserved scalar quantities of surface gradient solitons

The differential identities integrate to constants on a preconnected surface.
The scale is arbitrary; positivity and completeness enter only when these
identities are used in the classification argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle
open Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric 2 M}

/-- Scalar curvature times the inverse potential weight is constant. -/
theorem exists_scalar_conservation_of_surface_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w) :
    ∃ A : ℝ, ∀ x, D.scalarCurvature x * Real.exp (-f x) = A := by
  have hfs := D.contMDiff_of_C2_surface_soliton hf hsol
  have hcont : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun x => D.scalarCurvature x * Real.exp (-f x)) :=
    D.contMDiff_scalarCurvature.mul (Real.contDiff_exp.contMDiff.comp hfs.neg)
  exact Poincare.Manifold.exists_eq_const_of_mvfderiv_eq_zero
    (fun x => (hcont x).mdifferentiableAt (by simp))
    (D.mvfderiv_weighted_scalar_of_surface_soliton hf hsol)

/-- Hamilton's scalar identity holds globally at any constant soliton scale. -/
theorem exists_hamilton_conservation_of_surface_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w) :
    ∃ C : ℝ, ∀ x, D.scalarCurvature x +
      g.inner x (D.gradient f x) (D.gradient f x) - 2 * lambda * f x = C := by
  have hfs := D.contMDiff_of_C2_surface_soliton hf hsol
  have hnorm : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (D.gradient f x) (D.gradient f x)) := by
    intro x
    have hgrad := D.contMDiffAt_gradient (hfs x)
    simpa using (contMDiffAt_totalSpace.mp
      (((g.contMDiff x).clm_bundle_apply hgrad).clm_bundle_apply hgrad)).2
  have hcont : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun x => D.scalarCurvature x +
        g.inner x (D.gradient f x) (D.gradient f x) - 2 * lambda * f x) :=
    (D.contMDiff_scalarCurvature.add hnorm).sub (contMDiff_const.mul hfs)
  exact Poincare.Manifold.exists_eq_const_of_mvfderiv_eq_zero
    (fun x => (hcont x).mdifferentiableAt (by simp))
    (D.mvfderiv_hamilton_of_surface_soliton hf hsol)

/-- The two conservation constants needed for complete surface compactness. -/
theorem exists_conservation_constants_of_surface_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w) :
    ∃ A C : ℝ, (∀ x, D.scalarCurvature x * Real.exp (-f x) = A) ∧
      (∀ x, D.scalarCurvature x +
        g.inner x (D.gradient f x) (D.gradient f x) - 2 * lambda * f x = C) := by
  obtain ⟨A, hA⟩ := D.exists_scalar_conservation_of_surface_soliton hf hsol
  obtain ⟨C, hC⟩ := D.exists_hamilton_conservation_of_surface_soliton hf hsol
  exact ⟨A, C, hA, hC⟩

end PoincareMT.LeviCivitaData
