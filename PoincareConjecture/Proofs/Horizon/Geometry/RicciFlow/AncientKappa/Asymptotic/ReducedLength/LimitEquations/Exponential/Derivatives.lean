import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Volume
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

variable {n : ℕ}

theorem fderiv_normalized_exp_neg_apply
    {u : Spacetime n → ℝ} {z : Spacetime n}
    (hu : DifferentiableAt ℝ u z) (hz : 0 < z.2) (v : Spacetime n) :
    fderiv ℝ (fun y : Spacetime n => y.2 ^ (-(n : ℝ) / 2) * Real.exp (-u y)) z v =
      z.2 ^ (-(n : ℝ) / 2) * Real.exp (-u z) *
        (-(n : ℝ) / (2 * z.2) * v.2 - fderiv ℝ u z v) := by
  have hp := (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).rpow_const
    (p := -(n : ℝ) / 2) (Or.inl hz.ne')
  have hd := (hp.fun_mul hu.hasFDerivAt.neg.exp).fderiv
  simp only [Pi.neg_apply] at hd
  rw [hd]
  simp only [add_apply, smul_apply, neg_apply, smul_eq_mul, ContinuousLinearMap.coe_snd']
  rw [Real.rpow_sub hz, Real.rpow_one]
  field_simp
  ring

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
  (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)

include he hei

theorem timeDeriv_density_normalized_exp_neg
    {u : Spacetime n → ℝ} {z : Spacetime n}
    (hu : DifferentiableAt ℝ u z) (hz : z ∈ domain J e) (hτ : 0 < z.2) :
    Canonical.timeDeriv (fun y : Spacetime n => density F e y *
      (y.2 ^ (-(n : ℝ) / 2) * Real.exp (-u y))) z =
    density F e z * (z.2 ^ (-(n : ℝ) / 2) * Real.exp (-u z)) *
      (-Canonical.timeDeriv u z + (F.connection (-z.2)).scalarCurvature (e z.1) -
        (n : ℝ) / (2 * z.2)) := by
  have hρ := ((contDiffOn_density F e he hei).contDiffAt
    ((isOpen_domain e).mem_nhds hz)).differentiableAt (by simp)
  have hv : DifferentiableAt ℝ (fun y : Spacetime n =>
      y.2 ^ (-(n : ℝ) / 2) * Real.exp (-u y)) z :=
    ((differentiableAt_snd (𝕜 := ℝ) (p := z)).rpow_const
      (p := -(n : ℝ) / 2) (Or.inl hτ.ne')).fun_mul hu.neg.exp
  change fderiv ℝ _ z (0, 1) = _
  rw [fderiv_fun_mul hρ hv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_normalized_exp_neg_apply hu hτ,
    show fderiv ℝ (density F e) z (0, 1) =
      (F.connection (-z.2)).scalarCurvature (e z.1) * density F e z from
        timeDeriv_density F e he hei hz]
  simp only [Canonical.timeDeriv, mul_one]
  ring

end PoincareConjecture.RicciFlow.BackwardCoordinates
