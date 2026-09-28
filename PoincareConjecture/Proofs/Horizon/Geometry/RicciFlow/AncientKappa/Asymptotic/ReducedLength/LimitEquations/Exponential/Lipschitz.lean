import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Smooth
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Lipschitz.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology NNReal
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
  (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)

include he hei

theorem exists_lipschitzOnWith_normalized_exp_neg
    {C : Set (Spacetime n)} (hC : IsCompact C) (hconv : Convex ℝ C)
    (hCD : C ⊆ domain J e) (hCpos : ∀ z ∈ C, 0 < z.2)
    {u : Spacetime n → ℝ} {L : ℝ≥0} (hu : LipschitzOnWith L u C) :
    ∃ Cu Cw : ℝ≥0,
      LipschitzOnWith Cu (fun z : Spacetime n =>
        z.2 ^ (-(n : ℝ) / 2) * Real.exp (-u z)) C ∧
      LipschitzOnWith Cw (fun z : Spacetime n => density F e z *
        (z.2 ^ (-(n : ℝ) / 2) * Real.exp (-u z))) C := by
  have hp : ContDiffOn ℝ ∞ (fun z : Spacetime n => z.2 ^ (-(n : ℝ) / 2)) C :=
    contDiffOn_snd.rpow_const_of_ne (fun z hz => (hCpos z hz).ne')
  obtain ⟨Cu, hCu⟩ := Poincare.Analysis.exists_lipschitzOnWith_mul_exp_neg hC hconv hp hu
  obtain ⟨Cw, hCw⟩ := Poincare.Analysis.exists_lipschitzOnWith_mul_exp_neg hC hconv
    (((contDiffOn_density F e he hei).mono hCD).mul hp) hu
  exact ⟨Cu, Cw, hCu, by simpa only [mul_assoc] using hCw⟩

end PoincareConjecture.RicciFlow.BackwardCoordinates
