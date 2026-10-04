/-
Adapted from AxelWorkspace revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source and SHA-256: references/analysis/axel-workspace/weak-parabolic-regularity-sources.json.
Apache-2.0; see the license in that source directory.
-/
import PoincareLib.Analysis.Parabolic.WeakRegularity.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The local parabolic equation with its canonical adjoint

Time here is the increasing parabolic time, hence backward Ricci-flow time
when applying this equation to a conjugate-heat density. Both the test operator
and the Lebesgue pairing are defined from the coefficients. The legacy
`WeakParabolicSolution` is deliberately not used.

Reference: Morgan--Tian, Proposition 9.20, proof on p. 208.
-/

open MeasureTheory Set
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

def spatialDirection (i : Fin n) : Spacetime n :=
  (EuclideanSpace.single i 1, 0)

def spatialDeriv (i : Fin n) (u : Spacetime n → ℝ) (z : Spacetime n) : ℝ :=
  fderiv ℝ u z (spatialDirection i)

def timeDeriv (u : Spacetime n → ℝ) (z : Spacetime n) : ℝ :=
  fderiv ℝ u z (0, 1)

/-- Coefficients of `P = ∂t - aⁱʲ∂i∂j + bⁱ∂i + c`. -/
structure Coefficients (n : ℕ) where
  principal : Fin n → Fin n → Spacetime n → ℝ
  drift : Fin n → Spacetime n → ℝ
  zeroth : Spacetime n → ℝ

def Coefficients.IsSmoothOn (C : Coefficients n) (U : Set (Spacetime n)) : Prop :=
  (∀ i j, ContDiffOn ℝ ∞ (C.principal i j) U) ∧
  (∀ i, ContDiffOn ℝ ∞ (C.drift i) U) ∧ ContDiffOn ℝ ∞ C.zeroth U

def Coefficients.IsUniformlyEllipticOn (C : Coefficients n)
    (U : Set (Spacetime n)) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ z ∈ U, ∀ ξ : Euclid n,
    κ * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, C.principal i j z * ξ i * ξ j

def Coefficients.operator (C : Coefficients n) (u : Spacetime n → ℝ)
    (z : Spacetime n) : ℝ :=
  timeDeriv u z - (∑ i, ∑ j, C.principal i j z * spatialDeriv i (spatialDeriv j u) z) +
    (∑ i, C.drift i z * spatialDeriv i u z) + C.zeroth z * u z

def Coefficients.adjoint (C : Coefficients n) (φ : Spacetime n → ℝ)
    (z : Spacetime n) : ℝ :=
  -timeDeriv φ z - (∑ i, ∑ j,
    spatialDeriv j (spatialDeriv i (fun y => C.principal i j y * φ y)) z) -
    (∑ i, spatialDeriv i (fun y => C.drift i y * φ y) z) + C.zeroth z * φ z

/-- The distributional equation uses smooth tests compactly supported in the
open region and an actual Lebesgue integral. -/
def WeakSolutionOn (C : Coefficients n) (u : Spacetime n → ℝ)
    (U : Set (Spacetime n)) : Prop :=
  LocallyIntegrableOn u U volume ∧
    ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, u z * C.adjoint φ z) = 0

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
