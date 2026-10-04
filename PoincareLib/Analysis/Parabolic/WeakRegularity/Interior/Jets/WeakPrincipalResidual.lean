/-
Adapted from AxelWorkspace revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source and SHA-256: references/analysis/axel-workspace/weak-parabolic-regularity-sources.json.
Apache-2.0; see the license in that source directory.
-/
import PoincareLib.Analysis.Parabolic.WeakRegularity.Interior.ConstantEnergy
import PoincareLib.Analysis.Parabolic.WeakRegularity.Interior.Jets.WeakMollifiedEquation

/-!
# The actual mollified principal residual

The weak spatial derivative identities cancel the pointwise lower-order
terms in the mollified equation, leaving convolution forcing and flux commutators.

References: Morgan--Tian, Proposition 9.20, pp. 207-208;
Evans, second edition, Section 5.2.1, pp. 256-257.
-/

open Set MeasureTheory
open scoped ContDiff

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

open Poincare.Analysis.Parabolic.WeakRegularity.Interior

/-- The principal residual of an actual mollified forced weak solution. -/
theorem mollified_principal_residual_of_forcing
    {n : ℕ} {U V : Set (Spacetime n)} (hU : IsOpen U) (hV : IsOpen V)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    {u f : Spacetime n → ℝ} (hu : LocallyIntegrableOn u U volume)
    (hf : LocallyIntegrableOn f U volume)
    (hforce : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ y, u y * C.adjoint φ y) = ∫ y, φ y * f y)
    {g : Fin n → Spacetime n → ℝ}
    (hg : ∀ i, LocallyIntegrableOn (g i) U volume)
    (hweak : ∀ i (ψ : Spacetime n → ℝ), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * g i y) = -(∫ y in U, spatialDeriv i ψ y * u y))
    {η : Spacetime n → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : ∀ x ∈ V, tsupport (translatedKernel η x) ⊆ U)
    {z : Spacetime n} (hz : z ∈ V) :
    timeDeriv (lebesgueConvolution η u) z -
      (∑ i : Fin n, ∑ j : Fin n, C.principal i j z *
        spatialSecond i j (lebesgueConvolution η u) z) =
      -(∑ i : Fin n, ∑ j : Fin n,
        (C.principal i j z * lebesgueConvolution (spatialDeriv i η) (g j) z -
          lebesgueConvolution (spatialDeriv i η) (fun y => C.principal i j y * g j y) z +
          lebesgueConvolution η (fun y => spatialDeriv i (C.principal i j) y * g j y) z)) -
      (∑ i : Fin n, lebesgueConvolution η (fun y => C.drift i y * g i y) z) -
      lebesgueConvolution η (fun y => C.zeroth y * u y) z +
      lebesgueConvolution η f z := by
  have heq := mollified_principal_equation_of_forcing hU hV hC hu hf hforce
    hg hweak hη hηc hs hz
  have hfirst (i : Fin n) : spatialDeriv i (lebesgueConvolution η u) z =
      lebesgueConvolution η (g i) z :=
    fderiv_lebesgueConvolution_eq_weakDerivative hU hu (hg i) (hweak i) hη hηc (hs z hz)
  simp only [Coefficients.operator, hfirst, Finset.sum_sub_distrib,
    Finset.sum_add_distrib] at heq
  simp only [spatialSecond, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith only [heq]

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical

