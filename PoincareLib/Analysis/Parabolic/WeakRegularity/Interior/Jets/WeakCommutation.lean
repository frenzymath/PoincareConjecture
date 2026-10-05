/-
Adapted from AxelWorkspace revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source and SHA-256: references/analysis/axel-workspace/weak-parabolic-regularity-sources.json.
Apache-2.0; see the license in that source directory.
-/
import PoincareLib.Analysis.Parabolic.WeakRegularity.Interior.ConstantEnergy

/-!
# Commuting mixed weak derivatives

Two constant directional weak derivatives commute by transferring both
derivatives to a smooth compact test function.

References: Evans, second edition, Section 5.2.1, pp. 256-257;
Morgan--Tian, Proposition 9.20, pp. 207-208.
-/

open Set MeasureTheory
open scoped ContDiff

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

/-- A known mixed weak derivative also represents the reversed derivative. -/
theorem weak_directional_derivative_comm
    {n : ℕ} {U : Set (Spacetime n)} (_hU : IsOpen U)
    {u g h k : Spacetime n → ℝ} (v w : Spacetime n)
    (_hu : LocallyIntegrableOn u U volume)
    (_hg : LocallyIntegrableOn g U volume)
    (_hh : LocallyIntegrableOn h U volume)
    (_hk : LocallyIntegrableOn k U volume)
    (hgweak : ∀ ψ : Spacetime n → ℝ, ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * g y) = -(∫ y in U, fderiv ℝ ψ y v * u y))
    (hhweak : ∀ ψ : Spacetime n → ℝ, ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * h y) = -(∫ y in U, fderiv ℝ ψ y w * u y))
    (hkweak : ∀ ψ : Spacetime n → ℝ, ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * k y) = -(∫ y in U, fderiv ℝ ψ y w * g y))
    {φ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ y in U, φ y * k y) = -(∫ y in U, fderiv ℝ φ y v * h y) := by
  have hDv : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y v) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDw : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y w) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have h1 := hkweak φ hφ hφc hφU
  have h2 := hgweak (fun y => fderiv ℝ φ y w) hDw (hφc.fderiv_apply ℝ w)
    ((tsupport_fderiv_apply_subset ℝ w).trans hφU)
  have h3 := hhweak (fun y => fderiv ℝ φ y v) hDv (hφc.fderiv_apply ℝ v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hφU)
  have hcomm (y) : fderiv ℝ (fun z => fderiv ℝ φ z w) y v =
      fderiv ℝ (fun z => fderiv ℝ φ z v) y w := by
    exact directionalSecond_comm φ hφ v w y
  simp_rw [hcomm] at h2
  linarith only [h1, h2, h3]

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical

