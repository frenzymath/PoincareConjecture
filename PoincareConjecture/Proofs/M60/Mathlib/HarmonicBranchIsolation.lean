import PoincareConjecture.Proofs.M60.Mathlib.HarmonicComplexSystem
import PoincareConjecture.Proofs.M60.Mathlib.HolomorphicFrameLocal

set_option autoImplicit false

open Complex Set Filter Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M60

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem complexGradient_eq_zero_iff {u : ℂ → E} {z : ℂ} :
    complexGradient (complexCoordinates n) u z = 0 ↔ fderiv ℝ u z = 0 := by
  rw [complexGradient, complexCoordinates_sub_I_smul_eq_zero_iff]
  constructor
  · rintro ⟨h₁, hI⟩
    ext w
    have hw : w = w.re • (1 : ℂ) + w.im • I := by
      simpa only [real_smul, mul_one] using w.re_add_im.symm
    rw [hw, map_add, map_smul, map_smul, h₁, hI]
    simp
  · intro h
    simp [h]

theorem harmonic_differential_eventually_zero_or_isolated
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : ℂ → E} {O : Set ℂ}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O)
    (hΓ : ∀ z ∈ O, ContDiffAt ℝ 1 Γ (u z))
    (hsym : ∀ z ∈ O, ∀ a b : E, Γ (u z) a b = Γ (u z) b a)
    (hτ : ∀ z ∈ O,
      ConnectionVariation.covDerivAlong Γ u (fun w => fderiv ℝ u w 1) 1 z +
        ConnectionVariation.covDerivAlong Γ u (fun w => fderiv ℝ u w I) I z = 0)
    {z : ℂ} (hz : z ∈ O) :
    (∀ᶠ w in 𝓝 z, fderiv ℝ u w = 0) ∨
      ∀ᶠ w in 𝓝[≠] z, fderiv ℝ u w ≠ 0 := by
  let A := harmonicComplexOperator Γ u
  let W := complexGradient (complexCoordinates n) u
  have huAt (w : ℂ) (hw : w ∈ O) : ContDiffAt ℝ 2 u w :=
    hu.contDiffAt (hO.mem_nhds hw)
  have hA : ContDiffOn ℝ 1 A O := fun w hw =>
    (contDiffAt_harmonicComplexOperator (hΓ w hw) (huAt w hw)).contDiffWithinAt
  have hW : ContDiffOn ℝ 1 W O := fun w hw =>
    (contDiffAt_complexGradient _ (huAt w hw)).contDiffWithinAt
  obtain ⟨r, P, hr, hrO, hP, hPunit, hPeq⟩ :=
    exists_local_c1_invertible_frame hO hA hz
  have hWeq (w : ℂ) (hw : w ∈ ball z r) : cauchyRiemannDerivative W w = A w (W w) :=
    complexGradient_equation_of_covDeriv (huAt w (hrO hw))
      (hsym w (hrO hw)) (hτ w (hrO hw))
  have h := eventually_zero_or_isolated_of_frame isOpen_ball (mem_ball_self hr)
    hP.contDiffOn (hW.mono hrO) (fun w _ => hPunit w) hPeq hWeq
  simpa only [W, ne_eq, complexGradient_eq_zero_iff] using h

end PoincareConjecture.M60
