import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.StressTrigonometricModes
import PoincareLib.Geometry.CurveShortening.Comparison.Analysis.L1.TrigonometricUniqueness

/-!
# Vanishing of integrable annular stress

The two periodic stress identities and modulus balance imply zero stress
almost everywhere. Countable Fourier uniqueness is applied to the actual
L1 slices and then Fubini to their norms. Source: Lemaire 1982, Lemma 5.1,
p. 99; M64's second-stress-cutoff derivation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareMT

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "nu" => volume.restrict (Icc (0 : ℝ) 1)

/-- Zero actual trigonometric horizontal moments imply that an L1 field on the rectangle is
zero almost everywhere. Source: the final Fubini step in M64's second-stress-cutoff
derivation. Exact proof derivation: `2026-09-26-second-stress-cutoff.md`. -/
theorem m64Annulus_zero_of_trigonometric_moments
    {f : LoopPlane → ℝ} (hf : Integrable f mu)
    (hc : ∀ j : ℤ, m64HorizontalMoment (fun x => Real.cos (j * x)) f =ᵐ[nu] (fun _ => 0))
    (hs : ∀ j : ℤ, m64HorizontalMoment (fun x => Real.sin (j * x)) f =ᵐ[nu] (fun _ => 0)) :
    f =ᵐ[mu] (fun _ => 0) := by
  have hi := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hf
  have hnorm : (∫ p in S, ‖f p‖) = 0 := by
    rw [m64AnnulusInteriorIntegral_eq_iterated_swap_integrable _ hf.norm]
    apply integral_eq_zero_of_ae
    filter_upwards [hi.prod_left_ae, ae_all_iff.mpr hc, ae_all_iff.mpr hs]
      with s hfs hcs hss
    have hzero := m64L1Trigonometric_eq_zero hfs hcs hss
    apply integral_eq_zero_of_ae
    filter_upwards [hzero] with x hx
    exact norm_eq_zero.mpr hx
  have hzero := (integral_eq_zero_iff_of_nonneg (fun p => norm_nonneg (f p)) hf.norm).mp hnorm
  filter_upwards [hzero] with p hp
  exact norm_eq_zero.mp hp

/-- Two periodic weak stress identities with a nonnegative coupling and zero total diagonal
stress force both actual L1 stress fields to vanish. Source: Lemaire, Lemma 5.1, p. 99;
M64's second-stress-cutoff derivation. Exact proof derivation:
`2026-09-26-second-stress-cutoff.md`. -/
theorem m64AnnulusStress_eq_zero
    {U V : LoopPlane → ℝ} (hU : Integrable U mu) (hV : Integrable V mu)
    {c : ℝ} (hc : 0 ≤ c)
    (hfirst : ∀ eta rho : ℝ → ℝ, ContDiff ℝ ∞ eta →
      Function.Periodic eta curvePeriod → ContDiff ℝ ∞ rho → HasCompactSupport rho →
      (∫ p in S, deriv eta (p 0) * rho (p 1) * U p +
        eta (p 0) * deriv rho (p 1) * V p) = 0)
    (hsecond : ∀ eta rho : ℝ → ℝ, ContDiff ℝ ∞ eta →
      Function.Periodic eta curvePeriod → ContDiff ℝ ∞ rho → HasCompactSupport rho →
      tsupport rho ⊆ Ioo (0 : ℝ) 1 →
      (∫ p in S, deriv eta (p 0) * rho (p 1) * (-c * V p) +
        eta (p 0) * deriv rho (p 1) * U p) = 0)
    (hbalance : (∫ p in S, U p) = 0) :
    U =ᵐ[mu] (fun _ => 0) ∧ V =ᵐ[mu] (fun _ => 0) := by
  have hm := m64AnnulusStress_trigonometric_modes_zero hU hV hc hfirst hsecond
  have h0 := m64AnnulusStress_constant_mode_zero hU hV
    (fun rho hr hs ht => hsecond (fun _ => 1) rho contDiff_const (fun _ => rfl) hr hs ht)
    hbalance
  constructor
  · apply m64Annulus_zero_of_trigonometric_moments hU
    · intro j
      by_cases hj : j = 0
      · subst j
        simpa only [Int.cast_zero, zero_mul, Real.cos_zero] using h0
      · exact ((hm j).2.2 hj).1
    · intro j
      by_cases hj : j = 0
      · subst j
        filter_upwards [] with s
        simp only [Int.cast_zero, zero_mul, Real.sin_zero, m64HorizontalMoment, integral_zero]
      · exact ((hm j).2.2 hj).2
  · exact m64Annulus_zero_of_trigonometric_moments hV
      (fun j => (hm j).1) (fun j => (hm j).2.1)

end PoincareMT
