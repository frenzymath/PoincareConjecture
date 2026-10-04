import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.H1Coordinates
import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.H2JetCoordinates

/-!
# Actual L2 graph coordinates for periodic H1

The Fourier Hilbert-basis isometry gives the L2 derivative coordinate and
a bounded reconstruction from function/derivative pairs. MT2007 Claim
19.1, p. 437; `2026-09-21-smooth-h1-graph-composition.md`, items 2-4.
-/

set_option autoImplicit false

open AddCircle MeasureTheory

namespace PoincareMT.M63

variable {L : ℝ} [Fact (0 < L)]

/-- The actual L2 derivative coordinate of a completed H1 state.
MT2007 Claim 19.1, p. 437; smooth H1 graph derivation, item 2.
No classical differentiability is asserted by this definition. -/
noncomputable def periodicH1DerivativeLp :
    lp (fun _ : ℤ => ℂ) 2 →L[ℂ] Lp ℂ 2 (@haarAddCircle L _) :=
  fourierBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (periodicH2JetCoordinates (L := L) 1 (by omega))

/-- Reconstruction from an arbitrary pair of actual spatial L2 fields.
MT2007 Claim 19.1, p. 437; smooth H1 graph derivation, item 3. The product
uses its maximum norm; a derivative relation is not part of the domain. -/
noncomputable def periodicH1GraphReconstruct :
    (Lp ℂ 2 (@haarAddCircle L _) × Lp ℂ 2 (@haarAddCircle L _)) →L[ℂ]
      lp (fun _ : ℤ => ℂ) 2 :=
  ((periodicH2JetCoordinates (L := L) 0 (by omega)).comp
    fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (ContinuousLinearMap.fst ℂ _ _) -
  ((periodicH2JetCoordinates (L := L) 1 (by omega)).comp
    fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (ContinuousLinearMap.snd ℂ _ _)

/-- The graph reconstruction is bounded on arbitrary pairs and exactly
recovers actual C1 coordinates and their L2 derivative. MT2007 Claim
19.1, p. 437; smooth H1 graph derivation, item 4, including the zero mode. -/
theorem periodicH1Graph_spec :
    (∀ f g : Lp ℂ 2 (@haarAddCircle L _),
      ‖periodicH1GraphReconstruct (L := L) (f, g)‖ ≤ ‖f‖ + ‖g‖) ∧
    ∀ (f g : C(AddCircle L, ℂ))
      (hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L)) (g (x : AddCircle L)) x),
      periodicH1DerivativeLp (periodicH1Coordinates f g hf) =
        ContinuousMap.toLp 2 haarAddCircle ℂ g ∧
      periodicH1GraphReconstruct
        (ContinuousMap.toLp 2 haarAddCircle ℂ f, ContinuousMap.toLp 2 haarAddCircle ℂ g) =
        periodicH1Coordinates f g hf := by
  constructor
  · intro f g
    change ‖periodicH2JetCoordinates (L := L) 0 (by omega) (fourierBasis.repr f) -
      periodicH2JetCoordinates (L := L) 1 (by omega) (fourierBasis.repr g)‖ ≤ _
    apply (norm_sub_le _ _).trans
    have hf := (periodicH2JetCoordinates_spec (L := L) 0 (by omega) (fourierBasis.repr f)).1
    have hg := (periodicH2JetCoordinates_spec (L := L) 1 (by omega) (fourierBasis.repr g)).1
    simpa only [LinearIsometryEquiv.norm_map] using add_le_add hf hg
  · intro f g hf
    have hr (n : ℤ) :
        (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
    constructor
    · apply fourierBasis.repr.injective
      change fourierBasis.repr (fourierBasis.repr.symm
        (periodicH2JetCoordinates (L := L) 1 (by omega) (periodicH1Coordinates f g hf))) = _
      rw [LinearIsometryEquiv.apply_symm_apply]
      apply lp.ext
      funext n
      change periodicSobolevMoment L 0 1 n *
        ((Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ) * fourierCoeff f n) = _
      rw [fourierBasis_repr, fourierCoeff_toLp, fourierCoeff_circle_derivative f g hf]
      simp only [periodicSobolevMoment, pow_one, zero_add]
      rw [← mul_assoc, div_mul_cancel₀ _ (hr n)]
    · apply lp.ext
      funext n
      change periodicSobolevMoment L 0 0 n *
          fourierBasis.repr (ContinuousMap.toLp 2 haarAddCircle ℂ f) n -
        periodicSobolevMoment L 0 1 n *
          fourierBasis.repr (ContinuousMap.toLp 2 haarAddCircle ℂ g) n =
        (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ) * fourierCoeff f n
      rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_toLp, fourierCoeff_toLp,
        fourierCoeff_circle_derivative f g hf]
      let omega : ℝ := 2 * Real.pi * (n : ℝ) / L
      let rho : ℝ := Real.sqrt (1 + omega ^ 2)
      have hs : (rho : ℂ) ^ 2 = 1 + (omega : ℂ) ^ 2 := by
        exact_mod_cast (Real.sq_sqrt (by positivity : 0 ≤ 1 + omega ^ 2))
      have hc : (rho : ℂ) ≠ 0 := hr n
      have hfactor : 1 / (rho : ℂ) -
          (Complex.I * (omega : ℂ) / (rho : ℂ)) * (Complex.I * (omega : ℂ)) = rho := by
        rw [div_mul_eq_mul_div, ← sub_div, div_eq_iff hc]
        calc
          1 - Complex.I * (omega : ℂ) * (Complex.I * (omega : ℂ)) =
              1 + (omega : ℂ) ^ 2 := by
            rw [← pow_two, mul_pow, Complex.I_sq]
            ring
          _ = (rho : ℂ) * rho := by simpa only [pow_two] using hs.symm
      simp only [periodicSobolevMoment, pow_zero, pow_one, zero_add]
      change (1 / (rho : ℂ)) * fourierCoeff f n -
        (Complex.I * (omega : ℂ) / (rho : ℂ)) *
          (Complex.I * (omega : ℂ) * fourierCoeff f n) = (rho : ℂ) * fourierCoeff f n
      rw [← mul_assoc, ← sub_mul, hfactor]

end PoincareMT.M63
