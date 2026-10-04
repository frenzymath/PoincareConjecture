import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.ReplacementIntegration

/-!
# Splitting and projecting genuine L2 Green pairings

All products are integrable by the L2 bounds. Scalar and coordinate
Green identities therefore recover the vector weak equations used by
the actual annulus replacement. Source: M64 phase-cone flux gluing.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open MeasureTheory

namespace PoincareMT

/-- Genuine L2 data justify splitting the scalar weak Green pairing. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. M64 derivation
2026-09-26-phase-cone-normalization.md. -/
theorem m64L2_scalar_green_pairing {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {u v phi psi : X → ℝ} (hu : MemLp u 2 mu) (hv : MemLp v 2 mu)
    (hp : MemLp phi 2 mu) (hq : MemLp psi 2 mu) :
    (∫ x, phi x * v x ∂mu) + (∫ x, psi x * u x ∂mu) =
      ∫ x, v x * phi x + u x * psi x ∂mu := by
  have hi1 : Integrable (fun x => phi x * v x) mu := m64L2_test_integrable hv hp
  have hi2 : Integrable (fun x => psi x * u x) mu := m64L2_test_integrable hu hq
  rw [← integral_add hi1 hi2]
  congr 1
  funext x
  ring

/-- Each coordinate of the actual vector Green pairing equals the integrable scalar pairing
of the same fields. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. M64
derivation 2026-09-26-phase-cone-normalization.md. -/
theorem m64L2_vector_green_pairing {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {N : ℕ} {u v : X → EuclideanSpace ℝ (Fin N)} {phi psi : X → ℝ}
    (hu : MemLp u 2 mu) (hv : MemLp v 2 mu)
    (hp : MemLp phi 2 mu) (hq : MemLp psi 2 mu) (j : Fin N) :
    ((∫ x, phi x • v x ∂mu) + (∫ x, psi x • u x ∂mu)) j =
      ∫ x, v x j * phi x + u x j * psi x ∂mu := by
  have hi1 := m64L2_test_integrable hv hp
  have hi2 := m64L2_test_integrable hu hq
  rw [PiLp.add_apply, eval_integral_piLp hi1.eval_piLp j,
    eval_integral_piLp hi2.eval_piLp j]
  simp only [PiLp.smul_apply, smul_eq_mul]
  exact m64L2_scalar_green_pairing (hu.eval_piLp j) (hv.eval_piLp j) hp hq

end PoincareMT
