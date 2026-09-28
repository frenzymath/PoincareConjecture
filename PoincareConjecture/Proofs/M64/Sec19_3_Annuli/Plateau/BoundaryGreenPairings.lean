import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementIntegration












noncomputable section
set_option autoImplicit false
set_option warningAsError true

open MeasureTheory

namespace PoincareConjecture




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

end PoincareConjecture
