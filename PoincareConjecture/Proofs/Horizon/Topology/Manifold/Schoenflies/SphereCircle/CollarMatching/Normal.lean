import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.CollarDifferential
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.CircleCollar

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

theorem normal_derivative_pos_of_inward
    {k : E2 -> E2} (hk : ContDiff Real ∞ k)
    (hfix : ∀ p : S1, k p = p)
    (hinj : ∀ p : S1, Injective (fderiv Real k p))
    (hinside : ∀ p : S1, ∀ᶠ t in 𝓝[<] (0 : Real), ‖k ((1 + t) • (p : E2))‖ < 1)
    (p : S1) : 0 < inner Real (p : E2) (fderiv Real k p p) := by
  have hcurve : HasDerivAt (fun t : Real => k ((1 + t) • (p : E2)))
      (fderiv Real k p p) 0 := by
    have hd := ((hasDerivAt_const (0 : Real) (1 : Real)).add (hasDerivAt_id 0)).smul_const (p : E2)
    have hk0 : HasFDerivAt k (fderiv Real k p) ((1 + (0 : Real)) • (p : E2)) := by
      simpa using (hk.differentiable (by simp) p).hasFDerivAt
    have hc := hk0.comp_hasDerivAt 0
      (show HasDerivAt (fun t : Real => (1 + t) • (p : E2)) (p : E2) 0 by simpa using hd)
    convert! hc using 1
  have hlim := hcurve.norm_sq.tendsto_slope_zero_left
  have hnonneg : 0 ≤ 2 * inner Real (p : E2) (fderiv Real k p p) := by
    simp only [zero_add, add_zero, one_smul, hfix p, norm_eq_of_mem_sphere p, one_pow] at hlim
    apply ge_of_tendsto hlim
    filter_upwards [hinside p, self_mem_nhdsWithin] with t ht htneg
    change 0 ≤ t⁻¹ * (‖k ((1 + t) • (p : E2))‖ ^ 2 - 1)
    apply mul_nonneg_of_nonpos_of_nonpos
    · exact inv_nonpos.mpr (le_of_lt htneg)
    · nlinarith [norm_nonneg (k ((1 + t) • (p : E2)))]
  have hne : inner Real (p : E2) (fderiv Real k p p) ≠ 0 := by
    intro hz
    have htan := fderiv_eq_self_on_circle_tangent hk hfix p
      (fderiv Real k p p) hz
    have heq : fderiv Real k p p = (p : E2) := (hinj p) htan
    rw [heq] at hz
    simp at hz
  exact lt_of_le_of_ne (by linarith) hne.symm

end Poincare.Manifold.Schoenflies.CircleCollar
