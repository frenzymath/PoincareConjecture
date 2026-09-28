import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Variation



noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem geodesicVariation_jacobi
    [CompleteSpace E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {S I : Set ℝ}
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ x ∈ U, (B x).IsInvertible)
    (hsymm : ∀ x ∈ U, ∀ u v, B x u v = B x v u)
    (hS : IsOpen S) (hI : IsOpen I) (h0 : (0 : ℝ) ∈ S)
    (Γ : GeodesicVariation B S I)
    (hmem : ∀ s ∈ S, ∀ t ∈ I, (Γ.phase (s, t)).1 ∈ U) :
    ∀ t ∈ I,
      alongCovariantDerivative B
          (fun τ => (Γ.phase (0, τ)).1)
          (alongCovariantDerivative B
            (fun τ => (Γ.phase (0, τ)).1) (variationField Γ) ·) t +
      coordinateCurvature B (Γ.phase (0, t)).1
          (variationField Γ t) (Γ.phase (0, t)).2 (Γ.phase (0, t)).2 = 0 := by
  have hA (p : ℝ × ℝ) (hp : p ∈ S ×ˢ I) :
      ContDiffAt ℝ ∞ (christoffelBilinear B) (Γ.phase p).1 := by
    have hx := hmem p.1 hp.1 p.2 hp.2
    exact contDiffAt_christoffelBilinear (hB.contDiffAt (hU.mem_nhds hx)) (hinv _ hx)
  have hsymmA (p : ℝ × ℝ) (hp : p ∈ S ×ˢ I) (u v : E) :
      christoffelBilinear B (Γ.phase p).1 u v =
        christoffelBilinear B (Γ.phase p).1 v u := by
    have hx := hmem p.1 hp.1 p.2 hp.2
    exact christoffelBilinear_symm
      ((hB.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
      (Filter.Eventually.mono (hU.mem_nhds hx) fun y hy => hsymm y hy) u v
  intro t ht
  rw [coordinateCurvature_eq_christoffelCurvature
    ((hA (0, t) ⟨h0, ht⟩).differentiableAt (by simp))]
  exact Γ.jacobi_of_coefficients hS hI (christoffelBilinear B)
    hA hsymmA (christoffelBilinear_apply B) t ht

end PoincareConjecture.CoordinateExponential
