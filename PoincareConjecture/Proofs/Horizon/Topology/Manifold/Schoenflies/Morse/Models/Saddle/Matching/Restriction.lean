import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Matching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Coordinates

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem matching_on_closedSquare_after_ambient_map
    {f : S2 → E3} {e d : OpenPartialHomeomorph E2 S2}
    (F D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {s ρ r : Real} (hs : 0 < s) (hr : 0 ≤ r)
    (hrρ : 2 * r ≤ Real.sqrt s * ρ)
    (hd : closedBall (0 : E2) ρ ⊆ d.source)
    (he : ∀ x ∈ closedBall (0 : E2) ρ, Real.sqrt s • x ∈ e.source)
    (hmatch : ∀ x ∈ closedBall (0 : E2) ρ,
      F (d x) = f (e (Real.sqrt s • x))) :
    ∀ x ∈ SaddleLevel.closedSquare r,
      (Real.sqrt s)⁻¹ • x ∈ d.source ∧ x ∈ e.source ∧
        (F.trans D) (d ((Real.sqrt s)⁻¹ • x)) = D (f (e x)) := by
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  intro x hx
  have hxnorm : ‖x‖ ≤ 2 * r :=
    mem_closedBall_zero_iff.mp (SaddleLevel.closedSquare_subset_closedBall hr hx)
  have hscaled : (Real.sqrt s)⁻¹ • x ∈ closedBall (0 : E2) ρ := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hsqrt), inv_mul_eq_div]
    exact (div_le_iff₀ hsqrt).mpr (by nlinarith)
  have hcancel : Real.sqrt s • ((Real.sqrt s)⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ hsqrt.ne', one_smul]
  refine ⟨hd hscaled, ?_, ?_⟩
  · simpa only [hcancel] using he _ hscaled
  · change D (F (d ((Real.sqrt s)⁻¹ • x))) = D (f (e x))
    rw [hmatch _ hscaled, hcancel]

end Poincare.Manifold.Schoenflies.Saddle
