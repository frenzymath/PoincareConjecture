import PoincareConjecture.Proofs.M76.Triangulation.PLCylinderCompression
import PoincareConjecture.Proofs.M76.Mathlib.RelativeCompactifiedConjugation
import PoincareConjecture.Proofs.M76.Mathlib.RelativeAlexanderIsotopy

set_option autoImplicit false

open Set Metric
open Geometry

namespace PoincareConjecture.M76

theorem exists_plHandleCompactification (ι : Type*) [Fintype ι] (J : Finset ι) :
    ∃ p : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
      p.source = univ ∧ p.target = ball 0 2 ∧
      (∀ x, ‖x‖ ≤ 1 → p x = x) ∧
      LocallyPiecewiseAffineOn p p.source ∧ LocallyPiecewiseAffineOn p.symm p.target ∧
      ∀ (g : coordinateCylinder J ≃ₜ coordinateCylinder J) (C : ℝ),
        0 ≤ C → (∀ x : coordinateCylinder J, ‖(g x : ι → ℝ) - x‖ ≤ C) →
        (∀ x : coordinateCylinder J, (x : ι → ℝ) ∈ frontier (coordinateCylinder J) → g x = x) →
        ∃ H : (ι → ℝ) ≃ₜ (ι → ℝ),
          (∀ x : coordinateCylinder J, H (p x) = p (g x)) ∧
          Nonempty (ContinuousMap.HomotopyWith (ContinuousMap.id (ι → ℝ)) ⟨H, H.continuous⟩
            (fun f => IsHomeomorph f ∧ (∀ x, 2 ≤ ‖x‖ → f x = x) ∧
              ∀ x ∈ (coordinateCylinder J)ᶜ ∪ frontier (coordinateCylinder J), f x = x)) := by
  obtain ⟨p, hps, hpt, hcore, hpPL, hpiPL, hpcyl, hcompact⟩ :=
    exists_plCylinderCompression ι J
  refine ⟨p, hps, hpt, hcore, hpPL, hpiPL, ?_⟩
  intro g C hC hbound hfront
  let g' := g.closedExtension (isClosed_coordinateCylinder J) hfront
  have hg' : ∀ x, ‖g' x - x‖ ≤ C :=
    g.norm_closedExtension_sub_le (isClosed_coordinateCylinder J) hfront hC hbound
  obtain ⟨H, hH, hHout⟩ := hcompact g' C hg'
  have hHball (x : ι → ℝ) (hx : 2 ≤ ‖x‖) : H x = x :=
    hHout x (by simpa only [mem_ball_zero_iff, not_lt] using hx)
  have hg'out (x : ι → ℝ) (hx : x ∉ coordinateCylinder J) : g' x = x :=
    g.closedExtension_apply_notMem (isClosed_coordinateCylinder J) hfront hx
  have hHrel := Homeomorph.compactified_conjugate_fixed_relative p hpcyl g' H hg'out hH
    (fun y hy => hHout y (hpt ▸ hy))
  have hstar : StarConvex ℝ (0 : ι → ℝ) (coordinateCylinder J) :=
    (convex_coordinateCylinder J).starConvex (by intro i _; simp)
  refine ⟨H, ?_, ⟨H.relativeSupportedAlexanderHomotopy (by norm_num) hHball hstar
    (fun x hx => hHrel x (Or.inl hx))⟩⟩
  intro x
  have he : g' x = (g x : ι → ℝ) :=
    g.closedExtension_apply_mem (isClosed_coordinateCylinder J) hfront x.property
  simpa only [he] using hH x

end PoincareConjecture.M76
