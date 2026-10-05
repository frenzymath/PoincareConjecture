import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CoreCompressionDisplacement
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.VanishingDisplacementExtension
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Compactifying bounded homeomorphisms in core-fixing coordinates

The rational core-fixing compression conjugates a bounded
homeomorphism to a ball homeomorphism whose displacement vanishes
at the boundary. See Hamilton 1976, pp. 65, 67--68 and
M76 derivation 87. The coordinate map here is still nonlinear.
-/

set_option autoImplicit false

open Set Metric

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual core-fixing homeomorphism from the whole space
to the radius-two ball. See Hamilton pp. 67--68 and M76
derivations 86--87. -/
noncomputable def coreBall : E ≃ₜ ball (0 : E) 2 :=
  (Homeomorph.Set.univ E).symm.trans
    (OpenPartialHomeomorph.coreCompression.toHomeomorphSourceTarget)

/-- The core-ball homeomorphism uses the rational compression
formula. See M76 derivation 87. -/
theorem coreBall_apply (x : E) : (coreBall x : E) = NormedSpace.coreCompression x := rfl

/-- Bounded displacement becomes a continuous boundary-vanishing
bound in core-ball coordinates. See Hamilton pp. 65, 68 and
M76 derivation 87. -/
theorem coreBall_conjugate_bound (g : E ≃ₜ E) {C : ℝ}
    (hC : ∀ x, ‖g x - x‖ ≤ C) (y : ball (0 : E) 2) :
    ‖(coreBall (g (coreBall.symm y)) : E) - y‖ ≤ 2 * C * max (2 - ‖(y : E)‖) 0 := by
  let x := (coreBall : E ≃ₜ ball (0 : E) 2).symm y
  have he : NormedSpace.coreCompression x = (y : E) :=
    congrArg Subtype.val ((coreBall : E ≃ₜ ball (0 : E) 2).apply_symm_apply y)
  have hy : 0 < 2 - ‖(y : E)‖ := sub_pos.mpr (mem_ball_zero_iff.mp y.property)
  change ‖NormedSpace.coreCompression (g x) - (y : E)‖ ≤ _
  rw [max_eq_left hy.le, ← he, norm_sub_rev]
  exact (NormedSpace.norm_coreCompression_sub_le_deficit x (g x)).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hC x)
        (by norm_num)) (by rw [he]; exact hy.le))

/-- A bounded-displacement homeomorphism compactifies in
core-fixing radial coordinates to an ambient homeomorphism
fixed off the radius-two open ball. See Hamilton pp. 65, 68
and M76 derivation 87. -/
noncomputable def coreRadialCompactification (g : E ≃ₜ E) {C : ℝ}
    (hC : ∀ x, ‖g x - x‖ ≤ C) : E ≃ₜ E := by
  let e := ((coreBall : E ≃ₜ ball (0 : E) 2).symm.trans g).trans coreBall
  refine e.extendByVanishingBound isOpen_ball
    (b := fun y => 2 * C * max (2 - ‖y‖) 0) (by fun_prop) ?_
    (coreBall_conjugate_bound g hC) ?_
  · intro y hy
    have hn : 2 ≤ ‖y‖ := by simpa only [mem_compl_iff, mem_ball_zero_iff, not_lt] using hy
    dsimp only
    rw [max_eq_right (by linarith), mul_zero]
  · have hsymm (x : E) : ‖g.symm x - x‖ ≤ C := by
      rw [norm_sub_rev]
      simpa only [g.apply_symm_apply] using hC (g.symm x)
    exact coreBall_conjugate_bound g.symm hsymm

/-- Inside the open ball, the ambient compactification is the
exact conjugate in core-ball coordinates. See M76 derivation 87. -/
theorem coreRadialCompactification_apply_mem (g : E ≃ₜ E) {C : ℝ}
    (hC : ∀ x, ‖g x - x‖ ≤ C) {y : E} (hy : y ∈ ball (0 : E) 2) :
    g.coreRadialCompactification hC y =
      (coreBall (g (coreBall.symm ⟨y, hy⟩)) : E) := by
  classical
  exact Equiv.Perm.extendDomain_apply_subtype
    (((coreBall : E ≃ₜ ball (0 : E) 2).symm.trans g).trans coreBall).toEquiv
    (Equiv.refl (ball (0 : E) 2)) hy

/-- The compactification fixes the sphere and its entire exterior.
See Hamilton p. 68 and M76 derivation 87. -/
theorem coreRadialCompactification_fixed_outside (g : E ≃ₜ E) {C : ℝ}
    (hC : ∀ x, ‖g x - x‖ ≤ C) {y : E} (hy : y ∉ ball (0 : E) 2) :
    g.coreRadialCompactification hC y = y := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype
    (((coreBall : E ≃ₜ ball (0 : E) 2).symm.trans g).trans coreBall).toEquiv
    (Equiv.refl (ball (0 : E) 2)) hy

end Homeomorph
