import PoincareConjecture.Proofs.M76.Mathlib.CoreCompressionDisplacement
import PoincareConjecture.Proofs.M76.Mathlib.VanishingDisplacementExtension
import Mathlib.Topology.OpenPartialHomeomorph.Basic










set_option autoImplicit false

open Set Metric

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




noncomputable def coreBall : E ≃ₜ ball (0 : E) 2 :=
  (Homeomorph.Set.univ E).symm.trans
    (OpenPartialHomeomorph.coreCompression.toHomeomorphSourceTarget)



theorem coreBall_apply (x : E) : (coreBall x : E) = NormedSpace.coreCompression x := rfl




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



theorem coreRadialCompactification_apply_mem (g : E ≃ₜ E) {C : ℝ}
    (hC : ∀ x, ‖g x - x‖ ≤ C) {y : E} (hy : y ∈ ball (0 : E) 2) :
    g.coreRadialCompactification hC y =
      (coreBall (g (coreBall.symm ⟨y, hy⟩)) : E) := by
  classical
  exact Equiv.Perm.extendDomain_apply_subtype
    (((coreBall : E ≃ₜ ball (0 : E) 2).symm.trans g).trans coreBall).toEquiv
    (Equiv.refl (ball (0 : E) 2)) hy



theorem coreRadialCompactification_fixed_outside (g : E ≃ₜ E) {C : ℝ}
    (hC : ∀ x, ‖g x - x‖ ≤ C) {y : E} (hy : y ∉ ball (0 : E) 2) :
    g.coreRadialCompactification hC y = y := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype
    (((coreBall : E ≃ₜ ball (0 : E) 2).symm.trans g).trans coreBall).toEquiv
    (Equiv.refl (ball (0 : E) 2)) hy

end Homeomorph
