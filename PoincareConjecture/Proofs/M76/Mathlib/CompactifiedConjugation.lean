import PoincareConjecture.Proofs.M76.Mathlib.CompactVanishingExtension
import PoincareConjecture.Proofs.M76.Mathlib.CoreBoundedCompactification
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set Metric

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_extension_core_coordinate_change (p : E ≃ₜ ball (0 : E) 2)
    {D : ℝ} (herror : ∀ x, ‖(p x : E) - NormedSpace.coreCompression x‖ ≤
      D * (2 - ‖NormedSpace.coreCompression x‖)) :
    ∃ F : E ≃ₜ E,
      (∀ x, F (NormedSpace.coreCompression x) = (p x : E)) ∧
      ∀ y ∉ ball (0 : E) 2, F y = y := by
  let e := (coreBall : E ≃ₜ ball (0 : E) 2).symm.trans p
  have hbound (y : ball (0 : E) 2) :
      ‖(e y : E) - y‖ ≤ D * max (2 - ‖(y : E)‖) 0 := by
    have he : NormedSpace.coreCompression (coreBall.symm y) = (y : E) :=
      congrArg Subtype.val ((coreBall : E ≃ₜ ball (0 : E) 2).apply_symm_apply y)
    have hy : 0 < 2 - ‖(y : E)‖ := sub_pos.mpr (mem_ball_zero_iff.mp y.property)
    change ‖(p (coreBall.symm y) : E) - y‖ ≤ _
    simpa only [he, max_eq_left hy.le] using herror (coreBall.symm y)
  have hcompact : IsCompact (closure (ball (0 : E) 2)) :=
    (isCompact_closedBall (0 : E) 2).of_isClosed_subset
      isClosed_closure closure_ball_subset_closedBall
  obtain ⟨F, hF, hfix⟩ := e.exists_extension_of_compact_vanishing_bound isOpen_ball hcompact
    (b := fun y => D * max (2 - ‖y‖) 0) (by fun_prop) (by
      intro y hy
      have hn : 2 ≤ ‖y‖ := by simpa only [mem_compl_iff, mem_ball_zero_iff, not_lt] using hy
      dsimp only
      rw [max_eq_right (by linarith), mul_zero]) hbound
  refine ⟨F, fun x => ?_, hfix⟩
  have h := hF (coreBall x)
  simpa only [coreBall_apply, Homeomorph.trans_apply, Homeomorph.symm_apply_apply, e] using h

theorem exists_compactification_of_core_error (p : E ≃ₜ ball (0 : E) 2)
    {D : ℝ} (herror : ∀ x, ‖(p x : E) - NormedSpace.coreCompression x‖ ≤
      D * (2 - ‖NormedSpace.coreCompression x‖))
    (g : E ≃ₜ E) {C : ℝ} (hC : ∀ x, ‖g x - x‖ ≤ C) :
    ∃ H : E ≃ₜ E,
      (∀ x, H (p x) = (p (g x) : E)) ∧ ∀ y ∉ ball (0 : E) 2, H y = y := by
  obtain ⟨F, hF, hfix⟩ := p.exists_extension_core_coordinate_change herror
  let G := g.coreRadialCompactification hC
  let H := (F.symm.trans G).trans F
  refine ⟨H, ?_, ?_⟩
  · intro x
    have hFi : F.symm (p x) = NormedSpace.coreCompression x := by
      apply F.injective
      rw [F.apply_symm_apply, hF]
    change F (G (F.symm (p x))) = (p (g x) : E)
    rw [hFi]
    have hG : G (NormedSpace.coreCompression x) = NormedSpace.coreCompression (g x) := by
      have h := g.coreRadialCompactification_apply_mem hC (coreBall x).property
      change G (NormedSpace.coreCompression x) =
        (coreBall (g (coreBall.symm (coreBall x))) : E) at h
      simpa only [Homeomorph.symm_apply_apply, coreBall_apply] using h
    rw [hG, hF]
  · intro y hy
    have hFi : F.symm y = y := by
      apply F.injective
      rw [F.apply_symm_apply, hfix y hy]
    change F (G (F.symm y)) = y
    rw [hFi, g.coreRadialCompactification_fixed_outside hC hy, hfix y hy]

end Homeomorph
