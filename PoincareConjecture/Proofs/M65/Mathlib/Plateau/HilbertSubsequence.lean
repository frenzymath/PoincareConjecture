import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

set_option autoImplicit false

open Filter Set Metric
open scoped Topology

namespace InnerProductSpace

theorem exists_subsequence_tendsto_inner_of_norm_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (u : ℕ → E) {C : ℝ} (hbound : ∀ n, ‖u n‖ ≤ C) :
    ∃ (u0 : E) (phi : ℕ → ℕ), StrictMono phi ∧ ‖u0‖ ≤ C ∧
      ∀ v : E, Tendsto (fun n => ⟪u (phi n), v⟫_ℝ) atTop (𝓝 ⟪u0, v⟫_ℝ) := by
  let ell : ℕ → WeakDual ℝ E := fun n => StrongDual.toWeakDual (toDual ℝ E (u n))
  have hmem (n : ℕ) :
      ell n ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) C := by
    simpa only [mem_preimage, mem_closedBall, dist_zero_right, ell,
      StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hbound n
  obtain ⟨ell0, hell0, phi, hphi, hconv⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) C hmem
  let u0 : E := (toDual ℝ E).symm (WeakDual.toStrongDual ell0)
  refine ⟨u0, phi, hphi, ?_, ?_⟩
  · simpa only [mem_preimage, mem_closedBall, dist_zero_right, u0,
      LinearIsometryEquiv.norm_map] using hell0
  · intro v
    have htest := ((WeakDual.eval_continuous v).tendsto ell0).comp hconv
    simpa only [Function.comp_def, ell, StrongDual.toWeakDual_apply,
      toDual_apply_apply, u0, toDual_symm_apply, WeakDual.toStrongDual_apply] using htest

end InnerProductSpace
