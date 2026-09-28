import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

set_option autoImplicit false

open Filter Topology

namespace PoincareConjecture.ReducedLengthMinimum.Variational

theorem exists_weak_subsequence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (v : ℕ → H) (C : ℝ) (hbound : ∀ k, ‖v k‖ ≤ C) :
    ∃ w : H, ∃ φ : ℕ → ℕ, ‖w‖ ≤ C ∧ StrictMono φ ∧
      ∀ l : H →L[ℝ] ℝ,
        Tendsto (fun k => l (v (φ k))) atTop (𝓝 (l w)) := by
  let ξ : ℕ → WeakDual ℝ H := fun k =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (v k))
  have hξ : ∀ k, ξ k ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ H) C := by
    intro k
    simpa only [ξ, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hbound k
  obtain ⟨ζ, hζ, φ, hφ, hlim⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) C hξ
  let w : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual ζ)
  refine ⟨w, φ, ?_, hφ, ?_⟩
  · have hz : ‖WeakDual.toStrongDual ζ‖ ≤ C := by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hζ
    simpa only [w, LinearIsometryEquiv.norm_map] using hz
  · intro l
    let z : H := (InnerProductSpace.toDual ℝ H).symm l
    have h := ((WeakDual.eval_continuous z).tendsto ζ).comp hlim
    have heval (q : H) : inner ℝ q z = l q := by
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    have hw : ζ z = l w := by
      change (WeakDual.toStrongDual ζ) z = l w
      rw [← InnerProductSpace.toDual_symm_apply]
      exact heval w
    have htest : Tendsto (fun k => inner ℝ (v (φ k)) z) atTop (𝓝 (ζ z)) := h
    simpa only [heval, hw] using htest

theorem exists_finite_weak_subsequence {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)] [∀ i, TopologicalSpace.SeparableSpace (H i)]
    (v : ∀ i, ℕ → H i) (C : ι → ℝ) (hbound : ∀ i k, ‖v i k‖ ≤ C i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ∀ i, H i,
      ∀ i, ‖w i‖ ≤ C i ∧ ∀ l : H i →L[ℝ] ℝ,
        Tendsto (fun k => l (v i (φ k))) atTop (𝓝 (l (w i))) := by
  classical
  have hfinite (s : Finset ι) : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i ∈ s, ∃ w : H i, ‖w‖ ≤ C i ∧ ∀ l : H i →L[ℝ] ℝ,
        Tendsto (fun k => l (v i (φ k))) atTop (𝓝 (l w)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨id, strictMono_id, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨φ, hφ, hold⟩ := ih
      obtain ⟨w, ψ, hw, hψ, hweak⟩ :=
        exists_weak_subsequence (fun k => v i (φ k)) (C i) (fun k => hbound i (φ k))
      refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨w, hw, hweak⟩
      · obtain ⟨z, hz, hlim⟩ := hold j hj
        exact ⟨z, hz, fun l => (hlim l).comp hψ.tendsto_atTop⟩
  obtain ⟨φ, hφ, hlim⟩ := hfinite Finset.univ
  choose w hw using fun i => hlim i (Finset.mem_univ i)
  exact ⟨φ, hφ, w, hw⟩

end PoincareConjecture.ReducedLengthMinimum.Variational
