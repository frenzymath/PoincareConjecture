import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BallImages
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Connected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false

open Set Metric

namespace OpenPartialHomeomorph

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [ProperSpace E]
  [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [LocallyConnectedSpace M]

theorem isConnected_compl_image_closedBall
    (e : OpenPartialHomeomorph E M) (hdim : 1 < Module.rank Real E)
    (hs : closedBall (0 : E) 1 ⊆ e.source) :
    IsConnected (e '' closedBall (0 : E) 1)ᶜ := by
  obtain ⟨d, hd, hds⟩ := (isCompact_closedBall (0 : E) 1).exists_thickening_subset_open
    e.open_source hs
  rw [thickening_closedBall hd zero_le_one] at hds
  let R := d + 1
  have hR : 1 < R := by dsimp [R]; linarith
  let K := e '' closedBall (0 : E) 1
  let U := e '' ball (0 : E) R
  have hKc : IsCompact K := (isCompact_closedBall 0 1).image_of_continuousOn
    (e.continuousOn.mono hs)
  have hUo : IsOpen U := e.isOpen_image_of_subset_source isOpen_ball hds
  have hradial : (fun p : Real × E => p.1 • p.2) ''
      (Ioo 1 R ×ˢ sphere (0 : E) 1) = {x : E | 1 < ‖x‖ ∧ ‖x‖ < R} := by
    ext x
    constructor
    · rintro ⟨⟨t, v⟩, ⟨ht, hv⟩, rfl⟩
      simpa only [mem_ofPred_eq, mem_Ioo, norm_smul, Real.norm_eq_abs,
        abs_of_pos (zero_lt_one.trans ht.1), mem_sphere_zero_iff_norm.mp hv,
        mul_one] using ht
    · intro hx
      have hx0 : ‖x‖ ≠ 0 := ne_of_gt (zero_lt_one.trans hx.1)
      refine ⟨(‖x‖, ‖x‖⁻¹ • x), ⟨hx, ?_⟩, ?_⟩
      · simp [norm_smul, inv_mul_cancel₀ hx0]
      · simp [smul_smul, mul_inv_cancel₀ hx0]
  have hann : IsConnected {x : E | 1 < ‖x‖ ∧ ‖x‖ < R} := by
    rw [← hradial]
    exact ((isConnected_Ioo hR).prod (isConnected_sphere hdim 0 zero_le_one)).image
      _ (by fun_prop)
  have houter : Kᶜ ∩ U = e '' {x : E | 1 < ‖x‖ ∧ ‖x‖ < R} := by
    ext y
    constructor
    · rintro ⟨hyK, x, hx, rfl⟩
      refine ⟨x, ⟨?_, by simpa only [mem_ball_zero_iff] using hx⟩, rfl⟩
      by_contra hxle
      exact hyK ⟨x, mem_closedBall_zero_iff.mpr (le_of_not_gt hxle), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hxR : x ∈ ball (0 : E) R := mem_ball_zero_iff.mpr hx.2
      refine ⟨?_, x, hxR, rfl⟩
      rintro ⟨z, hz, heq⟩
      have hzx : z = x := e.injOn (hs hz) (hds hxR) heq
      exact (not_le_of_gt hx.1) (mem_closedBall_zero_iff.mp (hzx ▸ hz))
  apply Poincare.Topology.isConnected_of_inter_of_frontier_subset
    hKc.isClosed.isOpen_compl hUo
  · rw [houter]
    exact hann.image e (e.continuousOn.mono (fun x hx => hds (mem_ball_zero_iff.mpr hx.2)))
  · rw [frontier_compl, ← e.image_sphere_eq_frontier hs (rfl : e '' closedBall 0 1 = K)]
    exact image_mono (sphere_subset_closedBall.trans (closedBall_subset_ball hR))
  · intro h
    have hzero : e 0 ∈ K := ⟨0, mem_closedBall_self zero_le_one, rfl⟩
    have hnot : e 0 ∈ Kᶜ := h.symm ▸ mem_univ (e 0)
    exact hnot hzero

end OpenPartialHomeomorph
