import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Level.Parametrization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Level.Separator
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Normalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Nesting

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)

private theorem plane_rank : 1 < Module.rank Real E2 := by
  rw [← Module.finrank_eq_rank]
  norm_num

theorem filledSection_subset_outer_disk
    (F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hF : F '' sphere (0 : E2) 1 = outerOval) :
    filledSection ⊆ F '' closedBall (0 : E2) 1 := by
  let K := F '' closedBall (0 : E2) 1
  have hK : IsCompact K := (isCompact_closedBall 0 1).image F.contMDiff.continuous
  have hc : IsConnected Kᶜ :=
    F.toHomeomorph.toOpenPartialHomeomorph.isConnected_compl_image_closedBall plane_rank
      (fun x _ => mem_univ x)
  have hu : ¬ Bornology.IsBounded Kᶜ := by
    intro hb
    apply NormedSpace.unbounded_univ Real E2
    simpa only [union_compl_self] using hK.isBounded.union hb
  have hm : (Kᶜ ∩ filledSectionᶜ).Nonempty := by
    by_contra hempty
    apply hu
    apply isCompact_filledSection.isBounded.subset
    intro q hq
    by_contra hq'
    exact hempty ⟨q, hq, hq'⟩
  have hsub : Kᶜ ⊆ filledSectionᶜ := by
    apply Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier
      isCompact_filledSection.isClosed.isOpen_compl hc.isPreconnected ?_ hm
    rw [frontier_compl]
    apply disjoint_left.mpr
    intro q hq hk
    exact hq (image_mono sphere_subset_closedBall
      (hF.symm ▸ frontier_filledSection_subset_outerOval hk))
  intro q hq
  by_contra hq'
  exact hsub hq' hq

theorem separator_closedBall_subset_outer_interior
    (F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hF : F '' sphere (0 : E2) 1 = outerOval) :
    closedBall (0 : E2) (79 / 100) ⊆ F '' ball (0 : E2) 1 := by
  intro q hq
  have hqK := filledSection_subset_outer_disk F hF (Or.inr hq)
  obtain ⟨p, hp, rfl⟩ := hqK
  refine ⟨p, ?_, rfl⟩
  have hpn := mem_closedBall_zero_iff.mp hp
  rw [mem_ball_zero_iff]
  by_contra hpn'
  have hpe : ‖p‖ = 1 := le_antisymm hpn (le_of_not_gt hpn')
  have hboundary : F p ∈ outerOval := hF ▸
    mem_image_of_mem F (mem_sphere_zero_iff_norm.mpr hpe)
  have hlo := norm_ge_of_mem_outerOval hboundary
  have hhi := mem_closedBall_zero_iff.mp hq
  linarith

theorem exists_nested_filled_disks :
    ∃ A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      A '' sphere (0 : E2) 1 = outerOval ∧
      B '' sphere (0 : E2) 1 = innerOval ∧
      closedBall (0 : E2) (79 / 100) ⊆ A '' ball (0 : E2) 1 ∧
      B '' closedBall (0 : E2) 1 ⊆ A '' ball (0 : E2) 1 := by
  obtain ⟨A, hA⟩ := exists_ambient_diffeomorph_of_smooth_circle
    outerCircle outerCircle_isSmoothEmbedding
  obtain ⟨B, hB⟩ := exists_ambient_diffeomorph_of_smooth_circle
    innerCircle innerCircle_isSmoothEmbedding
  rw [range_outerCircle] at hA
  rw [range_innerCircle] at hB
  have hseparator := separator_closedBall_subset_outer_interior A hA
  refine ⟨A, B, hA, hB, hseparator, ?_⟩
  apply A.toHomeomorph.image_closedBall_subset_image_ball_of_sphere_subset B.toHomeomorph plane_rank
  intro q hq
  exact hseparator (ball_subset_closedBall (innerOval_subset_separator_ball (hB ▸ hq)))

end Poincare.Manifold.Schoenflies.Saddle.Nested
