import PoincareConjecture.Proofs.M34.Mathlib.PartialImageTopology
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceRecutFrontier

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.CapCertificate

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem image_core_compact_and_interior (e : OpenPartialHomeomorph M X)
    (hsource : N.closed_core ⊆ e.source) :
    IsCompact (e '' N.closed_core) ∧ e '' N.core = interior (e '' N.closed_core) := by
  refine ⟨N.closed_core_compact.image_of_continuousOn (e.continuousOn.mono hsource), ?_⟩
  rw [N.core_eq_interior_closed_core]
  exact e.image_interior_eq_of_subset_source hsource

theorem image_core_frontier_eq [T2Space X] (e : OpenPartialHomeomorph M X)
    (hsource : N.closed_core ⊆ e.source) :
    frontier (e '' N.closed_core) = e '' N.boundary_sphere := by
  rw [← N.core_frontier_eq_boundary]
  symm
  apply e.image_frontier_eq_of_isCompact
  · simpa only [N.closed_core_compact.isClosed.closure_eq] using N.closed_core_compact
  · simpa only [N.closed_core_compact.isClosed.closure_eq] using hsource

theorem image_recut_complement_end_eq (e : OpenPartialHomeomorph M X) {b : ℝ}
    (hsource : N.recutCarrier b ⊆ e.source) :
    e '' N.closed_core = e '' N.recutCarrier b \
      e '' N.end_neck.region (-N.epsilon⁻¹) b := by
  have he : N.end_neck.region (-N.epsilon⁻¹) b ⊆ e.source :=
    fun _ hx => hsource (Or.inr hx)
  rw [← e.image_sdiff_eq_of_subset_source hsource he]
  congr 1
  ext x
  constructor
  · intro hx
    refine ⟨Or.inl hx, ?_⟩
    rw [N.closed_core_eq_complement_end] at hx
    exact fun h => hx.2 h.1
  · rintro ⟨hx, hnot⟩
    exact hx.resolve_right hnot

theorem image_boundary_eq_recut_end_frontier (e : OpenPartialHomeomorph M X)
    {b : ℝ} (hb : -N.epsilon⁻¹ < b) (hsource : N.recutCarrier b ⊆ e.source) :
    e '' N.boundary_sphere = e '' N.recutCarrier b ∩
      frontier (e '' N.end_neck.region (-N.epsilon⁻¹) b) := by
  rw [N.boundary_eq_recut_end_frontier hb]
  exact e.image_inter_frontier_eq_of_subset_source hsource (fun _ hx => hsource (Or.inr hx))

theorem image_boundary_subset_inner_end_closure (e : OpenPartialHomeomorph M X)
    {b c : ℝ} (hc : -N.epsilon⁻¹ < c) (hcb : c ≤ b)
    (hsource : N.recutCarrier b ⊆ e.source) :
    e '' N.boundary_sphere ⊆ closure (e '' N.end_neck.region (-N.epsilon⁻¹) c) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxs : x ∈ e.source := hsource (Or.inl (N.boundary_subset_closed_core hx))
  have hregion : N.end_neck.region (-N.epsilon⁻¹) c ⊆ e.source := by
    intro y hy
    exact hsource (Or.inr ⟨hy.1, hy.2.1, hy.2.2.trans_le hcb⟩)
  exact ((e.continuousOn x hxs).mono hregion).mem_closure_image
    (N.boundary_subset_inner_end_closure hc hx)

end PoincareConjecture.CapCertificate
