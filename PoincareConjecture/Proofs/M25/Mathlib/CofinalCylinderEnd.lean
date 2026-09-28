import PoincareConjecture.Proofs.M25.Mathlib.CylinderTail
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.ProperSpace

set_option autoImplicit false

open Set Metric Topology

theorem Homeomorph.not_isBounded_image_of_isCompact_compl
    {W E : Type*} [TopologicalSpace W] [PseudoMetricSpace E]
    (Phi : W ≃ₜ E) (hunbounded : ¬ Bornology.IsBounded (univ : Set E))
    {s : Set W} (hs : IsCompact sᶜ) : ¬ Bornology.IsBounded (Phi '' s) := by
  intro hbounded
  apply hunbounded
  apply (hbounded.union (hs.image Phi.continuous).isBounded).subset
  intro z _
  by_cases hz : Phi.symm z ∈ s
  · exact Or.inl ⟨Phi.symm z, hz, Phi.apply_symm_apply z⟩
  · exact Or.inr ⟨Phi.symm z, hz, Phi.apply_symm_apply z⟩

theorem IsPreconnected.subset_compl_closedBall_of_unbounded
    {X : Type*} [PseudoMetricSpace X] {T : Set X} (hT : IsPreconnected T)
    (hunbounded : ¬ Bornology.IsBounded T) {z : X} {R : ℝ}
    (havoid : Disjoint T (sphere z R)) : T ⊆ (closedBall z R)ᶜ := by
  have hdisjoint : Disjoint (ball z R) (closedBall z R)ᶜ :=
    disjoint_left.mpr fun _ hx hy => hy (ball_subset_closedBall hx)
  have hcover : T ⊆ ball z R ∪ (closedBall z R)ᶜ := by
    intro x hx
    rcases lt_trichotomy (dist x z) R with h | h | h
    · exact Or.inl h
    · exact (disjoint_left.mp havoid hx h).elim
    · exact Or.inr (not_le.mpr h)
  rcases hT.subset_or_subset isOpen_ball isClosed_closedBall.isOpen_compl
    hdisjoint hcover with hinside | houtside
  · exact (hunbounded (isBounded_ball.subset hinside)).elim
  · exact houtside

namespace OpenPartialHomeomorph

variable {K W : Type*} [TopologicalSpace K] [TopologicalSpace W]

section Escape

variable [ConnectedSpace K] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] [ProperSpace E]
  (Phi : W ≃ₜ E) (e : OpenPartialHomeomorph (K × ℝ) W) {a b d : ℝ}
  (hsource : e.source = univ ×ˢ Ioo a b)
  (hcompact : ∀ d ∈ Ioo a b, IsCompact (e.cylinderTail b d)ᶜ)

include Phi hsource hcompact

theorem exists_cylinderTail_norm_gt_after (hd : d ∈ Ioo a b) (R : ℝ) :
    ∃ u ∈ Ioo d b, ∀ x ∈ e.cylinderTail b u, R < ‖Phi x‖ := by
  obtain ⟨L, hRL, hL⟩ := ((hcompact d hd).image Phi.continuous).isBounded
    |>.subset_ball_lt (max R 0) (0 : E)
  let Q : Set W := Phi.symm '' sphere (0 : E) L
  have hQ : IsCompact Q := (isCompact_sphere (0 : E) L).image Phi.symm.continuous
  have hQtail : Q ⊆ e.cylinderTail b d := by
    rintro x ⟨z, hz, rfl⟩
    by_contra hx
    have hzball : z ∈ ball (0 : E) L :=
      hL ⟨Phi.symm z, hx, Phi.apply_symm_apply z⟩
    exact (show ‖z‖ < L by simpa only [mem_ball, dist_zero_right] using hzball).ne
      (show ‖z‖ = L by simpa only [mem_sphere, dist_zero_right] using hz)
  obtain ⟨u, hu, hheight⟩ := e.exists_cylinder_height_lt_after hsource hQ
    (hQtail.trans (e.cylinderTail_subset_target hsource hd.1)) hd
  have huab : u ∈ Ioo a b := ⟨hd.1.trans hu.1, hu.2⟩
  have havoid : Disjoint (Phi '' e.cylinderTail b u) (sphere (0 : E) L) := by
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ hz
    have hxQ : x ∈ Q := ⟨Phi x, hz, Phi.symm_apply_apply x⟩
    exact (hheight x hxQ).not_gt ((e.mem_cylinderTail_iff hsource huab.1 x).mp hx).2.1
  have hconnected : IsConnected (Phi '' e.cylinderTail b u) :=
    (e.isConnected_cylinderTail hsource huab).image Phi Phi.continuous.continuousOn
  have hunbounded : ¬ Bornology.IsBounded (Phi '' e.cylinderTail b u) :=
    Phi.not_isBounded_image_of_isCompact_compl (NormedSpace.unbounded_univ ℝ E)
      (hcompact u huab)
  have houtside := hconnected.isPreconnected.subset_compl_closedBall_of_unbounded
    hunbounded havoid
  refine ⟨u, hu, fun x hx => ?_⟩
  have hLx : L < ‖Phi x‖ := by
    simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using
      houtside ⟨x, hx, rfl⟩
  exact ((le_max_left _ _).trans_lt hRL).trans hLx

theorem exists_cylinderTail_disjoint_compact_after
    {Q : Set W} (hQ : IsCompact Q) (hd : d ∈ Ioo a b) :
    ∃ u ∈ Ioo d b, Disjoint Q (e.cylinderTail b u) := by
  obtain ⟨R, hR⟩ := (hQ.image Phi.continuous).isBounded.exists_norm_le
  obtain ⟨u, hu, hescape⟩ := e.exists_cylinderTail_norm_gt_after
    Phi hsource hcompact hd R
  refine ⟨u, hu, disjoint_left.mpr ?_⟩
  intro x hxQ hxtail
  exact (hescape x hxtail).not_ge (hR (Phi x) ⟨x, hxQ, rfl⟩)

end Escape

section Frontier

variable [CompactSpace K] [T2Space W] [WeaklyLocallyCompactSpace W]
  (e : OpenPartialHomeomorph (K × ℝ) W) {a b d : ℝ}
  (hsource : e.source = univ ×ˢ Ioo a b)
  (hescape : ∀ Q : Set W, IsCompact Q → ∀ d ∈ Ioo a b,
    ∃ u ∈ Ioo d b, Disjoint Q (e.cylinderTail b u))

include hsource hescape

theorem closure_cylinderTail_subset_target_of_escape (hd : d ∈ Ioo a b) :
    closure (e.cylinderTail b d) ⊆ e.target := by
  intro x hx
  obtain ⟨Q, hQ, hxQ⟩ := exists_compact_mem_nhds x
  have hxint : x ∈ interior Q := mem_interior_iff_mem_nhds.mpr hxQ
  obtain ⟨u, hu, hdisjoint⟩ := hescape Q hQ d hd
  have hlate : Disjoint (closure (e.cylinderTail b u)) (interior Q) :=
    (hdisjoint.symm.mono_right interior_subset).closure_left isOpen_interior
  have hcover : closure (e.cylinderTail b d) ⊆
      e.cylinderSlab d u ∪ closure (e.cylinderTail b u) := by
    have h := closure_mono (e.cylinderTail_subset_slab_union_tail b d u)
    rw [closure_union, (e.isCompact_cylinderSlab hsource hd.1 hu.2).isClosed.closure_eq] at h
    exact h
  rcases hcover hx with hslab | htail
  · exact e.cylinderSlab_subset_target hsource hd.1 hu.2 hslab
  · exact (disjoint_left.mp hlate htail hxint).elim

theorem frontier_cylinderTail_eq_slice_of_escape (hd : d ∈ Ioo a b) :
    frontier (e.cylinderTail b d) = e.cylinderSlice d := by
  have hsubset : frontier (e.cylinderTail b d) ⊆ e.target :=
    frontier_subset_closure.trans
      (e.closure_cylinderTail_subset_target_of_escape hsource hescape hd)
  rw [← inter_eq_right.mpr hsubset]
  exact e.target_inter_frontier_cylinderTail hsource hd

theorem closure_cylinderTail_eq_union_slice_of_escape (hd : d ∈ Ioo a b) :
    closure (e.cylinderTail b d) = e.cylinderTail b d ∪ e.cylinderSlice d := by
  rw [closure_eq_interior_union_frontier,
    (e.isOpen_cylinderTail hsource hd.1).interior_eq,
    e.frontier_cylinderTail_eq_slice_of_escape hsource hescape hd]

end Frontier

end OpenPartialHomeomorph
