import PoincareConjecture.Proofs.M59.Mathlib.PathClassTopology
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false

open Set Metric
open scoped unitInterval Topology

universe u v

namespace LocallySimplyConnectedSpace

instance of_normedSpace {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    LocallySimplyConnectedSpace E where
  exists_open_simplyConnected x U hx hU := by
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
    have : ContractibleSpace (ball x r) :=
      (convex_ball x r).contractibleSpace ⟨x, mem_ball_self hr⟩
    exact ⟨ball x r, isOpen_ball, (inferInstance : SimplyConnectedSpace (ball x r)),
      mem_ball_self hr, hsub⟩

theorem of_convex {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : Convex ℝ s) : LocallySimplyConnectedSpace s where
  exists_open_simplyConnected x U hx hU := by
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
    have : ContractibleSpace ↥(ball (x : E) r ∩ s) :=
      ((convex_ball (x : E) r).inter hs).contractibleSpace ⟨x, mem_ball_self hr, x.2⟩
    have him : IsSimplyConnected (Subtype.val '' ball x r : Set E) := by
      rw [Subtype.image_ball]
      exact (inferInstance : SimplyConnectedSpace ↥(ball (x : E) r ∩ s))
    have hsc := Topology.IsEmbedding.subtypeVal.isSimplyConnected_image.mp him
    exact ⟨ball x r, isOpen_ball, hsc, mem_ball_self hr, hsub⟩

instance unitInterval : LocallySimplyConnectedSpace I :=
  of_convex (convex_Icc (0 : ℝ) 1)

theorem exists_of_openPartialHomeomorph
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallySimplyConnectedSpace Y] (e : OpenPartialHomeomorph X Y)
    {x : X} (hx : x ∈ e.source) {U : Set X} (hxU : x ∈ U) (hU : IsOpen U) :
    ∃ W : Set X, IsOpen W ∧ IsSimplyConnected W ∧ x ∈ W ∧ W ⊆ U := by
  obtain ⟨V, hV, hscV, hxV, hsub⟩ := exists_open_simplyConnected (e x)
    (e.target ∩ e.symm ⁻¹' U)
    ⟨e.map_source hx, by change e.symm (e x) ∈ U; simpa only [e.left_inv hx]⟩
    (e.isOpen_inter_preimage_symm hU)
  have htarget : V ⊆ e.target := hsub.trans inter_subset_left
  have he : e '' (e.source ∩ e ⁻¹' V) = V := by
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · intro y hy
      exact ⟨e.symm y, ⟨e.map_target (htarget hy),
        by change e (e.symm y) ∈ V; simpa only [e.right_inv (htarget hy)]⟩,
        e.right_inv (htarget hy)⟩
  have : SimplyConnectedSpace V := hscV
  have hsc : IsSimplyConnected (e.source ∩ e ⁻¹' V) :=
    (e.homeomorphOfImageSubsetSource inter_subset_left he).toHomotopyEquiv.simplyConnectedSpace
  refine ⟨e.source ∩ e ⁻¹' V, e.isOpen_inter_preimage hV, hsc, ⟨hx, hxV⟩, ?_⟩
  intro y hy
  have h := (hsub hy.2).2
  change e.symm (e y) ∈ U at h
  simpa only [e.left_inv hy.1] using h

end LocallySimplyConnectedSpace

theorem ChartedSpace.locallySimplyConnectedSpace
    (H : Type u) [TopologicalSpace H] [LocallySimplyConnectedSpace H]
    (M : Type v) [TopologicalSpace M] [ChartedSpace H M] : LocallySimplyConnectedSpace M where
  exists_open_simplyConnected x _U hx hU :=
    LocallySimplyConnectedSpace.exists_of_openPartialHomeomorph (chartAt H x)
      (mem_chart_source H x) hx hU
