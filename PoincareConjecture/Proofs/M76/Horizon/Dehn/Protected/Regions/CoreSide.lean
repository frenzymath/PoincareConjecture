import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.RelativeInterior









set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.Dehn

theorem product_core_subset_closure_of_frontier_patch
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set (E × F)} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hU : IsOpen U) (hUR : U ⊆ closedBall (0 : E) a ×ˢ (univ : Set F))
    (hdis : Disjoint (frontier U) (ball (0 : E) a ×ˢ ball (0 : F) b))
    (hmeet : (frontier U ∩ ((univ : Set E) ×ˢ ball (0 : F) b)).Nonempty) :
    closedBall (0 : E) a ×ˢ closedBall (0 : F) b ⊆ closure U := by
  have hUI : U ⊆ ball (0 : E) a ×ˢ (univ : Set F) := by
    have hi := interior_maximal hUR hU
    simpa only [interior_prod_eq, interior_closedBall _ ha.ne', interior_univ] using hi
  obtain ⟨q, hq, hqV⟩ := hmeet
  obtain ⟨x, hxV, hxU⟩ := _root_.mem_closure_iff.mp (frontier_subset_closure hq) _
    (isOpen_univ.prod isOpen_ball) hqV
  have hconn : IsPreconnected (ball (0 : E) a ×ˢ ball (0 : F) b) :=
    ((convex_ball (0 : E) a).prod (convex_ball (0 : F) b)).isPreconnected
  have hsub := hconn.m76_subset_of_disjoint_frontier hU hdis
    ⟨x, ⟨(hUI hxU).1, hxV.2⟩, hxU⟩
  have hclosed := closure_mono hsub
  simpa only [closure_prod_eq, closure_ball _ ha.ne', closure_ball _ hb.ne'] using hclosed

theorem product_core_relative_interior_of_frontier_decomposition
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set (E × F)} {a b c : ℝ} (ha : 0 < a)
    (hU : IsOpen U) (hUR : U ⊆ closedBall (0 : E) a ×ˢ (univ : Set F))
    (hK : IsClosed K)
    (hdis : Disjoint K (closedBall (0 : E) a ×ˢ closedBall (0 : F) b))
    (hfront : frontier U = K ∪ (sphere (0 : E) a ×ˢ closedBall (0 : F) c))
    (hcore : closedBall (0 : E) a ×ˢ closedBall (0 : F) b ⊆ closure U) :
    (Subtype.val : (closedBall (0 : E) a ×ˢ (univ : Set F)) → E × F) ⁻¹'
      (closedBall (0 : E) a ×ˢ closedBall (0 : F) b) ⊆
      interior (Subtype.val ⁻¹' closure U) := by
  intro q hq
  apply mem_relative_interior_closure_of_frontier_patch
    (isClosed_closedBall.prod isClosed_univ)
    ((convex_closedBall (0 : E) a).prod convex_univ)
    (by
      rw [interior_prod_eq, interior_closedBall _ ha.ne', interior_univ]
      exact ⟨(0, 0), mem_ball_self ha, mem_univ _⟩)
    hU hUR hK.isOpen_compl
    (Set.disjoint_right.mp hdis hq) (hcore hq)
  intro x hx
  have hside : x ∈ sphere (0 : E) a ×ˢ closedBall (0 : F) c :=
    (hfront.subset hx.1).resolve_left hx.2
  simpa only [frontier_prod_eq, frontier_univ, closure_univ,
    frontier_closedBall _ ha.ne', prod_empty, empty_union] using
      (show x ∈ sphere (0 : E) a ×ˢ (univ : Set F) from ⟨hside.1, mem_univ _⟩)

theorem closure_old_boundary_of_frontier_trace
    {E : Type*} [TopologicalSpace E] {U R A : Set E}
    (hU : IsOpen U) (hUR : U ⊆ R)
    (htrace : frontier U ∩ frontier R = A) :
    closure U ∩ frontier R = A := by
  rw [← htrace]
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨?_, hx.2⟩
    rw [hU.frontier_eq]
    exact ⟨hx.1, fun hxU ↦ hx.2.2 (interior_maximal hUR hU hxU)⟩
  · exact inter_subset_inter_left _ frontier_subset_closure

end PoincareConjecture.M76.Dehn
