import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood











set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D



theorem open_eq_of_frontier_eq_of_common_exterior
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsPreconnected U) (hVne : V.Nonempty)
    (houter : IsPreconnected (closure U)ᶜ)
    (hfront : frontier U = frontier V) {z : X}
    (hzU : z ∉ closure U) (hzV : z ∉ closure V) : U = V := by
  have hVU : V ⊆ U := by
    intro x hx
    by_contra hxU
    have hxout : x ∈ (closure U)ᶜ := by
      intro hxcl
      have hxf : x ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hxcl, hxU⟩
      rw [hfront, hV.frontier_eq] at hxf
      exact hxf.2 hx
    have hOV : (closure U)ᶜ ⊆ V := by
      apply houter.subset_of_closure_inter_subset hV ⟨x, hxout, hx⟩
      rintro y ⟨hycl, hyout⟩
      by_contra hyV
      have hyf : y ∈ frontier V := by rw [hV.frontier_eq]; exact ⟨hycl, hyV⟩
      rw [← hfront] at hyf
      exact hyout (frontier_subset_closure hyf)
    exact hzV (subset_closure (hOV hzU))
  apply Subset.antisymm _ hVU
  apply hUc.subset_of_closure_inter_subset hV
  · obtain ⟨x, hx⟩ := hVne
    exact ⟨x, hVU hx, hx⟩
  · rintro x ⟨hxcl, hxU⟩
    by_contra hxV
    have hxf : x ∈ frontier V := by rw [hV.frontier_eq]; exact ⟨hxcl, hxV⟩
    rw [← hfront, hU.frontier_eq] at hxf
    exact hxf.2 hxU

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F]



theorem bounded_open_eq_of_frontier_eq {U V : Set F}
    (hU : IsOpen U) (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    (hUc : IsPreconnected U) (hVne : V.Nonempty)
    (houter : IsPreconnected (closure U)ᶜ)
    (hfront : frontier U = frontier V) : U = V := by
  have hb : Bornology.IsBounded (closure U ∪ closure V) := hUb.closure.union hVb.closure
  have hn : closure U ∪ closure V ≠ univ := by
    intro heq
    rw [heq] at hb
    exact NormedSpace.unbounded_univ ℝ F hb
  obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem _).mp hn
  exact open_eq_of_frontier_eq_of_common_exterior hU hV hUc hVne houter hfront
    (fun h => hz (Or.inl h)) (fun h => hz (Or.inr h))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]



theorem BallNeighborhoodChart.inside_eq_of_boundary_eq
    (B D : BallNeighborhoodChart E F) (hdim : 1 < Module.rank ℝ E)
    (hboundary : B.boundary = D.boundary) : B.inside = D.inside := by
  apply bounded_open_eq_of_frontier_eq B.inside_open D.inside_open
    B.inside_bounded D.inside_bounded B.inside_connected.isPreconnected
    D.inside_connected.nonempty
  · rw [B.closure_inside, ← B.inside_union_boundary, compl_eq_univ_sdiff]
    exact (B.outside_connected hdim).isPreconnected
  · rw [B.frontier_inside, D.frontier_inside, hboundary]



theorem BallNeighborhoodChart.closedRegion_eq_of_boundary_eq
    (B D : BallNeighborhoodChart E F) (hdim : 1 < Module.rank ℝ E)
    (hboundary : B.boundary = D.boundary) : B.closedRegion = D.closedRegion := by
  rw [← B.closure_inside, ← D.closure_inside,
    B.inside_eq_of_boundary_eq D hdim hboundary]



theorem compactChart_region_eq_of_boundary_eq
    {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    (e f : OpenPartialHomeomorph E X) (hdim : 1 < Module.rank ℝ E)
    (he : closedBall 0 1 ⊆ e.source) (hf : closedBall 0 1 ⊆ f.source)
    (hboundary : e '' sphere 0 1 = f '' sphere 0 1)
    {z : X} (hze : z ∉ e '' closedBall 0 1) (hzf : z ∉ f '' closedBall 0 1) :
    e '' closedBall 0 1 = f '' closedBall 0 1 := by
  have hcloseE := compactChart_closure_ball e 0 zero_lt_one he
  have hcloseF := compactChart_closure_ball f 0 zero_lt_one hf
  have hopenE := e.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans he)
  have hopenF := f.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hf)
  have hconn : IsPreconnected (e '' ball 0 1) :=
    isPreconnected_ball.image e (e.continuousOn.mono (ball_subset_closedBall.trans he))
  have hne : (f '' ball 0 1).Nonempty :=
    ⟨f 0, 0, mem_ball_self zero_lt_one, rfl⟩
  have houter : IsPreconnected (closure (e '' ball 0 1))ᶜ := by
    obtain ⟨d, hd, hds⟩ := (isCompact_closedBall (0 : E) 1).exists_thickening_subset_open
      e.open_source he
    rw [thickening_closedBall hd zero_le_one] at hds
    rw [hcloseE]
    exact (compactChart_exterior_connected e hdim (by linarith : 1 < d + 1) hds).isPreconnected
  have hfront : frontier (e '' ball 0 1) = frontier (f '' ball 0 1) := by
    rw [compactChart_frontier_ball e 0 zero_lt_one he,
      compactChart_frontier_ball f 0 zero_lt_one hf, hboundary]
  have hins := open_eq_of_frontier_eq_of_common_exterior hopenE hopenF hconn hne houter hfront
    (by simpa only [hcloseE] using hze) (by simpa only [hcloseF] using hzf)
  rw [← hcloseE, ← hcloseF, hins]

end PoincareConjecture.M25.Topology3D
