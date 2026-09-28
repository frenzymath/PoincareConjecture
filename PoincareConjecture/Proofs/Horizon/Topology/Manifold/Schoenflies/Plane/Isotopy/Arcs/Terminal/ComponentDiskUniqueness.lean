import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelCapDisks

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
private instance : LocallyConnectedSpace S2 := ChartedSpace.locallyConnectedSpace E2 S2

theorem closed_regions_eq_of_common_circle_and_exterior
    {C : S1 → S2} (hC : ContMDiff (𝓡 1) (𝓡 2) ∞ C)
    (hCi : Injective C) (hCd : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) C q))
    {K L : Set S2} (hK : IsClosed K) (hL : IsClosed L)
    (hfrontK : frontier K ⊆ range C) (hfrontL : frontier L ⊆ range C)
    (hneK : (interior K \ range C).Nonempty)
    (hneL : (interior L \ range C).Nonempty)
    (hout : ∃ q, q ∉ K ∧ q ∉ L) : K = L := by
  have hproper : K ∪ L ≠ univ := by
    intro heq
    obtain ⟨q, hqK, hqL⟩ := hout
    exact (heq.symm ▸ mem_univ q).elim hqK hqL
  have hfront : frontier (K ∪ L) ⊆ range C := by
    intro q hq
    rcases frontier_union_subset K L hq with hk | hl
    · exact hfrontK hk.1
    · exact hfrontL hl.2
  have hne : (interior (K ∪ L) \ range C).Nonempty :=
    hneK.mono (fun _ hx => ⟨interior_mono subset_union_left hx.1, hx.2⟩)
  obtain ⟨d, hs, _, _, hc, hb⟩ :=
    exists_disk_neighborhood_of_frontier_subset_circle hC hCi hCd
      (hK.union hL) hproper hfront hne
  have hdis : Disjoint (d '' ball (0 : E2) 1) (range C) := by
    apply disjoint_left.mpr
    rintro x ⟨u, hu, rfl⟩ hxC
    obtain ⟨v, hv, hvu⟩ := hb.symm ▸ hxC
    have heq := d.injOn (hs (sphere_subset_closedBall hv))
      (hs (ball_subset_closedBall hu)) hvu
    rw [heq, mem_sphere_zero_iff_norm] at hv
    have hlt := mem_ball_zero_iff.mp hu
    linarith
  have hconn : IsPreconnected (d '' ball (0 : E2) 1) :=
    isPreconnected_ball.image d (d.continuousOn.mono (ball_subset_closedBall.trans hs))
  have hfull (D : Set S2) (hD : IsClosed D) (hDU : D ⊆ K ∪ L)
      (hDf : frontier D ⊆ range C) (hDn : (interior D \ range C).Nonempty) :
      K ∪ L ⊆ D := by
    have hmeet : (d '' ball (0 : E2) 1 ∩ interior D).Nonempty := by
      obtain ⟨q, hqi, hqC⟩ := hDn
      obtain ⟨u, hu, rfl⟩ := hc.symm ▸ hDU (interior_subset hqi)
      refine ⟨d u, ⟨u, mem_ball_zero_iff.mpr ?_, rfl⟩, hqi⟩
      apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp hu)
      intro heq
      exact hqC (hb ▸ mem_image_of_mem d (mem_sphere_zero_iff_norm.mpr heq))
    have hin := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      hconn (hdis.mono_right hDf) hmeet
    rw [← hc, ← ParallelDisks.closure_image_ball zero_lt_one d hs]
    exact closure_minimal (hin.trans interior_subset) hD
  exact (subset_union_left.trans (hfull L hL subset_union_right hfrontL hneL)).antisymm
    (subset_union_right.trans (hfull K hK subset_union_left hfrontK hneK))

theorem sublevel_components_eq_of_common_circle_frontier
    {h : S2 → Real} (hh : Continuous h) {b : Real}
    {C : S1 → S2} (hC : ContMDiff (𝓡 1) (𝓡 2) ∞ C)
    (hCi : Injective C) (hCd : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) C q))
    (hlevel : ∀ q, h (C q) = b) (habove : ∃ q, b < h q)
    {p q : S2} (hp : h p < b) (hq : h q < b)
    (hfrontp : frontier (closure (connectedComponentIn (h ⁻¹' Iio b) p)) ⊆ range C)
    (hfrontq : frontier (closure (connectedComponentIn (h ⁻¹' Iio b) q)) ⊆ range C) :
    connectedComponentIn (h ⁻¹' Iio b) p = connectedComponentIn (h ⁻¹' Iio b) q ∧
      closure (connectedComponentIn (h ⁻¹' Iio b) p) =
        closure (connectedComponentIn (h ⁻¹' Iio b) q) := by
  let W (z : S2) := connectedComponentIn (h ⁻¹' Iio b) z
  have hopen (z : S2) : IsOpen (W z) := (isOpen_Iio.preimage hh).connectedComponentIn
  have hcl (z : S2) : closure (W z) ⊆ h ⁻¹' Iic b :=
    closure_minimal
      ((connectedComponentIn_subset _ _).trans (fun _ hx => le_of_lt (show h _ < b from hx)))
      (isClosed_Iic.preimage hh)
  have hne (z : S2) (hz : h z < b) : (interior (closure (W z)) \ range C).Nonempty := by
    refine ⟨z, (hopen z).subset_interior_iff.mpr subset_closure (mem_connectedComponentIn hz), ?_⟩
    rintro ⟨u, rfl⟩
    exact (ne_of_lt hz) (hlevel u)
  have heq : closure (W p) = closure (W q) := by
    apply closed_regions_eq_of_common_circle_and_exterior hC hCi hCd
      isClosed_closure isClosed_closure hfrontp hfrontq (hne p hp) (hne q hq)
    obtain ⟨z, hz⟩ := habove
    exact ⟨z, fun hzp => (not_le_of_gt hz) (hcl p hzp),
      fun hzq => (not_le_of_gt hz) (hcl q hzq)⟩
  have hpq : p ∈ W q := by
    have hpc : p ∈ closure (W q) := heq ▸ subset_closure (mem_connectedComponentIn hp)
    by_contra hn
    have hpf : p ∈ frontier (W q) := ⟨hpc, by simpa only [(hopen q).interior_eq] using hn⟩
    have hboundary := hh.frontier_preimage_subset _
      (Poincare.Topology.frontier_connectedComponentIn_subset_of_isOpen
        (isOpen_Iio.preimage hh) q hpf)
    have heqb : h p = b := by
      simpa only [frontier_Iio, mem_preimage, mem_singleton_iff] using hboundary
    exact (ne_of_lt hp) heqb
  exact ⟨(connectedComponentIn_eq hpq).symm, heq⟩

theorem disjoint_closures_of_disjoint_open_and_frontiers
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : Disjoint (frontier (closure U)) (frontier (closure V))) :
    Disjoint (closure U) (closure V) := by
  have hUi : Disjoint (interior (closure U)) (closure V) :=
    ((hUV.closure_left hV).mono_left interior_subset).closure_right isOpen_interior
  have hVi : Disjoint (interior (closure V)) (closure U) :=
    ((hUV.symm.closure_left hU).mono_left interior_subset).closure_right isOpen_interior
  apply disjoint_left.mpr
  intro x hxU hxV
  apply disjoint_left.mp hfront
  · exact ⟨by simpa only [closure_closure] using hxU,
      fun hxi => disjoint_left.mp hUi hxi hxV⟩
  · exact ⟨by simpa only [closure_closure] using hxV,
      fun hxi => disjoint_left.mp hVi hxi hxU⟩

theorem component_closures_disjoint_of_frontiers_disjoint
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {O : Set X} (hO : IsOpen O) {p q : X}
    (hne : connectedComponentIn O p ≠ connectedComponentIn O q)
    (hfront : Disjoint (frontier (closure (connectedComponentIn O p)))
      (frontier (closure (connectedComponentIn O q)))) :
    Disjoint (closure (connectedComponentIn O p)) (closure (connectedComponentIn O q)) := by
  apply disjoint_closures_of_disjoint_open_and_frontiers
    hO.connectedComponentIn hO.connectedComponentIn ?_ hfront
  apply disjoint_left.mpr
  intro x hxp hxq
  exact hne ((connectedComponentIn_eq hxp).trans (connectedComponentIn_eq hxq).symm)

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
