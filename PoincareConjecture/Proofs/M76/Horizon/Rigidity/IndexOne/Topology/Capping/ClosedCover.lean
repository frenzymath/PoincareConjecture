import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.Capping.Motion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Gluing.ClosedCoverInjection

set_option autoImplicit false
open Set BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem simplyConnectedSpace_of_closed_cover_capping
    {X : Type*} [MetricSpace X] {N M : Set X}
    (hN : IsClosed N) (hM : IsClosed M) (hcover : N ∪ M = univ)
    (hcompact : IsCompact (N ∩ M))
    (hNp : IsPathConnected N) (hMs : IsSimplyConnected M)
    (hWp : IsPathConnected (N ∩ M)) (b : ↥(N ∩ M))
    (hgenerate : Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (inter_subset_left : N ∩ M ⊆ N)) b))
    (hlocalN : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) N,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_left a)
    (hlocalM : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) M,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_right a) :
    SimplyConnectedSpace X := by
  obtain ⟨hfront, hother, ⟨C⟩⟩ := nonempty_openFrontierCollapse_of_closed_cover_local_collars
    hN hM hcover hcompact ⟨b, b.property⟩ hlocalN hlocalM
  have hFW : N ∩ M ⊆ C.overlap := hfront ▸ C.frontier_subset
  have hMP : M ⊆ C.negative := hother.symm ▸ C.negative_subset
  have hneg : C.negative = M ∪ C.overlap := by rw [hother]; exact C.negative_eq
  have hmoveM : ∀ t, MapsTo (fun x => C.motion (t, x)) M M :=
    hother.symm ▸ C.motion_negative
  have hmoveF : ∀ t, MapsTo (fun x => C.motion (t, x)) (N ∩ M) (N ∩ M) :=
    fun t x hx => ⟨C.motion_positive t hx.1, hmoveM t hx.2⟩
  have hendW : MapsTo (fun x => C.motion (1, x)) C.overlap (N ∩ M) :=
    fun x hx => hfront ▸ C.endpoint_overlap hx
  have hmoveP : ∀ t, MapsTo (fun x => C.motion (t, x)) C.positive C.positive := by
    intro t x hx
    rw [C.positive_eq] at hx ⊢
    exact hx.elim (fun h => Or.inl (C.motion_positive t h))
      (fun h => Or.inr (C.motion_overlap t h))
  have hmoveQ : ∀ t, MapsTo (fun x => C.motion (t, x)) C.negative C.negative := by
    intro t x hx
    rw [hneg] at hx ⊢
    exact hx.elim (fun h => Or.inl (hmoveM t h))
      (fun h => Or.inr (C.motion_overlap t h))
  have hendP : MapsTo (fun x => C.motion (1, x)) C.positive N := by
    intro x hx
    rw [C.positive_eq] at hx
    exact hx.elim (fun h => C.motion_positive 1 h) (fun h => (hendW h).1)
  have hendQ : MapsTo (fun x => C.motion (1, x)) C.negative M := by
    intro x hx
    rw [hneg] at hx
    exact hx.elim (fun h => hmoveM 1 h) (fun h => (hendW h).2)
  obtain ⟨EP, hEP⟩ := exists_inclusion_homotopyEquiv_of_motion C.positive_subset
    C.motion C.motion_zero C.motion_positive hmoveP hendP
  obtain ⟨EQ, _⟩ := exists_inclusion_homotopyEquiv_of_motion hMP
    C.motion C.motion_zero hmoveM hmoveQ hendQ
  obtain ⟨EW, _⟩ := exists_inclusion_homotopyEquiv_of_motion hFW
    C.motion C.motion_zero hmoveF C.motion_overlap hendW
  have hPp : IsPathConnected C.positive := by
    let : PathConnectedSpace N := isPathConnected_iff_pathConnectedSpace.mp hNp
    exact isPathConnected_iff_pathConnectedSpace.mpr (pathConnectedSpace_of_homotopyEquiv EP)
  have hQs : IsSimplyConnected C.negative := by
    let : SimplyConnectedSpace M := hMs
    exact EQ.symm.simplyConnectedSpace
  have hWopen : IsPathConnected C.overlap := by
    let : PathConnectedSpace ↥(N ∩ M) := isPathConnected_iff_pathConnectedSpace.mp hWp
    exact isPathConnected_iff_pathConnectedSpace.mpr (pathConnectedSpace_of_homotopyEquiv EW)
  have hFI : N ∩ M ⊆ C.positive ∩ C.negative := by
    rw [C.inter_eq]
    exact hFW
  let bI : ↥(C.positive ∩ C.negative) := ⟨b, hFI b.property⟩
  have hgen : Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (inter_subset_left : C.positive ∩ C.negative ⊆ C.positive)) bI) := by
    have hsurj := (FundamentalGroup.map_bijective_of_homotopyEquiv EP
      (⟨b, b.property.1⟩ : N)).2
    rw [hEP] at hsurj
    intro a
    obtain ⟨c, hc⟩ := hsurj a
    obtain ⟨d, hd⟩ := hgenerate c
    refine ⟨FundamentalGroup.map (ContinuousMap.inclusion hFI) b d, ?_⟩
    change FundamentalGroup.map
      (ContinuousMap.inclusion (inter_subset_left : C.positive ∩ C.negative ⊆ C.positive))
      (ContinuousMap.inclusion hFI b) (FundamentalGroup.map (ContinuousMap.inclusion hFI) b d) = a
    rw [← FundamentalGroup.map_comp_apply]
    change FundamentalGroup.map ((ContinuousMap.inclusion C.positive_subset).comp
      (ContinuousMap.inclusion (inter_subset_left : N ∩ M ⊆ N))) b d = a
    rw [FundamentalGroup.map_comp_apply, hd]
    exact hc
  exact simplyConnectedSpace_of_open_cover_capping C.positive C.negative
    C.positive_open C.negative_open C.cover hPp hQs
    (C.inter_eq.symm ▸ hWopen) bI hgen

end PoincareConjecture.M76.HamiltonIntervalTorus
