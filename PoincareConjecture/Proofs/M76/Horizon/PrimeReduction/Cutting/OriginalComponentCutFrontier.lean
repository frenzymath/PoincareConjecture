import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalDiskComponentProduct









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem component_cut_frontier
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier)
    (a : Bool → X) (ha : ∀ b, a b ∈ P.capDisk b) :
    let C := connectedComponentIn R (a false)
    IsCompact (C ∩ P.cutCarrier) ∧ PLDomain e (C ∩ P.cutCarrier) ∧
      frontier (C ∩ P.cutCarrier) = (frontier C \ P.openStrip) ∪ P.endDisks ∧
      ∀ b, connectedComponentIn (C ∩ P.cutCarrier) (a b) =
        connectedComponentIn P.cutCarrier (a b) := by
  let C := connectedComponentIn R (a false)
  obtain ⟨hQ, _, hfront, hattach, _, _⟩ := P.cut_geometry hR hopen
  have hcapQ (b : Bool) : P.capDisk b ⊆ P.cutCarrier := by
    intro x hx
    apply (hattach.symm.subset ?_).2
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  have haR : a false ∈ R := sdiff_subset (hcapQ false (ha false))
  have hC := isCompact_connectedComponentIn_of_mem hR haR
  have hrec : C =
      (connectedComponentIn P.cutCarrier (a false) ∪
        connectedComponentIn P.cutCarrier (a true)) ∪ P.closedStrip :=
    (P.component_reconstruction hR hopen hPL (ha false) (ha true)).1
  have hstripC : P.closedStrip ⊆ C := fun _ hx => hrec.symm.subset (Or.inr hx)
  have hendC : P.endDisks ⊆ C := P.endDisks_subset_closedStrip.trans hstripC
  have hendQ : P.endDisks ⊆ P.cutCarrier := fun x hx =>
    (hattach.symm.subset hx).2
  let : LocallyPathConnectedSpace R := he.locallyPathConnectedSpace
  obtain ⟨U, hU, hCU⟩ := exists_open_inter_of_relative_open
    (connectedComponentIn_subset R (a false)) (isOpen_preimage_connectedComponentIn haR)
  have hCf : frontier C = C ∩ frontier R :=
    frontier_eq_inter_of_eq_inter_open hR.isClosed hC.isClosed hU hCU
  have hCQ : IsCompact (C ∩ P.cutCarrier) := hC.inter_right hQ.isClosed
  have hCQU : C ∩ P.cutCarrier = P.cutCarrier ∩ U := by
    change connectedComponentIn R (a false) ∩ P.cutCarrier = _
    rw [hCU]
    ext x
    have hxR : x ∈ P.cutCarrier → x ∈ R := fun h => sdiff_subset h
    simp only [mem_inter_iff]
    tauto
  have hCQopen : IsOpen ((Subtype.val : P.cutCarrier → X) ⁻¹' (C ∩ P.cutCarrier)) := by
    rw [hCQU]
    have heq : (Subtype.val : P.cutCarrier → X) ⁻¹' (P.cutCarrier ∩ U) =
        (Subtype.val : P.cutCarrier → X) ⁻¹' U := by
      ext x
      exact and_iff_right x.property
    rw [heq]
    exact hU.preimage continuous_subtype_val
  have hCQPL : PLDomain e (C ∩ P.cutCarrier) :=
    hPL.of_relative_clopen_subset inter_subset_right hCQ.isClosed hCQopen
  have hCQf : frontier (C ∩ P.cutCarrier) = (C ∩ P.cutCarrier) ∩ frontier P.cutCarrier :=
    frontier_eq_inter_of_eq_inter_open hQ.isClosed hCQ.isClosed hU hCQU
  refine ⟨hCQ, hCQPL, ?_, ?_⟩
  · rw [hCQf, hfront, hCf]
    ext x
    constructor
    · rintro ⟨⟨hxC, _⟩, hx | hx⟩
      · exact Or.inl ⟨⟨hxC, hx.1⟩, hx.2⟩
      · exact Or.inr hx
    · rintro (⟨⟨hxC, hxf⟩, hxo⟩ | hx)
      · exact ⟨⟨hxC, ⟨hR.isClosed.frontier_subset hxf, hxo⟩⟩, Or.inl ⟨hxf, hxo⟩⟩
      · exact ⟨⟨hendC hx, hendQ hx⟩, Or.inr hx⟩
  · intro b
    apply Subset.antisymm
    · exact connectedComponentIn_mono _ inter_subset_right
    · have hDC : connectedComponentIn P.cutCarrier (a b) ⊆ C := by
        rw [hrec]
        cases b
        · exact subset_union_of_subset_left subset_union_left _
        · exact subset_union_of_subset_left subset_union_right _
      exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn (hcapQ b (ha b)))
        (subset_inter hDC (connectedComponentIn_subset _ _))

end PoincareConjecture.M76.OriginalDiskProduct
