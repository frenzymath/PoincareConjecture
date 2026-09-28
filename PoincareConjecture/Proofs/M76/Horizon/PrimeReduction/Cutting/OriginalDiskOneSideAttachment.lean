import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalComponentCutFrontier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalStripPuncturedModel
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall










set_option autoImplicit false
open Set Metric Geometry

namespace Set

theorem frontier_of_closed_union_complement
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsClosed U) (hV : IsClosed V) (hVreg : closure (interior V) = V)
    (hdis : Disjoint U (interior V)) :
    frontier U = (frontier (U ∪ V) ∩ U) ∪ (U ∩ V) := by
  have hdis' : Disjoint (interior U) V := by
    rw [← hVreg]
    exact (hdis.mono_left interior_subset).closure_right isOpen_interior
  have hlocal : interior (U ∪ V) ∩ Vᶜ ⊆ interior U := by
    apply (isOpen_interior.inter hV.isOpen_compl).subset_interior_iff.mpr
    rintro x ⟨hx, hxV⟩
    exact (interior_subset hx).resolve_right hxV
  rw [hU.frontier_eq, (hU.union hV).frontier_eq]
  apply Subset.antisymm
  · intro x hx
    by_cases hxV : x ∈ V
    · exact Or.inr ⟨hx.1, hxV⟩
    · exact Or.inl ⟨⟨Or.inl hx.1, fun hi => hx.2 (hlocal ⟨hi, hxV⟩)⟩, hx.1⟩
  · rintro x (⟨⟨_, hxint⟩, hxU⟩ | ⟨hxU, hxV⟩)
    · exact ⟨hxU, fun hi => hxint (interior_mono subset_union_left hi)⟩
    · exact ⟨hxU, fun hi => disjoint_left.mp hdis' hi hxV⟩

end Set

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem one_side_attachment_frontier
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) (a : Bool → X) (ha : ∀ b, a b ∈ P.capDisk b)
    (hdis : Disjoint (connectedComponentIn P.cutCarrier (a false))
      (connectedComponentIn P.cutCarrier (a true))) :
    let D := fun b => connectedComponentIn P.cutCarrier (a b)
    let C := connectedComponentIn R (a false)
    ∀ b, (D b ∪ P.closedStrip) ∩ D (!b) = P.capDisk (!b) ∧
      IsCompact (D b ∪ P.closedStrip) ∧
      frontier (D b ∪ P.closedStrip) =
        (frontier C ∩ (D b ∪ P.closedStrip)) ∪ P.capDisk (!b) := by
  let D := fun b => connectedComponentIn P.cutCarrier (a b)
  let C := connectedComponentIn R (a false)
  obtain ⟨hQ, _, hQf, hattach, _, _⟩ := P.cut_geometry hR hopen
  have hcapQ (b : Bool) : P.capDisk b ⊆ P.cutCarrier := by
    intro x hx
    apply (hattach.symm.subset ?_).2
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  have hacut (b : Bool) := hcapQ b (ha b)
  have hDc (b : Bool) : IsCompact (D b) := isCompact_connectedComponentIn_of_mem hQ (hacut b)
  have hDPL (b : Bool) : PLDomain e (D b) := hPL.connectedComponentIn hQ (hacut b)
  have hcapD (b : Bool) : P.capDisk b ⊆ D b :=
    (P.isConnected_capDisk b).isPreconnected.subset_connectedComponentIn (ha b) (hcapQ b)
  have hcapstrip (b : Bool) : P.capDisk b ⊆ P.closedStrip := by
    apply subset_trans _ P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hDf (b : Bool) : frontier (D b) = D b ∩ frontier P.cutCarrier := by
    let : LocallyPathConnectedSpace P.cutCarrier := hPL.locallyPathConnectedSpace
    obtain ⟨U, hU, hDU⟩ := exists_open_inter_of_relative_open
      (connectedComponentIn_subset P.cutCarrier (a b))
      (isOpen_preimage_connectedComponentIn (hacut b))
    exact frontier_eq_inter_of_eq_inter_open hQ.isClosed (hDc b).isClosed hU hDU
  have hcapDf (b : Bool) : P.capDisk b ⊆ frontier (D b) := by
    rw [hDf, hQf]
    intro x hx
    refine ⟨hcapD b hx, Or.inr ?_⟩
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  have hDdis (b : Bool) : Disjoint (D b) (D (!b)) := by
    cases b
    · exact hdis
    · exact hdis.symm
  have hstripD (b : Bool) : P.closedStrip ∩ D b = P.capDisk b := by
    apply Subset.antisymm
    · rintro x ⟨hxstrip, hxD⟩
      have hend := hattach.subset ⟨hxstrip, connectedComponentIn_subset _ _ hxD⟩
      rw [P.endDisks_eq_capDisks] at hend
      cases b
      · exact hend.resolve_right (fun hc => disjoint_left.mp hdis hxD (hcapD true hc))
      · exact hend.resolve_left (fun hc => disjoint_left.mp hdis (hcapD false hc) hxD)
    · intro x hx
      exact ⟨hcapstrip b hx, hcapD b hx⟩
  have hrec : C = (D false ∪ D true) ∪ P.closedStrip :=
    (P.component_reconstruction hR hopen hPL (ha false) (ha true)).1
  change ∀ b, (D b ∪ P.closedStrip) ∩ D (!b) = P.capDisk (!b) ∧
    IsCompact (D b ∪ P.closedStrip) ∧ frontier (D b ∪ P.closedStrip) =
      (frontier C ∩ (D b ∪ P.closedStrip)) ∪ P.capDisk (!b)
  intro b
  have hcontact : (D b ∪ P.closedStrip) ∩ D (!b) = P.capDisk (!b) := by
    rw [union_inter_distrib_right, (hDdis b).inter_eq, empty_union, hstripD]
  have hUc : IsCompact (D b ∪ P.closedStrip) :=
    (hDc b).union (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hcover : (D b ∪ P.closedStrip) ∪ D (!b) = C := by
    rw [hrec]
    cases b <;> simp only [Bool.not_false, Bool.not_true] <;> ext x <;>
      simp only [mem_union] <;> tauto
  have hintdis : Disjoint (D b ∪ P.closedStrip) (interior (D (!b))) := by
    apply disjoint_left.mpr
    intro x hxU hxint
    have hxcap := hcontact.subset ⟨hxU, interior_subset hxint⟩
    exact (hcapDf (!b) hxcap).2 hxint
  refine ⟨hcontact, hUc, ?_⟩
  rw [frontier_of_closed_union_complement hUc.isClosed (hDc (!b)).isClosed
    (hDPL (!b)).closure_interior hintdis, hcover, hcontact]

theorem one_side_disk_port_geometry
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) (a : Bool → X) (ha : ∀ b, a b ∈ P.capDisk b)
    (hdis : Disjoint (connectedComponentIn P.cutCarrier (a false))
      (connectedComponentIn P.cutCarrier (a true))) :
    let D := fun b => connectedComponentIn P.cutCarrier (a b)
    ∀ b, D b ∩ P.closedStrip = P.capDisk b ∧
      frontier (D b ∪ P.closedStrip) =
        (frontier (D b) \ (P.capDisk b \ P.capRimSet b)) ∪
        (frontier P.closedStrip \ (P.capDisk b \ P.capRimSet b)) := by
  let D := fun b => connectedComponentIn P.cutCarrier (a b)
  let C := connectedComponentIn R (a false)
  let band := P.map '' (sphere (0 : V2) 1 ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2))
  obtain ⟨hQ, _, hQf, hattach, _, _⟩ := P.cut_geometry hR hopen
  have hcapQ (b : Bool) : P.capDisk b ⊆ P.cutCarrier := by
    intro x hx
    apply (hattach.symm.subset ?_).2
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  have hacut (b : Bool) := hcapQ b (ha b)
  have hcapD (b : Bool) : P.capDisk b ⊆ D b :=
    (P.isConnected_capDisk b).isPreconnected.subset_connectedComponentIn (ha b) (hcapQ b)
  have hDdis (b : Bool) : Disjoint (D b) (D (!b)) := by
    cases b
    · exact hdis
    · exact hdis.symm
  have hcapstrip (b : Bool) : P.capDisk b ⊆ P.closedStrip := by
    apply subset_trans _ P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have haR : a false ∈ R := sdiff_subset (hacut false)
  have hCc : IsCompact C := isCompact_connectedComponentIn_of_mem hR haR
  have hCf : frontier C = C ∩ frontier R := by
    let : LocallyPathConnectedSpace R := he.locallyPathConnectedSpace
    obtain ⟨U, hU, hCU⟩ := exists_open_inter_of_relative_open
      (connectedComponentIn_subset R (a false)) (isOpen_preimage_connectedComponentIn haR)
    exact frontier_eq_inter_of_eq_inter_open hR.isClosed hCc.isClosed hU hCU
  have hrec : C = (D false ∪ D true) ∪ P.closedStrip :=
    (P.component_reconstruction hR hopen hPL (ha false) (ha true)).1
  have hDf (b : Bool) : frontier (D b) = (D b ∩ frontier R) ∪ P.capDisk b := by
    let : LocallyPathConnectedSpace P.cutCarrier := hPL.locallyPathConnectedSpace
    obtain ⟨U, hU, hDU⟩ := exists_open_inter_of_relative_open
      (connectedComponentIn_subset P.cutCarrier (a b))
      (isOpen_preimage_connectedComponentIn (hacut b))
    have hf : frontier (D b) = D b ∩ frontier P.cutCarrier :=
      frontier_eq_inter_of_eq_inter_open hQ.isClosed
        (isCompact_connectedComponentIn_of_mem hQ (hacut b)).isClosed hU hDU
    rw [hf, hQf, P.endDisks_eq_capDisks]
    ext x
    have hnotopen : x ∈ D b → x ∉ P.openStrip :=
      fun hx => (connectedComponentIn_subset _ _ hx).2
    have hown : x ∈ P.capDisk b → x ∈ D b := fun hx => hcapD b hx
    have hother : x ∈ D b → x ∉ P.capDisk (!b) :=
      fun hx hc => disjoint_left.mp (hDdis b) hx (hcapD (!b) hc)
    cases b <;>
      simp only [Bool.not_false, Bool.not_true, mem_inter_iff, mem_union, mem_sdiff] at * <;> tauto
  change ∀ b, D b ∩ P.closedStrip = P.capDisk b ∧ _
  intro b
  have hmain := P.one_side_attachment_frontier hR hopen hPL a ha hdis b
  have hcontact : D b ∩ P.closedStrip = P.capDisk b := by
    have h := (P.one_side_attachment_frontier hR hopen hPL a ha hdis (!b)).1
    simp only [Bool.not_not] at h
    change (D (!b) ∪ P.closedStrip) ∩ D b = P.capDisk b at h
    have hdb : Disjoint (D (!b)) (D b) := by
      simpa only [Bool.not_not] using hDdis (!b)
    rw [union_inter_distrib_right, hdb.inter_eq, empty_union] at h
    exact (inter_comm _ _).trans h
  have hUcC : D b ∪ P.closedStrip ⊆ C := by
    rw [hrec]
    apply union_subset _ subset_union_right
    cases b
    · exact subset_union_of_subset_left subset_union_left _
    · exact subset_union_of_subset_left subset_union_right _
  have hUf : frontier (D b ∪ P.closedStrip) =
      ((D b ∩ frontier R) ∪ band) ∪ P.capDisk (!b) := by
    rw [hmain.2.2, hCf]
    have hbi : band = P.closedStrip ∩ frontier R := P.closedStrip_inter_frontier.symm
    rw [hbi]
    ext x
    have hu : x ∈ D b ∪ P.closedStrip → x ∈ C := fun hx => hUcC hx
    simp only [mem_union, mem_inter_iff] at *
    tauto
  have hSf : frontier P.closedStrip = band ∪ (P.capDisk b ∪ P.capDisk (!b)) := by
    rw [P.frontier_closedStrip, P.endDisks_eq_capDisks]
    cases b <;> simp [band, union_comm]
  refine ⟨hcontact, ?_⟩
  rw [hUf, hDf, hSf]
  ext x
  have hold : x ∈ frontier R → x ∈ P.capDisk b → x ∈ P.capRimSet b :=
    fun hf hc => (P.capDisk_inter_frontier b).subset ⟨hc, hf⟩
  have hbandold : x ∈ band → x ∈ frontier R :=
    fun hx => (P.closedStrip_inter_frontier.symm.subset hx).2
  have hrimband : x ∈ P.capRimSet b → x ∈ band := by
    intro hx
    have h := (P.capDisk_inter_frontier b).symm.subset hx
    exact P.closedStrip_inter_frontier.subset ⟨hcapstrip b h.1, h.2⟩
  have hcapsdis : x ∈ P.capDisk (!b) → x ∉ P.capDisk b :=
    fun hother hown => disjoint_left.mp (P.disjoint_capDisks b) hown hother
  simp only [mem_union, mem_inter_iff, mem_sdiff] at *
  tauto

theorem second_side_disk_port_frontier
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) (a : Bool → X) (ha : ∀ b, a b ∈ P.capDisk b)
    (hdis : Disjoint (connectedComponentIn P.cutCarrier (a false))
      (connectedComponentIn P.cutCarrier (a true))) (b : Bool) :
    frontier (connectedComponentIn R (a false)) =
      (frontier (connectedComponentIn P.cutCarrier (a b) ∪ P.closedStrip) \
        (P.capDisk (!b) \ P.capRimSet (!b))) ∪
      (frontier (connectedComponentIn P.cutCarrier (a (!b))) \
        (P.capDisk (!b) \ P.capRimSet (!b))) := by
  let D := fun b => connectedComponentIn P.cutCarrier (a b)
  let C := connectedComponentIn R (a false)
  let U := D b ∪ P.closedStrip
  obtain ⟨hQ, _, hQf, hattach, _, _⟩ := P.cut_geometry hR hopen
  have hcapQ (d : Bool) : P.capDisk d ⊆ P.cutCarrier := by
    intro x hx
    apply (hattach.symm.subset ?_).2
    rw [P.endDisks_eq_capDisks]
    cases d
    · exact Or.inl hx
    · exact Or.inr hx
  have hacut (d : Bool) := hcapQ d (ha d)
  have hcapD (d : Bool) : P.capDisk d ⊆ D d :=
    (P.isConnected_capDisk d).isPreconnected.subset_connectedComponentIn (ha d) (hcapQ d)
  have hrec : C = (D false ∪ D true) ∪ P.closedStrip :=
    (P.component_reconstruction hR hopen hPL (ha false) (ha true)).1
  have hcover : U ∪ D (!b) = C := by
    dsimp only [U]
    rw [hrec]
    cases b <;> simp only [Bool.not_false, Bool.not_true] <;> ext x <;>
      simp only [mem_union] <;> tauto
  have hDC : D (!b) ⊆ C := subset_union_right.trans hcover.subset
  have haR : a false ∈ R := sdiff_subset (hacut false)
  have hCc : IsCompact C := isCompact_connectedComponentIn_of_mem hR haR
  have hCf : frontier C = C ∩ frontier R := by
    let : LocallyPathConnectedSpace R := he.locallyPathConnectedSpace
    obtain ⟨O, hO, hCO⟩ := exists_open_inter_of_relative_open
      (connectedComponentIn_subset R (a false)) (isOpen_preimage_connectedComponentIn haR)
    exact frontier_eq_inter_of_eq_inter_open hR.isClosed hCc.isClosed hO hCO
  have hDf : frontier (D (!b)) = (frontier C ∩ D (!b)) ∪ P.capDisk (!b) := by
    let : LocallyPathConnectedSpace P.cutCarrier := hPL.locallyPathConnectedSpace
    obtain ⟨O, hO, hDO⟩ := exists_open_inter_of_relative_open
      (connectedComponentIn_subset P.cutCarrier (a (!b)))
      (isOpen_preimage_connectedComponentIn (hacut (!b)))
    have hf : frontier (D (!b)) = D (!b) ∩ frontier P.cutCarrier :=
      frontier_eq_inter_of_eq_inter_open hQ.isClosed
        (isCompact_connectedComponentIn_of_mem hQ (hacut (!b))).isClosed hO hDO
    rw [hf, hQf, P.endDisks_eq_capDisks, hCf]
    ext x
    have hnotopen : x ∈ D (!b) → x ∉ P.openStrip :=
      fun hx => (connectedComponentIn_subset _ _ hx).2
    have hown : x ∈ P.capDisk (!b) → x ∈ D (!b) := fun hx => hcapD (!b) hx
    have hCmem : x ∈ D (!b) → x ∈ C := fun hx => hDC hx
    have hother : x ∈ D (!b) → x ∉ P.capDisk b := by
      intro hx hc
      cases b
      · exact disjoint_left.mp hdis (hcapD false hc) hx
      · exact disjoint_left.mp hdis hx (hcapD true hc)
    cases b <;>
      simp only [Bool.not_false, Bool.not_true, mem_inter_iff, mem_union, mem_sdiff] at * <;> tauto
  have hUf : frontier U = (frontier C ∩ U) ∪ P.capDisk (!b) :=
    (P.one_side_attachment_frontier hR hopen hPL a ha hdis b).2.2
  have hcapC : P.capDisk (!b) ∩ frontier C = P.capRimSet (!b) := by
    rw [hCf]
    have hsub := (hcapD (!b)).trans hDC
    calc
      P.capDisk (!b) ∩ (C ∩ frontier R) = P.capDisk (!b) ∩ frontier R := by
        ext x
        have hx : x ∈ P.capDisk (!b) → x ∈ C := fun h => hsub h
        simp only [mem_inter_iff]
        tauto
      _ = P.capRimSet (!b) := P.capDisk_inter_frontier (!b)
  change frontier C = (frontier U \ _) ∪ (frontier (D (!b)) \ _)
  rw [hUf, hDf]
  ext x
  have hpointcover : x ∈ frontier C → x ∈ U ∨ x ∈ D (!b) :=
    fun hx => hcover.symm.subset (hCc.isClosed.frontier_subset hx)
  have hrim : x ∈ P.capRimSet (!b) ↔ x ∈ P.capDisk (!b) ∧ x ∈ frontier C :=
    (Set.ext_iff.mp hcapC x).symm
  simp only [mem_union, mem_inter_iff, mem_sdiff] at *
  tauto

end PoincareConjecture.M76.OriginalDiskProduct
