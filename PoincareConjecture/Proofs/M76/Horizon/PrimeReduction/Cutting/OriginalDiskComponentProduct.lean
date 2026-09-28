import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalDiskComponentHandle

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1

theorem exists_component_product
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) {a b : X}
    (ha : a ∈ P.capDisk false) (hb : b ∈ P.capDisk true) :
    ∃ G : OriginalDiskProduct e (connectedComponentIn R a) j,
      G.map = P.map ∧ G.closedStrip = P.closedStrip ∧ G.openStrip = P.openStrip ∧
      G.endDisks = P.endDisks ∧ (∀ i, G.capDisk i = P.capDisk i) ∧
      IsCompact (connectedComponentIn R a) ∧ PLDomain e (connectedComponentIn R a) ∧
      IsOpen ((Subtype.val : connectedComponentIn R a → X) ⁻¹' G.openStrip) ∧
      IsCompact G.cutCarrier ∧ PLDomain e G.cutCarrier ∧
      G.cutCarrier = connectedComponentIn P.cutCarrier a ∪ connectedComponentIn P.cutCarrier b := by
  have haM : a ∈ P.map '' (Disk ×ˢ Icc (-1 : ℝ) 1) :=
    image_mono (cap_source_subset false) ha
  have hMR : P.map '' (Disk ×ˢ Icc (-1 : ℝ) 1) ⊆ R := by
    rintro x ⟨z, hz, rfl⟩
    exact P.inside hz
  have haR : a ∈ R := hMR haM
  have hMconn : IsConnected (P.map '' (Disk ×ˢ Icc (-1 : ℝ) 1)) :=
    ((isConnected_closedBall (x := (0 : V2)) zero_le_one).prod
      (isConnected_Icc (by norm_num : (-1 : ℝ) ≤ 1))).image _ P.polyhedral.continuousOn
  have hMC : P.map '' (Disk ×ˢ Icc (-1 : ℝ) 1) ⊆ connectedComponentIn R a :=
    hMconn.isPreconnected.subset_connectedComponentIn haM hMR
  have hCcompact : IsCompact (connectedComponentIn R a) :=
    isCompact_connectedComponentIn_of_mem hR haR
  have hCPL := he.connectedComponentIn hR haR
  let : LocallyPathConnectedSpace R := he.locallyPathConnectedSpace
  obtain ⟨U, hU, hCU⟩ := exists_open_inter_of_relative_open (connectedComponentIn_subset R a)
    (isOpen_preimage_connectedComponentIn haR)
  have hCfront : frontier (connectedComponentIn R a) = connectedComponentIn R a ∩ frontier R :=
    frontier_eq_inter_of_eq_inter_open hR.isClosed hCcompact.isClosed hU hCU
  let G : OriginalDiskProduct e (connectedComponentIn R a) j :=
    { map := P.map
      polyhedral := P.polyhedral
      injective := P.injective
      embedding := P.embedding
      inside := fun z hz => hMC (mem_image_of_mem P.map hz)
      central := P.central
      proper := fun z hz => by
        rw [hCfront]
        exact ⟨fun h => (P.proper z hz).mp h.2,
          fun h => ⟨hMC (mem_image_of_mem P.map hz), (P.proper z hz).mpr h⟩⟩ }
  let incl : connectedComponentIn R a → R := fun x =>
    ⟨x, connectedComponentIn_subset R a x.property⟩
  have hincl : Continuous incl := continuous_subtype_val.subtype_mk _
  have hGopen : IsOpen ((Subtype.val : connectedComponentIn R a → X) ⁻¹' G.openStrip) :=
    hopen.preimage hincl
  obtain ⟨hQcompact, _, _, hattach, _, _⟩ := P.cut_geometry hR hopen
  have hGcut : G.cutCarrier = connectedComponentIn R a ∩ P.cutCarrier := by
    change connectedComponentIn R a \ P.openStrip = _
    ext x
    exact ⟨fun hx => ⟨hx.1, ⟨connectedComponentIn_subset R a hx.1, hx.2⟩⟩,
      fun hx => ⟨hx.1, hx.2.2⟩⟩
  have hGcompact : IsCompact G.cutCarrier := by
    rw [hGcut]
    exact hCcompact.inter_right hQcompact.isClosed
  have hGsub : G.cutCarrier ⊆ P.cutCarrier := by
    rw [hGcut]
    exact inter_subset_right
  have hGrelopen : IsOpen ((Subtype.val : P.cutCarrier → X) ⁻¹' G.cutCarrier) := by
    have heq : (Subtype.val : P.cutCarrier → X) ⁻¹' G.cutCarrier =
        (Subtype.val : P.cutCarrier → X) ⁻¹' U := by
      ext x
      rw [mem_preimage, hGcut, mem_inter_iff]
      have hmem : (x : X) ∈ connectedComponentIn R a ↔ (x : X) ∈ U := by
        rw [hCU]
        exact and_iff_right (sdiff_subset x.property)
      exact ⟨fun h => hmem.mp h.1, fun h => ⟨hmem.mpr h, x.property⟩⟩
    rw [heq]
    exact hU.preimage continuous_subtype_val
  have hGPL := hPL.of_relative_clopen_subset hGsub hGcompact.isClosed hGrelopen
  have hcapQ (i : Bool) : P.capDisk i ⊆ P.cutCarrier := by
    intro x hx
    apply (hattach.symm.subset ?_).2
    rw [P.endDisks_eq_capDisks]
    cases i
    · exact Or.inl hx
    · exact Or.inr hx
  have hports : P.endDisks ⊆ connectedComponentIn P.cutCarrier a ∪
      connectedComponentIn P.cutCarrier b := by
    rw [P.endDisks_eq_capDisks]
    exact union_subset_union
      ((P.isConnected_capDisk false).isPreconnected.subset_connectedComponentIn ha (hcapQ false))
      ((P.isConnected_capDisk true).isPreconnected.subset_connectedComponentIn hb (hcapQ true))
  have hcutEq : G.cutCarrier = connectedComponentIn P.cutCarrier a ∪
      connectedComponentIn P.cutCarrier b := by
    change connectedComponentIn R a \ P.openStrip = _
    rw [(P.component_reconstruction hR hopen hPL ha hb).1, union_sdiff_distrib,
      P.closedStrip_sdiff_openStrip]
    have havoid : (connectedComponentIn P.cutCarrier a ∪
        connectedComponentIn P.cutCarrier b) \ P.openStrip =
        connectedComponentIn P.cutCarrier a ∪ connectedComponentIn P.cutCarrier b := by
      apply sdiff_eq_left.mpr
      apply disjoint_left.mpr
      rintro x (hx | hx) ho
      · exact (connectedComponentIn_subset _ _ hx).2 ho
      · exact (connectedComponentIn_subset _ _ hx).2 ho
    rw [havoid, union_eq_left.mpr hports]
  exact ⟨G, rfl, rfl, rfl, rfl, fun _ => rfl, hCcompact, hCPL, hGopen,
    hGcompact, hGPL, hcutEq⟩

end PoincareConjecture.M76.OriginalDiskProduct
