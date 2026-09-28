import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalDiskProductHandle
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoPortComponentCarriers
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapGeometry









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem exists_two_components_of_disconnected_cut
    (P : OriginalDiskProduct e R j) (hR : IsCompact R) (hRc : IsConnected R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) (hdisc : ¬ IsConnected P.cutCarrier) :
    ∃ (a : Bool → X) (ha : ∀ b, a b ∈ P.cutCarrier)
      (E : Bool ≃ ConnectedComponents P.cutCarrier),
      (∀ b, a b ∈ P.capDisk b) ∧
      (∀ b, E b = ConnectedComponents.mk (⟨a b, ha b⟩ : P.cutCarrier)) ∧
      (∀ b, IsConnected (connectedComponentIn P.cutCarrier (a b))) ∧
      P.cutCarrier = connectedComponentIn P.cutCarrier (a false) ∪
        connectedComponentIn P.cutCarrier (a true) ∧
      Disjoint (connectedComponentIn P.cutCarrier (a false))
        (connectedComponentIn P.cutCarrier (a true)) ∧
      (∀ b, P.capDisk b ⊆ connectedComponentIn P.cutCarrier (a b)) ∧
      (∀ b, Disjoint (connectedComponentIn P.cutCarrier (a b)) (P.capDisk (!b))) ∧
      (∀ b, connectedComponentIn P.cutCarrier (a b) ∩ P.closedStrip = P.capDisk b) ∧
      P.closedStrip ∪ P.cutCarrier = R := by
  classical
  obtain ⟨hc, _, _, ho, hu, _⟩ := P.cut_geometry hR hopen
  let : LocallyPathConnectedSpace P.cutCarrier := hPL.locallyPathConnectedSpace
  have hcapcut (b : Bool) : P.capDisk b ⊆ P.cutCarrier := by
    intro x hx
    apply (ho.symm.subset ?_).2
    rw [P.endDisks_eq_capDisks]
    cases b with
    | false => exact Or.inl hx
    | true => exact Or.inr hx
  choose a ha using fun b => (P.isConnected_capDisk b).nonempty
  have hac (b : Bool) : a b ∈ P.cutCarrier := hcapcut b (ha b)
  have hcap (b : Bool) : P.capDisk b ⊆ connectedComponentIn P.cutCarrier (a b) :=
    (P.isConnected_capDisk b).isPreconnected.subset_connectedComponentIn (ha b) (hcapcut b)
  have hstrip : IsConnected P.closedStrip := by
    apply ((isConnected_closedBall (x := (0 : V2)) zero_le_one).prod
      (isConnected_Icc (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2))).image P.map
    apply P.polyhedral.continuousOn.mono
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hports : P.cutCarrier ∩ P.closedStrip = P.capDisk false ∪ P.capDisk true := by
    rw [inter_comm, ho, P.endDisks_eq_capDisks]
  obtain ⟨hmerged, _⟩ := Topology.componentIn_closed_attachment_of_two_connected_ports
    hc.isClosed (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
    hstrip (P.isConnected_capDisk false) (P.isConnected_capDisk true) hports
    (ha false) (ha true)
  change connectedComponentIn (P.cutCarrier ∪ P.closedStrip) (a false) =
    (connectedComponentIn P.cutCarrier (a false) ∪
      connectedComponentIn P.cutCarrier (a true)) ∪ P.closedStrip at hmerged
  have hwhole : connectedComponentIn (P.cutCarrier ∪ P.closedStrip) (a false) = R := by
    rw [union_comm, hu]
    exact hRc.isPreconnected.connectedComponentIn (sdiff_subset (hac false))
  have hcutcover : P.cutCarrier = connectedComponentIn P.cutCarrier (a false) ∪
      connectedComponentIn P.cutCarrier (a true) := by
    apply Subset.antisymm
    · intro x hx
      have hxR : x ∈ R := sdiff_subset hx
      rw [← hwhole, hmerged] at hxR
      rcases hxR with hxC | hxS
      · exact hxC
      · rcases hports.subset ⟨hx, hxS⟩ with h0 | h1
        · exact Or.inl (hcap false h0)
        · exact Or.inr (hcap true h1)
    · exact union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)
  have hne : connectedComponentIn P.cutCarrier (a false) ≠
      connectedComponentIn P.cutCarrier (a true) := by
    intro heq
    apply hdisc
    rw [hcutcover, heq, union_self]
    exact isConnected_connectedComponentIn_iff.mpr (hac true)
  have hdis : Disjoint (connectedComponentIn P.cutCarrier (a false))
      (connectedComponentIn P.cutCarrier (a true)) := by
    apply disjoint_left.mpr
    intro x hx0 hx1
    exact hne ((connectedComponentIn_eq hx0).trans (connectedComponentIn_eq hx1).symm)
  let f : Bool → ConnectedComponents P.cutCarrier := fun b =>
    ConnectedComponents.mk (⟨a b, hac b⟩ : P.cutCarrier)
  have hfmem (b : Bool) (x : P.cutCarrier) :
      f b = ConnectedComponents.mk x ↔ (x : X) ∈ connectedComponentIn P.cutCarrier (a b) := by
    rw [eq_comm, ConnectedComponents.coe_eq_coe', connectedComponentIn_eq_image (hac b)]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hxy : y = x := Subtype.ext hyx
      exact hxy ▸ hy
  have hfinj : Function.Injective f := by
    intro b c hbc
    by_contra hnebc
    have hcross := (hfmem b ⟨a c, hac c⟩).mp hbc
    cases b <;> cases c
    · exact hnebc rfl
    · exact disjoint_left.mp hdis hcross (mem_connectedComponentIn (hac true))
    · exact disjoint_left.mp hdis (mem_connectedComponentIn (hac false)) hcross
    · exact hnebc rfl
  have hfsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    rcases hcutcover.subset x.property with hx0 | hx1
    · exact ⟨false, (hfmem false x).mpr hx0⟩
    · exact ⟨true, (hfmem true x).mpr hx1⟩
  have hmiss (b : Bool) :
      Disjoint (connectedComponentIn P.cutCarrier (a b)) (P.capDisk (!b)) := by
    cases b with
    | false => exact hdis.mono_right (hcap true)
    | true => exact hdis.symm.mono_right (hcap false)
  refine ⟨a, hac, Equiv.ofBijective f ⟨hfinj, hfsurj⟩, ha, fun _ => rfl,
    fun b => isConnected_connectedComponentIn_iff.mpr (hac b), hcutcover, hdis, hcap,
    hmiss, ?_, hu⟩
  intro b
  apply Subset.antisymm
  · intro x hx
    have hxports := hports.subset ⟨connectedComponentIn_subset _ _ hx.1, hx.2⟩
    cases b with
    | false =>
      exact hxports.resolve_right (fun hxopp => disjoint_left.mp (hmiss false) hx.1 hxopp)
    | true =>
      exact hxports.resolve_left (fun hxopp => disjoint_left.mp (hmiss true) hx.1 hxopp)
  · intro x hx
    refine ⟨hcap b hx, P.endDisks_subset_closedStrip ?_⟩
    rw [P.endDisks_eq_capDisks]
    cases b with
    | false => exact Or.inl hx
    | true => exact Or.inr hx


theorem card_components_of_disconnected_cut
    (P : OriginalDiskProduct e R j) (hR : IsCompact R) (hRc : IsConnected R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) (hdisc : ¬ IsConnected P.cutCarrier) :
    Nat.card (ConnectedComponents P.cutCarrier) = 2 := by
  obtain ⟨_, _, E, _⟩ := P.exists_two_components_of_disconnected_cut hR hRc hopen hPL hdisc
  simpa using (Nat.card_congr E).symm

end PoincareConjecture.M76.OriginalDiskProduct
