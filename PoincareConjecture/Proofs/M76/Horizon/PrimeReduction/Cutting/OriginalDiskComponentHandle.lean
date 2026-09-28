import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalDiskProductHandle
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoPortComponentCarriers
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapGeometry
import PoincareConjecture.Proofs.M76.Wall.PLDomainComponents









set_option autoImplicit false
open Set Metric Geometry
open scoped unitInterval

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere

theorem component_reconstruction
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) {a b : X}
    (ha : a ∈ P.capDisk false) (hb : b ∈ P.capDisk true) :
    connectedComponentIn R a =
      (connectedComponentIn P.cutCarrier a ∪ connectedComponentIn P.cutCarrier b) ∪
        P.closedStrip ∧
      ∀ x ∈ P.cutCarrier,
        x ∉ connectedComponentIn P.cutCarrier a ∪ connectedComponentIn P.cutCarrier b →
          connectedComponentIn R x = connectedComponentIn P.cutCarrier x := by
  obtain ⟨hc, _, _, hattach, hcover, _⟩ := P.cut_geometry hR hopen
  let : LocallyPathConnectedSpace P.cutCarrier := hPL.locallyPathConnectedSpace
  have hstrip : IsConnected P.closedStrip := by
    apply ((isConnected_closedBall (x := (0 : V2)) zero_le_one).prod
      (isConnected_Icc (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2))).image
    apply P.polyhedral.continuousOn.mono
    rintro z ⟨hz, ht⟩
    exact ⟨hz, by constructor <;> linarith [ht.1, ht.2]⟩
  have hports : P.cutCarrier ∩ P.closedStrip = P.capDisk false ∪ P.capDisk true := by
    rw [inter_comm, hattach, P.endDisks_eq_capDisks]
  have h := Topology.componentIn_closed_attachment_of_two_connected_ports
    (P := P.cutCarrier) (D := P.closedStrip)
    hc.isClosed (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
    hstrip (P.isConnected_capDisk false) (P.isConnected_capDisk true) hports ha hb
  simpa only [union_comm P.cutCarrier P.closedStrip, hcover] using h

theorem not_homeomorph_punctured_sphere_of_cap_component_self_attachment
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) {a b : X}
    (ha : a ∈ P.capDisk false) (hb : b ∈ P.capDisk true)
    (hsame : b ∈ connectedComponentIn P.cutCarrier a)
    (D B : κ → Set V4) (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hDS : ∀ i, D i ⊆ Sphere)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hholes : ∀ i, IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (D i \ B i))) :
    ¬ Nonempty ((connectedComponentIn R a : Set X) ≃ₜ
      (Sphere \ ⋃ i, D i \ B i : Set V4)) := by
  obtain ⟨hc, _, _, hattach, _, _⟩ := P.cut_geometry hR hopen
  have hcapQ (i : Bool) : P.capDisk i ⊆ P.cutCarrier := by
    intro x hx
    apply (hattach.symm.subset ?_).2
    rw [P.endDisks_eq_capDisks]
    cases i
    · exact Or.inl hx
    · exact Or.inr hx
  have haQ := hcapQ false ha
  have hbQ := hcapQ true hb
  let : LocallyPathConnectedSpace P.cutCarrier := hPL.locallyPathConnectedSpace
  have hpath : IsPathConnected (connectedComponentIn P.cutCarrier a) := by
    rw [connectedComponentIn_eq_image haQ, ← pathComponent_eq_connectedComponent]
    exact isPathConnected_pathComponent.image continuous_subtype_val
  have hCclosed : IsClosed (connectedComponentIn P.cutCarrier a) :=
    (isCompact_connectedComponentIn_of_mem hc haQ).isClosed
  have hendsC : P.endDisks ⊆ connectedComponentIn P.cutCarrier a := by
    rw [P.endDisks_eq_capDisks]
    apply union_subset
    · exact (P.isConnected_capDisk false).isPreconnected.subset_connectedComponentIn
        ha (hcapQ false)
    · rw [connectedComponentIn_eq hsame]
      exact (P.isConnected_capDisk true).isPreconnected.subset_connectedComponentIn
        hb (hcapQ true)
  obtain ⟨W, _, hWends⟩ := P.exists_closedStrip_product
  let : Nonempty Disk := ⟨⟨0, mem_closedBall_self zero_le_one⟩⟩
  have hWattach (z : Disk × unitInterval) :
      (W z : X) ∈ connectedComponentIn P.cutCarrier a ↔ z.2 = 0 ∨ z.2 = 1 := by
    rw [← hWends]
    exact ⟨fun hx => hattach.subset ⟨(W z).property, connectedComponentIn_subset _ _ hx⟩,
      fun hx => hendsC hx⟩
  have hno := Poincare.Topology.not_nonempty_homeomorph_punctured_sphere_of_product_handle
    hCclosed (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
    hpath W hWattach D B hD hDS hdis hholes
  have hcomponent := (P.component_reconstruction hR hopen hPL ha hb).1
  rw [← connectedComponentIn_eq hsame, union_self] at hcomponent
  rintro ⟨F⟩
  exact hno ⟨(Homeomorph.setCongr hcomponent.symm).trans F⟩

end PoincareConjecture.M76.OriginalDiskProduct
