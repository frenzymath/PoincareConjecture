import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalDiskCutComponents
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.FiniteCapComponents
import PoincareConjecture.Proofs.M76.Wall.PLDomainComponents

set_option autoImplicit false
open Set Metric Geometry

namespace Geometry.CubicalThreeSphere

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)

theorem isConnected_punctured_sphere_of_isOpen {κ : Type*} [Finite κ]
    (D B : κ → Set V4) (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hDS : ∀ i, D i ⊆ sphere)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hholes : ∀ i, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (D i \ B i))) :
    IsConnected (sphere \ ⋃ i, D i \ B i) := by
  classical
  let Q := sphere \ ⋃ i, D i \ B i
  have hU : IsOpen ((Subtype.val : sphere → V4) ⁻¹' (⋃ i, D i \ B i)) := by
    rw [preimage_iUnion]
    exact isOpen_iUnion hholes
  have himage : (Subtype.val : sphere → V4) ''
      (((Subtype.val : sphere → V4) ⁻¹' (⋃ i, D i \ B i))ᶜ) = Q := by
    ext x
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ ⟨y.property, hy⟩,
      fun hx => ⟨⟨x, hx.1⟩, hx.2, rfl⟩⟩
  have hQ : IsClosed Q := by
    rw [← himage]
    exact isClosed_frontier.isClosedMap_subtype_val _ hU.isClosed_compl
  have hattach (i : κ) : Q ∩ D i = B i := by
    apply Subset.antisymm
    · intro x hx
      by_contra hnot
      exact hx.1.2 (mem_iUnion.mpr ⟨i, hx.2, hnot⟩)
    · intro x hx
      refine ⟨⟨hDS i ((hD i).1 hx), ?_⟩, (hD i).1 hx⟩
      intro hh
      obtain ⟨k, hk, hkb⟩ := mem_iUnion.mp hh
      by_cases hki : k = i
      · exact hkb (hki.symm ▸ hx)
      · exact disjoint_left.mp (hdis hki) hk ((hD i).1 hx)
  have hfill : Q ∪ ⋃ i, D i = sphere := by
    apply Subset.antisymm
    · exact union_subset sdiff_subset (iUnion_subset hDS)
    · intro x hx
      by_cases hh : x ∈ ⋃ i, D i \ B i
      · obtain ⟨i, hi, _⟩ := mem_iUnion.mp hh
        exact Or.inr (mem_iUnion.mpr ⟨i, hi⟩)
      · exact Or.inl ⟨hx, hh⟩
  obtain ⟨H, _⟩ := exists_components_homeomorph_finite_cap_attachment D B hQ hD hdis hattach
  let : SimplyConnectedSpace sphere := simplyConnectedSpace_sphere
  have hfilled : ConnectedSpace (Q ∪ ⋃ i, D i : Set V4) := by
    rw [hfill]
    infer_instance
  let : ConnectedSpace (Q ∪ ⋃ i, D i : Set V4) := hfilled
  have hclasses (x y : Q) : ConnectedComponents.mk x = ConnectedComponents.mk y :=
    H.injective (Subsingleton.elim _ _)
  let : PreconnectedSpace Q := preconnectedSpace_iff_connectedComponent.mpr (fun x => by
    apply eq_univ_of_forall
    intro y
    exact ConnectedComponents.coe_eq_coe'.mp (hclasses y x))
  obtain ⟨z⟩ := (inferInstance : Nonempty (Q ∪ ⋃ i, D i : Set V4))
  obtain ⟨x, _⟩ := ConnectedComponents.surjective_coe (H.symm (ConnectedComponents.mk z))
  let : Nonempty Q := ⟨x⟩
  let : ConnectedSpace Q := { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }
  exact isConnected_iff_connectedSpace.mpr (show ConnectedSpace Q from inferInstance)

end Geometry.CubicalThreeSphere

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem exists_two_PL_components_of_punctured_sphere_cut
    (P : OriginalDiskProduct e R j) (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier)
    {κ : Type*} [Finite κ] (D B : κ → Set V4)
    (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hDS : ∀ i, D i ⊆ Sphere)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hholes : ∀ i, IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (D i \ B i)))
    (H : R ≃ₜ (Sphere \ ⋃ i, D i \ B i : Set V4)) :
    ∃ (A : Bool → Set X) (a : Bool → X),
      (∀ b, a b ∈ P.cutCarrier ∧ A b = connectedComponentIn P.cutCarrier (a b)) ∧
      (∀ b, PLDomain e (A b) ∧ IsCompact (A b) ∧ IsConnected (A b)) ∧
      P.cutCarrier = A false ∪ A true ∧ Disjoint (A false) (A true) ∧
      (∀ b, P.capDisk b ⊆ A b ∧ Disjoint (A b) (P.capDisk (!b))) ∧
      (∀ b, A b ∩ P.closedStrip = P.capDisk b) ∧
      (∀ b, frontier (A b) = A b ∩ ((frontier R \ P.openStrip) ∪ P.endDisks)) ∧
      Nat.card (ConnectedComponents P.cutCarrier) = 2 ∧
      P.closedStrip ∪ (A false ∪ A true) = R := by
  have hmodel := Geometry.CubicalThreeSphere.isConnected_punctured_sphere_of_isOpen
    D B hD hDS hdis hholes
  let : ConnectedSpace (Sphere \ ⋃ i, D i \ B i : Set V4) :=
    isConnected_iff_connectedSpace.mp hmodel
  let : ConnectedSpace R := H.connectedSpace_iff.mpr inferInstance
  have hRc : IsConnected R := isConnected_iff_connectedSpace.mpr inferInstance
  have hdisc : ¬ IsConnected P.cutCarrier := by
    intro hc
    exact P.not_homeomorph_punctured_sphere_of_connected_cut hR hopen hPL hc
      D B hD hDS hdis hholes ⟨H⟩
  obtain ⟨a, ha, E, _, _, hc, hcover, hsep, hcap, hmiss, hinter, hrec⟩ :=
    P.exists_two_components_of_disconnected_cut hR hRc hopen hPL hdisc
  obtain ⟨hcompact, _, hfront, _, _, _⟩ := P.cut_geometry hR hopen
  refine ⟨fun b => connectedComponentIn P.cutCarrier (a b), a, fun b => ⟨ha b, rfl⟩,
    fun b => ⟨hPL.connectedComponentIn hcompact (ha b),
      isCompact_connectedComponentIn_of_mem hcompact (ha b), hc b⟩,
    hcover, hsep, fun b => ⟨hcap b, hmiss b⟩, hinter, ?_, ?_, ?_⟩
  · intro b
    let : LocallyPathConnectedSpace P.cutCarrier := hPL.locallyPathConnectedSpace
    obtain ⟨U, hU, hAU⟩ := exists_open_inter_of_relative_open
      (connectedComponentIn_subset P.cutCarrier (a b))
      (isOpen_preimage_connectedComponentIn (ha b))
    rw [frontier_eq_inter_of_eq_inter_open hcompact.isClosed
      (isCompact_connectedComponentIn_of_mem hcompact (ha b)).isClosed hU hAU, hfront]
  · simpa using (Nat.card_congr E).symm
  · rwa [← hcover]

end PoincareConjecture.M76.OriginalDiskProduct

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere

theorem exists_original_punctured_sphere_disk_cut
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X} {j : V2 → X}
    (hR : IsCompact R) (he : PLDomain e R)
    (hj : PolyhedralPLInCharts e j Disk)
    (hemb : Topology.IsEmbedding (fun z : Disk => j z))
    (hDR : MapsTo j Disk R)
    (hproper : ∀ z : Disk, j z ∈ frontier R ↔ (z : V2) ∈ sphere 0 1)
    (hU : IsOpen U) (hDU : j '' Disk ⊆ U)
    {κ : Type*} [Finite κ] (D B : κ → Set V4)
    (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hDS : ∀ i, D i ⊆ Sphere)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hholes : ∀ i, IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (D i \ B i)))
    (H : R ≃ₜ (Sphere \ ⋃ i, D i \ B i : Set V4)) :
    ∃ (P : OriginalDiskProduct e R j) (A : Bool → Set X) (a : Bool → X),
      MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) U ∧
      PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
      (∀ b, a b ∈ P.cutCarrier ∧ A b = connectedComponentIn P.cutCarrier (a b)) ∧
      (∀ b, PLDomain e (A b) ∧ IsCompact (A b) ∧ IsConnected (A b)) ∧
      P.cutCarrier = A false ∪ A true ∧ Disjoint (A false) (A true) ∧
      (∀ b, P.capDisk b ⊆ A b ∧ Disjoint (A b) (P.capDisk (!b))) ∧
      (∀ b, A b ∩ P.closedStrip = P.capDisk b) ∧
      (∀ b, frontier (A b) = A b ∩ ((frontier R \ P.openStrip) ∪ P.endDisks)) ∧
      Nat.card (ConnectedComponents P.cutCarrier) = 2 ∧
      P.closedStrip ∪ (A false ∪ A true) = R := by
  obtain ⟨P, hsmall, hopen, hPL, hc, _, _, _, _, _, _⟩ :=
    exists_original_disk_cut_domain_with_collars hR he hj hemb hDR hproper hU hDU
  obtain ⟨A, a, hcomponents⟩ := P.exists_two_PL_components_of_punctured_sphere_cut
    hR hopen hPL D B hD hDS hdis hholes H
  exact ⟨P, A, a, hsmall, hPL, hc, hcomponents⟩

end PoincareConjecture.M76
