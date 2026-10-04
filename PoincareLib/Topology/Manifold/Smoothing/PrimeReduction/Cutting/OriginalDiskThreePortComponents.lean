import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Cutting.OriginalDiskThreePorts
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Cutting.CommonCutComponentDomains
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Complement.OriginalExteriorCapSpheres
import Mathlib.Data.Fin.VecNotation

/-!
# The five component cases of the actual global sphere-disk cut

The same proper disk product constructs the three disjoint sphere ports.
The global complement has no component missing those ports: connected
reconstruction gives its entire component partition and each exact frontier.
-/

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareMT.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_original_three_port_component_domains
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) j)
    (hR : IsCompact R) (hRc : IsConnected R) (he : PLDomain e R)
    (hK : PLDomain e K) (hKc : IsConnected K) (hKR : K ⊆ interior R)
    (B : Bool → Set X) (sB : ∀ b, ChartwisePLSphere e (B b))
    (hBdis : Disjoint (B false) (B true)) (hfront : frontier K = B false ∪ B true)
    (hsmall : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (interior R))
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (hDPL : PLDomain e (K ∪ P.closedStrip))
    (hDfront : frontier (K ∪ P.closedStrip) = (frontier K \ P.openStrip) ∪ P.endDisks) :
    ∃ (owner : Bool) (k q : Bool → Set V3) (p : Fin 3 → Set X)
      (sp : ∀ i, ChartwisePLSphere e (p i)) (a : Fin 3 → X) (C : Fin 3 → Set X),
      (∀ b, IsFinitePLBallPair P2 (k b) (q b) ∧ k b ⊆ Sphere ∧
        IsFinitePLBallPair P2 (Sphere \ (k b \ q b)) (q b) ∧
        (sB owner).map '' q b = P.capRimSet b ∧
        ((sB owner).map '' k b) ∩ P.closedStrip = (sB owner).map '' q b ∧
        P.capDisk b ∩ K = (sB owner).map '' q b) ∧
      p = ![B (!owner), ((sB owner).map '' k false) ∪ P.capDisk false,
        ((sB owner).map '' k true) ∪ P.capDisk true] ∧
      Pairwise (fun i j => Disjoint (p i) (p j)) ∧
      frontier (K ∪ P.closedStrip) = ⋃ i, p i ∧
      (∀ i, a i ∈ p i ∧ a i ∈ P.cutCarrier ∧
        C i = connectedComponentIn P.cutCarrier (a i)) ∧
      (∀ i, IsCompact (C i) ∧ PLDomain e (C i) ∧ IsConnected (C i) ∧
        C i ⊆ P.cutCarrier ∧ p i ⊆ C i) ∧
      P.cutCarrier = ⋃ i, C i ∧
      (∀ i j, C i = C j ∨ Disjoint (C i) (C j)) ∧
      (∀ i, frontier (C i) = (C i ∩ frontier R) ∪ ⋃ j ∈ {j | C j = C i}, p j) ∧
      (∀ i, C i ∩ (K ∪ P.closedStrip) = ⋃ j ∈ {j | C j = C i}, p j) ∧
      (∀ x ∈ P.cutCarrier, ∃ i, connectedComponentIn P.cutCarrier x = C i) ∧
      ((∀ i j, C i = C j) ∨
        (C 0 = C 1 ∧ C 0 ≠ C 2 ∧ C 1 ≠ C 2) ∨
        (C 0 = C 2 ∧ C 0 ≠ C 1 ∧ C 1 ≠ C 2) ∨
        (C 1 = C 2 ∧ C 0 ≠ C 1 ∧ C 0 ≠ C 2) ∨
        (C 0 ≠ C 1 ∧ C 0 ≠ C 2 ∧ C 1 ≠ C 2)) := by
  classical
  obtain ⟨owner, k, q, howner, hk, _, _, _, _, hnewdis, hnewopp, hports⟩ :=
    P.exists_original_three_connected_ports hR he hK hKR B sB hBdis hfront hsmall hstripK
  obtain ⟨t, _⟩ := P.exists_original_exterior_retained_caps B sB he.compatible
    hK.closed hfront hstripK owner ((howner owner).mpr rfl) k q
    (fun b => ⟨(hk b).1, (hk b).2.1, (hk b).2.2.1, (hk b).2.2.2.1⟩)
  let p : Fin 3 → Set X := ![B (!owner),
    ((sB owner).map '' k false) ∪ P.capDisk false,
    ((sB owner).map '' k true) ∪ P.capDisk true]
  let sp : ∀ i, ChartwisePLSphere e (p i) :=
    Fin.cases (sB (!owner)) (Fin.cases (t false) (Fin.cases (t true) (fun i => Fin.elim0 i)))
  have hpdis : Pairwise (fun i j => Disjoint (p i) (p j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hnewopp false
    · exact hnewopp true
    · exact (hnewopp false).symm
    · exact (hij rfl).elim
    · exact hnewdis
    · exact (hnewopp true).symm
    · exact hnewdis.symm
    · exact (hij rfl).elim
  have hpconn (i : Fin 3) : IsConnected (p i) := isConnected_iff_connectedSpace.mpr
    ((sp i).parametrization.connectedSpace_iff.mp (isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by simp) (0 : V3) zero_le_one)))
  have hunion : ((B (!owner) ∪ ((sB owner).map '' k false ∪ P.capDisk false)) ∪
      ((sB owner).map '' k true ∪ P.capDisk true)) = ⋃ i, p i := by
    ext x
    constructor
    · rintro ((h0 | h1) | h2)
      · exact mem_iUnion.mpr ⟨0, h0⟩
      · exact mem_iUnion.mpr ⟨1, h1⟩
      · exact mem_iUnion.mpr ⟨2, h2⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
  have hportfront : frontier (K ∪ P.closedStrip) = ⋃ i, p i :=
    hDfront.trans (hports.trans hunion)
  obtain ⟨_, hQeq, hQc, hQPL, hQR, hQD, hQfront, _, _⟩ :=
    P.global_common_cut_geometry hR he hDPL hKR rfl hsmall hDfront
  have hcut : P.cutCarrier = R ∩ (interior (K ∪ P.closedStrip))ᶜ := hQeq.symm
  rw [← hcut] at hQc hQPL hQR hQD hQfront
  have hstripconn : IsConnected P.closedStrip := by
    apply ((isConnected_closedBall (x := (0 : V2)) zero_le_one).prod
      (isConnected_Icc (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2))).image
    apply P.polyhedral.continuousOn.mono
    rintro z ⟨hz, ht⟩
    exact ⟨hz, by constructor <;> linarith [ht.1, ht.2]⟩
  have hmeet : (K ∩ P.closedStrip).Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_sphere (by simp) (0 : V2) zero_le_one).nonempty
    have hx : P.map (z, 0) ∈ P.map '' (Rim ×ˢ J) :=
      ⟨(z, 0), ⟨hz, by norm_num⟩, rfl⟩
    exact ⟨_, (hstripK.symm.subset hx).2, (hstripK.symm.subset hx).1⟩
  have hDconn := hKc.union hmeet hstripconn
  have hwhole : IsConnected (P.cutCarrier ∪ (K ∪ P.closedStrip)) := hQR.symm ▸ hRc
  have hQports : P.cutCarrier ∩ (K ∪ P.closedStrip) = ⋃ i, p i :=
    hQD.trans (hports.trans hunion)
  obtain ⟨a, C, ha, hC, hcover, hdis, hCfront, hCattach, hexhaust, hcases⟩ :=
    hQPL.exists_three_port_component_domains hQc hDPL.closed hDconn hwhole p hpconn hQports
  refine ⟨owner, k, q, p, sp, a, C, hk, rfl, hpdis, hportfront, ha, hC,
    hcover, hdis, ?_, hCattach, hexhaust, hcases⟩
  intro i
  rw [hCfront i, hQfront, hports, hunion, inter_union_distrib_left, union_comm]
  congr 1
  rw [← hQports, ← inter_assoc, inter_eq_left.mpr (hC i).2.2.2.1, hCattach]

end PoincareMT.M76.OriginalDiskProduct
