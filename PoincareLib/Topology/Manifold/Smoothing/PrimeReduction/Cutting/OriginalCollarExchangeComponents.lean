import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Cutting.OriginalDiskThreePortComponents
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Complement.OriginalCollarExchange
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Complement.OriginalSphereProductDomain

/-!
# Literal common-cut components for the same two collar exchanges

One choice of the annulus and retained disks constructs both sphere products
and the complete component partition. The component ledger never replaces
the retained disk witnesses used by either exchange.
-/

set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel PLAnnularStrip

namespace PoincareMT.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_collar_exchange_component_domains
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) j)
    (hR : IsCompact R) (hRc : IsConnected R) (he : PLDomain e R)
    (hK : PLDomain e K) (hKc : IsConnected K) (hKR : K ⊆ interior R)
    (B : Bool → Set X) (sB : ∀ b, ChartwisePLSphere e (B b))
    (hBdis : Disjoint (B false) (B true)) (hfront : frontier K = B false ∪ B true)
    (hsmall : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (interior R))
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (hDPL : PLDomain e (K ∪ P.closedStrip))
    (hDfront : frontier (K ∪ P.closedStrip) = (frontier K \ P.openStrip) ∪ P.endDisks)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (N.space ×ˢ Icc (-1 : ℝ) 1))
    (hci : InjOn c (N.space ×ˢ Icc (-1 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1)
    (hKeq : K = c '' (N.space ×ˢ Icc (-ε) ε))
    (hBeq : ∀ a, B a = c '' (N.space ×ˢ {if a then ε else -ε})) :
    ∃ (owner : Bool) (F : V3 × ℝ → X) (g : P2 → V3)
      (k q : Bool → Set V3) (C : Bool → Set (V3 × ℝ))
      (p : Fin 3 → Set X) (sp : ∀ i, ChartwisePLSphere e (p i))
      (a : Fin 3 → X) (D : Fin 3 → Set X),
      PolyhedralPLInCharts e F (Sphere ×ˢ I) ∧ InjOn F (Sphere ×ˢ I) ∧
      F '' (Sphere ×ˢ I) = K ∧
      (∀ x ∈ Sphere, F (x, 1) = (sB owner).map x) ∧
      F '' (Sphere ×ˢ {(0 : ℝ)}) = B (!owner) ∧
      (∀ d, P.map '' (Rim ×ˢ J) ⊆ B d ↔ d = owner) ∧
      FinitePiecewiseAffineOn g (squareAnnulus 8 1) ∧
      (sB owner).map '' (g '' squareAnnulus 8 1) = P.map '' (Rim ×ˢ J) ∧
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
        D i = connectedComponentIn P.cutCarrier (a i)) ∧
      (∀ i, IsCompact (D i) ∧ PLDomain e (D i) ∧ IsConnected (D i) ∧
        D i ⊆ P.cutCarrier ∧ p i ⊆ D i) ∧
      P.cutCarrier = ⋃ i, D i ∧
      (∀ i j, D i = D j ∨ Disjoint (D i) (D j)) ∧
      (∀ i, frontier (D i) = (D i ∩ frontier R) ∪ ⋃ j ∈ {j | D j = D i}, p j) ∧
      (∀ i, D i ∩ (K ∪ P.closedStrip) = ⋃ j ∈ {j | D j = D i}, p j) ∧
      (∀ x ∈ P.cutCarrier, ∃ i, connectedComponentIn P.cutCarrier x = D i) ∧
      ((∀ i j, D i = D j) ∨
        (D 0 = D 1 ∧ D 0 ≠ D 2 ∧ D 1 ≠ D 2) ∨
        (D 0 = D 2 ∧ D 0 ≠ D 1 ∧ D 1 ≠ D 2) ∨
        (D 1 = D 2 ∧ D 0 ≠ D 1 ∧ D 0 ≠ D 2) ∨
        (D 0 ≠ D 1 ∧ D 0 ≠ D 2 ∧ D 1 ≠ D 2)) ∧
      ∀ b,
        let A := Sphere \ (k b \ q b)
        ∃ (W : ((F '' (A ×ˢ I)) ∪ P.closedStrip : Set X) ≃ₜ
            (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ))) (σ : P3 × ℝ → X),
          PolyhedralPLInCharts e σ (frontier (halfBall 1) ×ˢ I) ∧
          (∀ z : (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)), σ z = (W.symm z : X)) ∧
          (∀ x : ((F '' (A ×ˢ I)) ∪ P.closedStrip : Set X),
            (x : X) ∈ (F '' C b) ∪ P.capDisk b ↔
              (W x : P3 × ℝ).2 = if b then (1 : ℝ) else 0) ∧
          (∀ x : ((F '' (A ×ˢ I)) ∪ P.closedStrip : Set X),
            (x : X) ∈ p (if b then 1 else 2) ↔
              (W x : P3 × ℝ).2 = if !b then (1 : ℝ) else 0) ∧
          PLDomain e ((F '' (A ×ˢ I)) ∪ P.closedStrip) ∧
          frontier ((F '' (A ×ˢ I)) ∪ P.closedStrip) =
            ((F '' C b) ∪ P.capDisk b) ∪ p (if b then 1 else 2) := by
  classical
  obtain ⟨owner, F, g, k, q, C, hF, hFi, hFK, htop, hbottom, howner,
      hg, _, hgimage, hk, hkd, hcover, hproducts⟩ :=
    P.exists_original_collar_exchanges B sB hR he (hKR.trans interior_subset)
      hBdis rfl hfront hsmall hstripK N hN c hc hci hε hεle hKeq hBeq
  obtain ⟨hkfull, _, _, _, _, hnewdis, hnewopp, hports⟩ :=
    P.three_connected_ports_of_retained_disks hR he hK hKR B sB hBdis hfront
      hsmall hstripK owner k q howner
      (fun b => ⟨(hk b).1, (hk b).2.1, (hk b).2.2.2.1, (hk b).2.2.2.2⟩)
      (fun b => (hk b).2.2.1) hkd hcover
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
  obtain ⟨a, D, ha, hD, hexhaust, hdis, hDfrontier, hDattach, hactual, hcases⟩ :=
    hQPL.exists_three_port_component_domains hQc hDPL.closed hDconn hwhole p hpconn hQports
  have hfrontiers (i : Fin 3) : frontier (D i) =
      (D i ∩ frontier R) ∪ ⋃ j ∈ {j | D j = D i}, p j := by
    rw [hDfrontier i, hQfront, hports, hunion, inter_union_distrib_left, union_comm]
    congr 1
    rw [← hQports, ← inter_assoc, inter_eq_left.mpr (hD i).2.2.2.1, hDattach]
  refine ⟨owner, F, g, k, q, C, p, sp, a, D, hF, hFi, hFK, htop, hbottom, howner, hg, hgimage,
    hkfull, rfl, hpdis, hportfront, ha, hD, hexhaust, hdis, hfrontiers, hDattach,
    hactual, hcases, ?_⟩
  intro b
  obtain ⟨W, σ, hσ, hσval, hfirst, hsecond, hWfront⟩ := hproducts b
  refine ⟨W, σ, hσ, hσval, hfirst, ?_,
    original_sphere_product_plDomain W σ hσ hσval he.compatible he.cover, ?_⟩
  · intro x
    cases b
    · exact hsecond x
    · exact hsecond x
  · cases b
    · exact hWfront
    · exact hWfront

end PoincareMT.M76.OriginalDiskProduct
