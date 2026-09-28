import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.InstalledSecondSlabHierarchy
import PoincareConjecture.Proofs.M76.RelativeApproximation.ChartwiseRestriction










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "R0" => latticeHandleDomain (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => Metric.closedBall (0 : V2) 1
local notation "Q" => Metric.sphere (0 : V2) 1

theorem hamiltonZero_second_slabs_separated
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {R : Set X0} {phi : C(H0, H0)} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < p)
    (geometry : HamiltonZeroSecondPhaseGeometry e R phi a b) :
    ∀ s : Bool,
      let N := fun s : Bool => R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)
      N s ⊆ (interior (N (!s)))ᶜ := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let N := fun s : Bool => R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
    AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)
  have h10 : N true ⊆ (interior (N false))ᶜ := by
    intro x hx hi
    have hxR : x ∈ interior R := interior_mono inter_subset_left hi
    exact (complementary_circle_slab_agrees_exterior (hamiltonZeroSecondCircleMap phi)
      ha hab (by simpa using hb) (geometry.slabs false).2.1 x hxR).mp hx hi
  have h01 : N false ⊆ (interior (N true))ᶜ := by
    have hreg : closure (interior (N false)) = N false := (geometry.slabs false).1.closure_interior
    rw [← hreg]
    apply closure_minimal _ isOpen_interior.isClosed_compl
    intro x hx hi
    exact h10 (interior_subset hi) hx
  intro s
  cases s
  · exact h01
  · exact h10

theorem exists_hamiltonZero_disjoint_slab_installation
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (psi : Bool → C(H0, H0)) (N A : Bool → Set X0)
    (hN : ∀ s, IsClosed (N s))
    (hsep : ∀ s, N s ⊆ (interior (N (!s)))ᶜ)
    (hA : ∀ s, IsCompact (A s)) (hAN : ∀ s, A s ⊆ interior (N s))
    (hfixed : ∀ s x, x ∉ A s → hamiltonZeroAmbientMap (psi s) x = hamiltonZeroAmbientMap phi x)
    (hPL : ∀ s, ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 (psi s)))
    (hfirst : ∀ s, hamiltonZeroCircleMap (psi s) = hamiltonZeroCircleMap phi)
    (hsecond : ∀ s, hamiltonZeroSecondCircleMap (psi s) = hamiltonZeroSecondCircleMap phi)
    (H : ∀ s, (hamiltonZeroAmbientMap phi).HomotopyRel
      (hamiltonZeroAmbientMap (psi s)) (interior (N s))ᶜ)
    {R : Set X0} (hNR : ∀ s, N s ⊆ R) :
    ∃ chi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi) ∧
      Nonempty (phi.HomotopyRel chi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel chi B0) ∧
      hamiltonZeroCircleMap chi = hamiltonZeroCircleMap phi ∧
      hamiltonZeroSecondCircleMap chi = hamiltonZeroSecondCircleMap phi ∧
      (∀ s, EqOn (hamiltonZeroAmbientMap chi) (hamiltonZeroAmbientMap (psi s)) (N s)) ∧
      IsCompact (A false ∪ A true) ∧ (A false ∪ A true) ⊆ interior R ∧
      (∀ x ∉ A false ∪ A true, hamiltonZeroAmbientMap chi x = hamiltonZeroAmbientMap phi x) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap chi) (interior R)ᶜ,
        ∀ s t x, x ∈ N s → G (t, x) = H s (t, x) := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  have hfixedN (s : Bool) (x : X0) (hx : x ∈ N s) :
      hamiltonZeroAmbientMap (psi (!s)) x = hamiltonZeroAmbientMap phi x :=
    hfixed (!s) x (fun h => hsep s hx (hAN (!s) h))
  have hboundary (t : unitInterval) (x : X0) (hx : x ∈ frontier (N false)) :
      H false (t, x) = H true (t, x) := by
    have hx0 : x ∉ interior (N false) := fun hi =>
      disjoint_left.mp disjoint_interior_frontier hi hx
    have hx1 : x ∉ interior (N true) := hsep false ((hN false).frontier_subset hx)
    exact (H false).prop t x hx0 |>.trans ((H true).prop t x hx1).symm
  let G : C(unitInterval × X0, X0) :=
    ⟨(Prod.snd ⁻¹' N false).piecewise (H false) (H true),
      Continuous.piecewise
        (fun z hz => hboundary z.1 z.2 (continuous_snd.frontier_preimage_subset (N false) hz))
        (H false).continuous (H true).continuous⟩
  have hGzero (x : X0) : G (0, x) = hamiltonZeroAmbientMap phi x := by
    change (if x ∈ N false then H false (0, x) else H true (0, x)) = _
    split_ifs <;> exact ContinuousMap.Homotopy.map_zero_left _ _
  have hGside (s : Bool) (t : unitInterval) (x : X0) (hx : x ∈ N s) :
      G (t, x) = H s (t, x) := by
    change (if x ∈ N false then H false (t, x) else H true (t, x)) = _
    cases s
    · simp only [hx, if_true]
    · split_ifs with hx0
      · exact ((H false).prop t x (hsep true hx)).trans
          ((H true).prop t x (hsep false hx0)).symm
      · rfl
  let g : C(X0, X0) := ⟨fun x => G (1, x),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let chi := hamiltonZeroHandleMap g
  have hg (x : X0) : hamiltonZeroAmbientMap chi x = g x := by
    rw [hamiltonZeroAmbientMap_handle]
  have hgon (s : Bool) : EqOn g (hamiltonZeroAmbientMap (psi s)) (N s) := by
    intro x hx
    exact (hGside s 1 x hx).trans ((H s).map_one_left x)
  have hgoff : EqOn g (hamiltonZeroAmbientMap (psi true)) (A false)ᶜ := by
    intro x hx
    change (if x ∈ N false then H false (1, x) else H true (1, x)) = _
    split_ifs with hxN
    · exact ((H false).map_one_left x).trans
        ((hfixed false x hx).trans (hfixedN false x hxN).symm)
    · exact (H true).map_one_left x
  have hgPL : ChartwisePLMap e d (hamiltonZeroAmbientMapInDomain g) := by
    have hlocal (x : R0) : ∃ U : Set R0,
        ChartwisePLOn e d (hamiltonZeroAmbientMapInDomain g) U ∧ x ∈ U := by
      by_cases hx : (x : X0) ∈ A false
      · let U : Set R0 := Subtype.val ⁻¹' interior (N false)
        refine ⟨U, (hPL false).congr_mono
          (isOpen_interior.preimage continuous_subtype_val) (subset_univ _) ?_, hAN false hx⟩
        intro y hy
        rw [← hamiltonZeroAmbientMapInDomain_original]
        exact Subtype.ext (hgon false (interior_subset hy)).symm
      · let U : Set R0 := Subtype.val ⁻¹' (A false)ᶜ
        refine ⟨U, (hPL true).congr_mono
          ((hA false).isClosed.isOpen_compl.preimage continuous_subtype_val) (subset_univ _) ?_, hx⟩
        intro y hy
        rw [← hamiltonZeroAmbientMapInDomain_original]
        exact Subtype.ext (hgoff hy).symm
    refine ⟨(hPL false).source_domain, (hPL false).target_domain, isOpen_univ, ?_⟩
    intro x _
    obtain ⟨U, hU, hx⟩ := hlocal x
    obtain ⟨i, j, K, V, f, hK, hV, hxV, _, hVi, hVK, hKt, hKU, hf, hvalue⟩ :=
      hU.coordinates x hx
    refine ⟨i, j, K, V, f, hK, hV, hxV, subset_univ _, hVi, hVK, hKt, ?_, hf, hvalue⟩
    intro z hz
    obtain ⟨y, _, hy⟩ := hKU hz
    exact ⟨y, mem_univ _, hy⟩
  have hselect (x : X0) : ∃ s : Bool, g x = hamiltonZeroAmbientMap (psi s) x := by
    by_cases hx : x ∈ N false
    · exact ⟨false, hgon false hx⟩
    · refine ⟨true, ?_⟩
      change (if x ∈ N false then H false (1, x) else H true (1, x)) = _
      rw [if_neg hx]
      exact (H true).map_one_left x
  refine ⟨chi, ?_, ⟨hamiltonZeroHandleHomotopy phi G hGzero⟩,
    ⟨F.trans (hamiltonZeroHandleHomotopy phi G hGzero)⟩, ?_, ?_, ?_,
    (hA false).union (hA true), ?_, ?_, ?_⟩
  · rw [hamiltonZeroHandleMap_domain]
    exact hgPL
  · ext x
    obtain ⟨s, hs⟩ := hselect x
    rw [← hamiltonZeroAmbientMap_circle, hg, hs, hamiltonZeroAmbientMap_circle, hfirst]
  · ext x
    obtain ⟨s, hs⟩ := hselect x
    rw [hamiltonZeroSecondCircleMap_ambient, hg, hs, ← hamiltonZeroSecondCircleMap_ambient, hsecond]
  · intro s x hx
    exact (hg x).trans (hgon s hx)
  · exact union_subset
      ((hAN false).trans (interior_mono (hNR false)))
      ((hAN true).trans (interior_mono (hNR true)))
  · intro x hx
    obtain ⟨s, hs⟩ := hselect x
    refine (hg x).trans (hs.trans (hfixed s x ?_))
    cases s
    · exact fun h => hx (Or.inl h)
    · exact fun h => hx (Or.inr h)
  · refine ⟨{
      toFun := G
      continuous_toFun := G.continuous
      map_zero_left := hGzero
      map_one_left := fun x => (hg x).symm
      prop' := ?_ }, hGside⟩
    intro t x hx
    change (if x ∈ N false then H false (t, x) else H true (t, x)) = _
    split_ifs
    · exact (H false).prop t x (fun h => hx (interior_mono (hNR false) h))
    · exact (H true).prop t x (fun h => hx (interior_mono (hNR true) h))




structure HamiltonZeroThirdPhaseComponents {ι : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (R : Set X0)
    (psi : C(H0, H0)) (a b : ℝ) : Prop where
  slabs : ∀ side : Bool,
    let N := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
    PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
      ((R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(a : C0)}) ∪
        (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(b : C0)})) ∧
    ∀ t ∈ ({a, b} : Set ℝ),
      ∃ hSN : R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(t : C0)} ⊆ N,
        ∀ x, Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSN) x)
  boundary : ∀ xi : C0, (frontier R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {xi}).Nonempty
  components : ∀ t ∈ ({a, b} : Set ℝ),
    let S := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(t : C0)}
    ∃ (n : ℕ) (T : Fin n → Set X0),
      (⋃ i, T i) = S ∧ Pairwise (fun i k => Disjoint (T i) (T k)) ∧
      ∀ i, IsCompact (T i) ∧ IsPathConnected (T i) ∧
        (∀ x ∈ T i, connectedComponentIn S x = T i) ∧
        ((∃ (H : D ≃ₜ T i) (k : V2 → X0), PolyhedralPLInCharts e k D ∧
          Topology.IsEmbedding (fun z : D => k z) ∧ MapsTo k D R ∧
          (∀ z : D, k z = (H z : X0)) ∧ k '' D = T i ∧
          ∀ z : D, k z ∈ frontier R ↔ (z : V2) ∈ Q) ∨
        (Disjoint (T i) (frontier R) ∧ Nonempty (ChartwisePLSphere e (T i)) ∧
          ∃ B : Set X0, IsCompact B ∧ B ⊆ interior R ∧
            Nonempty (ChartwisePLBall e B (T i))))

theorem HamiltonZeroThirdPhaseComponents.congr
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    {phi psi : C(H0, H0)} {a b : ℝ}
    (h : HamiltonZeroThirdPhaseComponents e R phi a b) (hR : IsClosed R)
    (heq : EqOn (hamiltonZeroAmbientMap psi) (hamiltonZeroAmbientMap phi) R) :
    HamiltonZeroThirdPhaseComponents e R psi a b := by
  have hthird (x : X0) (hx : x ∈ R) :
      hamiltonZeroThirdCircleMap psi x = hamiltonZeroThirdCircleMap phi x := by
    rw [hamiltonZeroThirdCircleMap_ambient, heq hx, ← hamiltonZeroThirdCircleMap_ambient]
  have hsets (T : Set C0) :
      R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' T = R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' T := by
    ext x
    by_cases hx : x ∈ R
    · simp only [mem_inter_iff, mem_preimage, hthird x hx]
    · simp only [mem_inter_iff, hx, false_and]
  refine ⟨?_, ?_, ?_⟩
  · intro s
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hsets] using (h.slabs s).1
    · simpa only [hsets] using (h.slabs s).2.1
    · intro t ht
      have transfer {S T S' T' : Set X0} (hS : S = S') (hT : T = T')
          (hi : ∃ hST : S' ⊆ T', ∀ x,
            Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hST) x)) :
          ∃ hST : S ⊆ T, ∀ x,
            Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hST) x) := by
        subst S'
        subst T'
        exact hi
      exact transfer (hsets {(t : C0)})
        (hsets (AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)))
        ((h.slabs s).2.2 t ht)
  · intro xi
    obtain ⟨x, hx, hxi⟩ := h.boundary xi
    exact ⟨x, hx, by simpa only [mem_preimage, hthird x (hR.frontier_subset hx)] using hxi⟩
  · intro t ht
    simpa only [hsets] using h.components t ht

theorem exists_hamiltonZero_simultaneous_second_slab_hierarchies
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (geometry : HamiltonZeroSecondPhaseGeometry e R phi a b)
    (h : ∀ s : Bool, HamiltonZeroThirdComponentHierarchy e d phi
      (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b))) :
    ∃ (chi : C(H0, H0)) (A : Set X0),
      IsCompact A ∧ A ⊆ interior R ∧
      (∀ x ∉ A, hamiltonZeroAmbientMap chi x = hamiltonZeroAmbientMap phi x) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi) ∧
      Nonempty (phi.HomotopyRel chi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel chi B0) ∧
      Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap chi) (interior R)ᶜ) ∧
      hamiltonZeroCircleMap chi = hamiltonZeroCircleMap phi ∧
      hamiltonZeroSecondCircleMap chi = hamiltonZeroSecondCircleMap phi ∧
      ∀ s : Bool,
        let N := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
          AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)
        ∃ u ∈ Ioo (p / 4) (p / 3), ∃ v ∈ Ioo (2 * p / 3) (3 * p / 4),
          (∀ t ∈ ({u, v} : Set ℝ), HamiltonZeroThirdCoordinateRegularity e N phi (t : C0)) ∧
          HamiltonZeroThirdPhaseComponents e N chi u v := by
  classical
  let N := fun s : Bool => R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
    AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)
  change ∀ s, HamiltonZeroThirdComponentHierarchy e d phi (N s) at h
  choose u hu v hv hreg psi A hA hAN hfixed hfirst hsecond hPL _ _ HH hslabs hboundary hcomponents using h
  let H := fun s => Classical.choice (HH s)
  obtain ⟨chi, hchi, Hphi, Fchi, hfirstChi, hsecondChi, heq, hAc, hAR, hfixedChi, G, _⟩ :=
    exists_hamiltonZero_disjoint_slab_installation phi F psi N A
      (fun s => (geometry.slabs s).1.closed)
      (hamiltonZero_second_slabs_separated ha hab hb geometry)
      hA hAN hfixed hPL hfirst hsecond H (fun _ => inter_subset_left)
  refine ⟨chi, A false ∪ A true, hAc, hAR, hfixedChi, hchi, Hphi, Fchi, ⟨G⟩,
    hfirstChi, hsecondChi, ?_⟩
  intro s
  refine ⟨u s, hu s, v s, hv s, hreg s, ?_⟩
  exact (HamiltonZeroThirdPhaseComponents.mk (hslabs s) (hboundary s) (hcomponents s)).congr
    (geometry.slabs s).1.closed (heq s)

theorem HamiltonZeroTerminalThirdPhaseData.to_components
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    {psi : C(H0, H0)} {a b : ℝ} (h : HamiltonZeroTerminalThirdPhaseData e R psi a b) :
    HamiltonZeroThirdPhaseComponents e R psi a b := by
  refine ⟨h.geometry.slabs, h.boundary, ?_⟩
  intro t ht
  obtain ⟨n, T, hcover, hdis, hprops⟩ := h.disks t ht
  exact ⟨n, T, hcover, hdis, fun i =>
    ⟨(hprops i).1, (hprops i).2.1, (hprops i).2.2.1, Or.inl (hprops i).2.2.2⟩⟩

theorem HamiltonZeroTerminalThirdPhaseData.congr
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    {phi psi : C(H0, H0)} {a b : ℝ}
    (h : HamiltonZeroTerminalThirdPhaseData e R phi a b) (hR : IsClosed R)
    (heq : EqOn (hamiltonZeroAmbientMap psi) (hamiltonZeroAmbientMap phi) R) :
    HamiltonZeroTerminalThirdPhaseData e R psi a b := by
  have hsets (T : Set C0) :
      R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' T = R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' T := by
    ext x
    by_cases hx : x ∈ R
    · have hthird : hamiltonZeroThirdCircleMap psi x = hamiltonZeroThirdCircleMap phi x := by
        rw [hamiltonZeroThirdCircleMap_ambient, heq hx, ← hamiltonZeroThirdCircleMap_ambient]
      simp only [mem_inter_iff, mem_preimage, hthird]
    · simp only [mem_inter_iff, hx, false_and]
  have hcomponents := h.to_components.congr hR heq
  refine ⟨⟨hcomponents.slabs, ?_⟩, hcomponents.boundary, ?_, ?_⟩
  · intro t ht
    have transfer {S T : Set X0} (hST : S = T)
        (hi : ∀ x : T, Function.Injective (FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(T, X0)) x)) :
        ∀ x : S, Function.Injective (FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X0)) x) := by
      subst T
      exact hi
    exact transfer (hsets {(t : C0)}) (h.geometry.groups t ht)
  · intro s
    simpa only [hsets] using h.irreducible s
  · intro t ht
    simpa only [hsets] using h.disks t ht




def HamiltonZeroSupportedThirdRealization {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (phi : C(H0, H0)) (R : Set X0) (chi : C(H0, H0)) (a b : ℝ) : Prop :=
  ∃ (psi : C(H0, H0)) (A : Set X0), IsCompact A ∧ A ⊆ interior R ∧
    (∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
    hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
    hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi ∧
    ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
    Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
    Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ) ∧
    HamiltonZeroTerminalThirdPhaseData e R psi a b ∧
    EqOn (hamiltonZeroAmbientMap chi) (hamiltonZeroAmbientMap psi) R

theorem exists_hamiltonZero_simultaneous_terminal_second_slab_hierarchies
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (geometry : HamiltonZeroSecondPhaseGeometry e R phi a b)
    (h : ∀ s : Bool, HamiltonZeroTerminalThirdHierarchy e d phi
      (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b))) :
    ∃ (chi : C(H0, H0)) (A : Set X0),
      IsCompact A ∧ A ⊆ interior R ∧
      (∀ x ∉ A, hamiltonZeroAmbientMap chi x = hamiltonZeroAmbientMap phi x) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi) ∧
      Nonempty (phi.HomotopyRel chi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel chi B0) ∧
      Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap chi) (interior R)ᶜ) ∧
      hamiltonZeroCircleMap chi = hamiltonZeroCircleMap phi ∧
      hamiltonZeroSecondCircleMap chi = hamiltonZeroSecondCircleMap phi ∧
      ∀ s : Bool,
        let N := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
          AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)
        ∃ u ∈ Ioo (p / 4) (p / 3), ∃ v ∈ Ioo (2 * p / 3) (3 * p / 4),
          (∀ t ∈ ({u, v} : Set ℝ), HamiltonZeroThirdCoordinateRegularity e N phi (t : C0)) ∧
          HamiltonZeroTerminalThirdPhaseData e N chi u v ∧
          HamiltonZeroSupportedThirdRealization e d phi N chi u v := by
  classical
  let N := fun s : Bool => R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
    AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)
  change ∀ s, HamiltonZeroTerminalThirdHierarchy e d phi (N s) at h
  choose u hu v hv hreg psi A hA hAN hfixed hfirst hsecond hPL Hbase Hidentity HH terminal using h
  let H := fun s => Classical.choice (HH s)
  obtain ⟨chi, hchi, Hphi, Fchi, hfirstChi, hsecondChi, heq, hAc, hAR, hfixedChi, G, _⟩ :=
    exists_hamiltonZero_disjoint_slab_installation phi F psi N A
      (fun s => (geometry.slabs s).1.closed)
      (hamiltonZero_second_slabs_separated ha hab hb geometry)
      hA hAN hfixed hPL hfirst hsecond H (fun _ => inter_subset_left)
  refine ⟨chi, A false ∪ A true, hAc, hAR, hfixedChi, hchi, Hphi, Fchi, ⟨G⟩,
    hfirstChi, hsecondChi, ?_⟩
  intro s
  exact ⟨u s, hu s, v s, hv s, hreg s,
    (terminal s).congr (geometry.slabs s).1.closed (heq s),
    psi s, A s, hA s, hAN s, hfixed s, hfirst s, hsecond s, hPL s,
    Hbase s, Hidentity s, HH s, terminal s, heq s⟩




theorem exists_hamiltonZero_source_simultaneous_terminal_hierarchies
    {E ι κ : Type*} [TopologicalSpace E] [Zero E]
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F0 : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (hI : IsPLIrreducible e R)
    {cut alpha beta : ℝ}
    (ha : cut < alpha) (hab : alpha < beta) (hb : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hRfront : frontier R ⊆ hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)})
    (hinjR : ∀ x : R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) x))
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X0)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ioo (-r) r)))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hproduct : ∀ x : K, ∀ t ∈ Icc (-r) r,
      ((hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates)
        (hamiltonZeroAmbientMap phi (c (x, t)))).1 = g x) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      (∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroSecondCoordinateRegularity e R phi (theta : C0)) ∧
      ∃ (psi chi : C(H0, H0)) (A : Set X0),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
        Nonempty (phi.HomotopyRel psi B0) ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi) ∧
        Nonempty (phi.HomotopyRel chi B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel chi B0) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap chi) (interior R)ᶜ) ∧
        IsCompact A ∧ A ⊆ interior R ∧
        (∀ x ∉ A, hamiltonZeroAmbientMap chi x = hamiltonZeroAmbientMap psi x) ∧
        hamiltonZeroCircleMap chi = hamiltonZeroCircleMap psi ∧
        hamiltonZeroSecondCircleMap chi = hamiltonZeroSecondCircleMap psi ∧
        R ⊆ hamiltonZeroCircleMap chi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
        HamiltonZeroSecondPhaseGeometry e R chi a b ∧
        (∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
          AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b))) ∧
        (∀ side : Bool,
          let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
          ∀ x : N, Function.Injective
            (FundamentalGroup.map (ContinuousMap.inclusion (inter_subset_left : N ⊆ R)) x)) ∧
        (∀ theta : C0, (frontier R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {theta}).Nonempty) ∧
        ∀ side : Bool,
          let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
          ∃ u ∈ Ioo (p / 4) (p / 3), ∃ v ∈ Ioo (2 * p / 3) (3 * p / 4),
            (∀ t ∈ ({u, v} : Set ℝ), HamiltonZeroThirdCoordinateRegularity e N psi (t : C0)) ∧
            HamiltonZeroTerminalThirdPhaseData e N chi u v ∧
            HamiltonZeroSupportedThirdRealization e d psi N chi u v := by
  obtain ⟨a, ha', b, hb', hreg, psi, hpsi, ⟨Hpsi⟩, ⟨Fpsi⟩, ⟨Gpsi⟩,
      hRpsi, geometry, hcuts, hinj, hboundary, terminal⟩ :=
    exists_hamiltonZero_source_second_slabs_terminal_hierarchies e d hd phi hphi F0 hI
      ha hab hb hR hRfront hinjR hK hne hr c hc hi ho hzero hside g hg hproduct
  obtain ⟨chi, A, hA, hAR, hfixed, hchi, ⟨Hchi⟩, ⟨Fchi⟩, ⟨Gchi⟩,
      hfirst, hsecond, hterminal⟩ :=
    exists_hamiltonZero_simultaneous_terminal_second_slab_hierarchies psi Fpsi
      (by linarith [ha'.1]) (by linarith [ha'.2, hb'.1])
      (by linarith [hb'.2]) geometry terminal
  have hRchi : R ⊆ hamiltonZeroCircleMap chi ⁻¹' AddCircle.closedIntervalArc p alpha beta := by
    rw [hfirst]
    exact hRpsi
  refine ⟨a, ha', b, hb', hreg, psi, chi, A, hpsi, ⟨Hpsi⟩, hchi,
    ⟨Hpsi.trans Hchi⟩, ⟨Fchi⟩, ⟨Gpsi.trans Gchi⟩, hA, hAR, hfixed,
    hfirst, hsecond, hRchi,
    geometry.of_secondCircleMap_eq hsecond Fchi ha hab.le hb hRchi, ?_, ?_, ?_, ?_⟩
  · rw [hsecond]
    exact hcuts
  · rw [hsecond]
    exact hinj
  · rw [hsecond]
    exact hboundary
  · rw [hsecond]
    exact hterminal

end PoincareConjecture.M76
