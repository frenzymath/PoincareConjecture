import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.SourceDiskPhases
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.SourceFamilyInstallation

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

structure HamiltonZeroTerminalThirdPhaseData {ι : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (R : Set X0)
    (psi : C(H0, H0)) (a b : ℝ) : Prop where
  geometry : HamiltonZeroThirdPhaseGeometry e R psi a b
  boundary : ∀ xi : C0, (frontier R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {xi}).Nonempty
  irreducible : ∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
    AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b))
  disks : ∀ t ∈ ({a, b} : Set ℝ),
    let S := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(t : C0)}
    ∃ (n : ℕ) (T : Fin n → Set X0),
      (⋃ i, T i) = S ∧ Pairwise (fun i k => Disjoint (T i) (T k)) ∧
      ∀ i, IsCompact (T i) ∧ IsPathConnected (T i) ∧
        (∀ x ∈ T i, connectedComponentIn S x = T i) ∧
        ∃ (H : D ≃ₜ T i) (k : V2 → X0), PolyhedralPLInCharts e k D ∧
          Topology.IsEmbedding (fun z : D => k z) ∧ MapsTo k D R ∧
          (∀ z : D, k z = (H z : X0)) ∧ k '' D = T i ∧
          ∀ z : D, k z ∈ frontier R ↔ (z : V2) ∈ Q

def HamiltonZeroTerminalThirdHierarchy {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (phi : C(H0, H0)) (R : Set X0) : Prop :=
  ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
    (∀ t ∈ ({a, b} : Set ℝ), HamiltonZeroThirdCoordinateRegularity e R phi (t : C0)) ∧
    ∃ (psi : C(H0, H0)) (A : Set X0), IsCompact A ∧ A ⊆ interior R ∧
      (∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ) ∧
      HamiltonZeroTerminalThirdPhaseData e R psi a b

def HamiltonZeroThirdComponentHierarchy {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (phi : C(H0, H0)) (R : Set X0) : Prop :=
  ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
    (∀ t ∈ ({a, b} : Set ℝ), HamiltonZeroThirdCoordinateRegularity e R phi (t : C0)) ∧
    ∃ (psi : C(H0, H0)) (A : Set X0), IsCompact A ∧ A ⊆ interior R ∧
      (∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ) ∧
      (∀ side : Bool,
        let N := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
          AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
        PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
          ((R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(a : C0)}) ∪
            (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(b : C0)})) ∧
        ∀ t ∈ ({a, b} : Set ℝ),
          ∃ hSN : R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(t : C0)} ⊆ N,
            ∀ x, Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSN) x)) ∧
      (∀ xi : C0, (frontier R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {xi}).Nonempty) ∧
      ∀ t ∈ ({a, b} : Set ℝ),
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

theorem HamiltonZeroTerminalThirdHierarchy.to_componentHierarchy
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3} {phi : C(H0, H0)} {R : Set X0}
    (h : HamiltonZeroTerminalThirdHierarchy e d phi R) :
    HamiltonZeroThirdComponentHierarchy e d phi R := by
  obtain ⟨a, ha, b, hb, hreg, psi, A, hA, hAR, hfixed, hfirst, hsecond,
    hPL, H, F, G, terminal⟩ := h
  refine ⟨a, ha, b, hb, hreg, psi, A, hA, hAR, hfixed, hfirst, hsecond,
    hPL, H, F, G, terminal.geometry.slabs, terminal.boundary, ?_⟩
  intro t ht
  obtain ⟨n, T, hcover, hdis, hprops⟩ := terminal.disks t ht
  refine ⟨n, T, hcover, hdis, ?_⟩
  intro i
  exact ⟨(hprops i).1, (hprops i).2.1, (hprops i).2.2.1, Or.inl (hprops i).2.2.2⟩

theorem hamiltonZero_installed_second_slabs_terminal_third_hierarchies
    {ι κ : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (chi : C(H0, H0))
    (hchi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi))
    (Fchi : (ContinuousMap.id H0).HomotopyRel chi B0)
    {R : Set X0} (heR : PLDomain e R)
    (hinjR : ∀ x : R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) x))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (geometry : HamiltonZeroSecondPhaseGeometry e R chi a b)
    (hcuts : ∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)))
    (hinj : ∀ side : Bool,
      let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      ∀ x : N, Function.Injective
        (FundamentalGroup.map (ContinuousMap.inclusion (inter_subset_left : N ⊆ R)) x))
    (hboundary : (frontier R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {(a : C0)}).Nonempty)
    (n : Bool → ℕ) (j : (Σ s : Bool, Fin (n s)) → ℝ × ℝ → X0)
    (hfamily : ∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Ann) =
      R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {((if s then b else a : ℝ) : C0)})
    (hnormal : ∀ i, ∃ (delta0 delta1 : ℝ) (c : C(Ann, unitInterval × C0)),
      IsCoveringMap c ∧ ∀ z : Ann, hamiltonZeroAmbientMap chi (j i z) =
        hamiltonZeroAnnulusTargetMap delta0 delta1 ((if i.1 then b else a : ℝ) : C0) (c z))
    {cut alpha beta : ℝ} (halpha : cut < alpha) (hbeta : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap chi ⁻¹' AddCircle.closedIntervalArc p alpha beta) :
    ∀ side : Bool, HamiltonZeroTerminalThirdHierarchy e d chi
      (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)) := by
  obtain ⟨x, hxfront, hxphase⟩ := hboundary
  have hxR : x ∈ R := heR.closed.frontier_subset hxfront
  have hxfamily : x ∈ ⋃ i : Fin (n false), j ⟨false, i⟩ '' Ann := by
    rw [hfamily]
    exact ⟨hxR, hxphase⟩
  obtain ⟨i, _⟩ := mem_iUnion.mp hxfamily
  obtain ⟨delta0, delta1, c, hc, hvalue⟩ := hnormal ⟨false, i⟩
  have hjphase : j ⟨false, i⟩ '' Ann ⊆ R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {(a : C0)} := by
    have hfamily0 : (⋃ k : Fin (n false), j ⟨false, k⟩ '' Ann) =
        R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {(a : C0)} := by simpa using hfamily false
    rw [← hfamily0]
    exact subset_iUnion (fun i : Fin (n false) => j ⟨false, i⟩ '' Ann) i
  intro side
  let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
    AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
  have hjfront : j ⟨false, i⟩ '' Ann ⊆ frontier N := by
    rw [(geometry.slabs side).2.1]
    exact hjphase.trans (subset_union_left.trans subset_union_right)
  have hinjN : ∀ x : N, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(N, X0)) x) := by
    let inclusion := ContinuousMap.inclusion (inter_subset_left : N ⊆ R)
    let ambient : C(R, X0) := ⟨Subtype.val, continuous_subtype_val⟩
    intro x
    change Function.Injective (FundamentalGroup.map (ambient.comp inclusion) x)
    rw [FundamentalGroup.map_comp]
    exact (hinjR (inclusion x)).comp (hinj side x)
  have hfirst : N ⊆ hamiltonZeroCircleMap chi ⁻¹' AddCircle.closedIntervalArc p alpha beta :=
    inter_subset_left.trans hR
  cases side
  · obtain ⟨u, hu, v, hv, hreg, psi, A, hA, hAR, hfixed, hfirstEq, hsecondEq,
        hPL, H, F, G, geom, hboundary, hI, hdisks⟩ :=
      exists_hamiltonZero_terminal_third_disk_families e d hd chi hchi Fchi (hcuts false)
        hinjN halpha hbeta (cut' := 0) ha (by change b < 0 + p; linarith) hfirst inter_subset_right
        (j ⟨false, i⟩) hjfront c hc delta0 delta1 (a : C0) hvalue
    exact ⟨u, hu, v, hv, hreg, psi, A, hA, hAR, hfixed, hfirstEq, hsecondEq,
      hPL, H, F, G, ⟨geom, hboundary, hI, hdisks⟩⟩
  · obtain ⟨u, hu, v, hv, hreg, psi, A, hA, hAR, hfixed, hfirstEq, hsecondEq,
        hPL, H, F, G, geom, hboundary, hI, hdisks⟩ :=
      exists_hamiltonZero_terminal_third_disk_families e d hd chi hchi Fchi (hcuts true)
        hinjN halpha hbeta (cut' := (a + b) / 2)
        (by change (a + b) / 2 < b; linarith) (by change a + p < (a + b) / 2 + p; linarith)
        hfirst inter_subset_right (j ⟨false, i⟩) hjfront c hc delta0 delta1 (a : C0) hvalue
    exact ⟨u, hu, v, hv, hreg, psi, A, hA, hAR, hfixed, hfirstEq, hsecondEq,
      hPL, H, F, G, ⟨geom, hboundary, hI, hdisks⟩⟩

theorem hamiltonZero_installed_second_slabs_third_component_hierarchies
    {ι κ : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (chi : C(H0, H0))
    (hchi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi))
    (Fchi : (ContinuousMap.id H0).HomotopyRel chi B0)
    {R : Set X0} (heR : PLDomain e R)
    (hinjR : ∀ x : R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) x))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (geometry : HamiltonZeroSecondPhaseGeometry e R chi a b)
    (hcuts : ∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)))
    (hinj : ∀ side : Bool,
      let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      ∀ x : N, Function.Injective
        (FundamentalGroup.map (ContinuousMap.inclusion (inter_subset_left : N ⊆ R)) x))
    (hboundary : (frontier R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {(a : C0)}).Nonempty)
    (n : Bool → ℕ) (j : (Σ s : Bool, Fin (n s)) → ℝ × ℝ → X0)
    (hfamily : ∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Ann) =
      R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {((if s then b else a : ℝ) : C0)})
    (hnormal : ∀ i, ∃ (delta0 delta1 : ℝ) (c : C(Ann, unitInterval × C0)),
      IsCoveringMap c ∧ ∀ z : Ann, hamiltonZeroAmbientMap chi (j i z) =
        hamiltonZeroAnnulusTargetMap delta0 delta1 ((if i.1 then b else a : ℝ) : C0) (c z))
    {cut alpha beta : ℝ} (halpha : cut < alpha) (hbeta : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap chi ⁻¹' AddCircle.closedIntervalArc p alpha beta) :
    ∀ side : Bool, HamiltonZeroThirdComponentHierarchy e d chi
      (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)) := by
  intro side
  exact (hamiltonZero_installed_second_slabs_terminal_third_hierarchies e d hd chi hchi Fchi
    heR hinjR ha hab hb geometry hcuts hinj hboundary n j hfamily hnormal halpha hbeta hR side).to_componentHierarchy

theorem exists_hamiltonZero_source_second_slabs_third_hierarchies
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
      (Q0 (hamiltonZeroAmbientMap phi (c (x, t)))).1 = g x) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      (∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroSecondCoordinateRegularity e R phi (theta : C0)) ∧
      ∃ (chi : C(H0, H0)) (n : Bool → ℕ) (j : (Σ s : Bool, Fin (n s)) → ℝ × ℝ → X0),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi) ∧
        Nonempty (phi.HomotopyRel chi B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel chi B0) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap chi) (interior R)ᶜ) ∧
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
        (∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Ann) =
          R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {((if s then b else a : ℝ) : C0)}) ∧
        Pairwise (fun i k => Disjoint (j i '' Ann) (j k '' Ann)) ∧
        (∀ i, PolyhedralPLInCharts e (j i) Ann ∧
          Topology.IsEmbedding (fun z : Ann => j i z) ∧
          (∀ z : Ann, depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
            j i z ∈ frontier R) ∧
          (∃ delta0 ∈ ({alpha, beta} : Set ℝ), ∃ delta1 ∈ ({alpha, beta} : Set ℝ),
            ∃ f : C(Ann, unitInterval × C0), IsCoveringMap f ∧
              (∀ z : Ann, hamiltonZeroAmbientMap chi (j i z) =
                hamiltonZeroAnnulusTargetMap delta0 delta1
                  ((if i.1 then b else a : ℝ) : C0) (f z)) ∧
              HamiltonZeroInstalledAnnulusPLArcFibers e R (j i) chi f)) ∧
        ∀ side : Bool, HamiltonZeroThirdComponentHierarchy e d chi
          (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)) := by
  obtain ⟨a, ha', b, hb', hreg, chi, n, j, hchi, Hchi, ⟨Fchi⟩, Hext,
      hRchi, geometry, hcuts, hinj, hboundary, hfamily, hdis, hnormal⟩ :=
    exists_hamiltonZero_source_annulus_family_installation e d hd phi hphi F0 hI
      ha hab hb hR hRfront hinjR hK hne hr c hc hi ho hzero hside g hg hproduct
  refine ⟨a, ha', b, hb', hreg, chi, n, j, hchi, Hchi, ⟨Fchi⟩, Hext,
    hRchi, geometry, hcuts, hinj, hboundary, hfamily, hdis, hnormal, ?_⟩
  apply hamiltonZero_installed_second_slabs_third_component_hierarchies e d hd chi hchi Fchi
    hI.1 hinjR (by linarith [ha'.1]) (by linarith [ha'.2, hb'.1])
    (by linarith [hb'.2]) geometry hcuts hinj (hboundary a) n j hfamily
    ?_ ha hb hRchi
  intro i
  obtain ⟨delta0, _, delta1, _, f, hf, hvalue, _⟩ := (hnormal i).2.2.2
  exact ⟨delta0, delta1, f, hf, hvalue⟩

theorem exists_hamiltonZero_source_second_slabs_terminal_hierarchies
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
      (Q0 (hamiltonZeroAmbientMap phi (c (x, t)))).1 = g x) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      (∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroSecondCoordinateRegularity e R phi (theta : C0)) ∧
      ∃ chi : C(H0, H0),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi) ∧
        Nonempty (phi.HomotopyRel chi B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel chi B0) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap chi) (interior R)ᶜ) ∧
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
        ∀ side : Bool, HamiltonZeroTerminalThirdHierarchy e d chi
          (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)) := by
  obtain ⟨a, ha', b, hb', hreg, chi, n, j, hchi, Hchi, ⟨Fchi⟩, Hext,
      hRchi, geometry, hcuts, hinj, hboundary, hfamily, _, hnormal⟩ :=
    exists_hamiltonZero_source_annulus_family_installation e d hd phi hphi F0 hI
      ha hab hb hR hRfront hinjR hK hne hr c hc hi ho hzero hside g hg hproduct
  refine ⟨a, ha', b, hb', hreg, chi, hchi, Hchi, ⟨Fchi⟩, Hext,
    hRchi, geometry, hcuts, hinj, hboundary, ?_⟩
  apply hamiltonZero_installed_second_slabs_terminal_third_hierarchies e d hd chi hchi Fchi
    hI.1 hinjR (by linarith [ha'.1]) (by linarith [ha'.2, hb'.1])
    (by linarith [hb'.2]) geometry hcuts hinj (hboundary a) n j hfamily
    ?_ ha hb hRchi
  intro i
  obtain ⟨delta0, _, delta1, _, f, hf, hvalue, _⟩ := (hnormal i).2.2.2
  exact ⟨delta0, delta1, f, hf, hvalue⟩

end PoincareConjecture.M76
