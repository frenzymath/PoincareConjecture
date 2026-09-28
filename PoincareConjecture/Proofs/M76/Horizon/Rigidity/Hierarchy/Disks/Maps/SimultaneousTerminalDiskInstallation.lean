import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.TerminalDiskInstallation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.SimultaneousTerminalGroups
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.OriginalPhaseSelectionPL









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "R0" => latticeHandleDomain (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem chartwisePL_hamiltonZero_continuous_selection
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi psi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi))
    (g : C(X0, X0))
    (hselect : ∀ x, g x = hamiltonZeroAmbientMap phi x ∨ g x = hamiltonZeroAmbientMap psi x) :
    ChartwisePLMap e d (hamiltonZeroAmbientMapInDomain g) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  have hempty : ChartwisePLOn e d (hamiltonZeroAmbientMapInDomain g) ∅ :=
    hphi.congr_mono isOpen_empty (empty_subset _) (fun _ hx => hx.elim)
  apply chartwisePLMap_of_open_and_embedded_parameters (E := V3) e d
    (hamiltonZeroAmbientMapInDomain g) hempty
  intro x _
  obtain ⟨i, j, K, V, f, hK, hV, hxV, _, hVi, hVK, hKt, _, _, _⟩ :=
    hphi.coordinates x (mem_univ x)
  let q : V3 → R0 := fun z =>
    ⟨(e i).symm z, hamiltonZeroDomain_eq_univ.symm.subset (mem_univ _)⟩
  have hq : ContinuousOn q K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
      ((e i).symm.continuousOn.mono hKt)
  have hi : Topology.IsEmbedding (fun z : K.space => (e i).symm z) :=
    (e i).symm.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion hKt)
  have hiq : Topology.IsEmbedding (fun z : K.space => q z) :=
    hi.codRestrict R0 (fun _ => hamiltonZeroDomain_eq_univ.symm.subset (mem_univ _))
  have hxK : e i x ∈ K.space := hVK ⟨x, hxV, rfl⟩
  let z : K.space := ⟨e i x, hxK⟩
  have hqz : q z = x := Subtype.ext ((e i).left_inv (hVi hxV))
  have hVrange : V ⊆ range (fun z : K.space => q z) := by
    intro y hy
    exact ⟨⟨e i y, hVK ⟨y, hy, rfl⟩⟩, Subtype.ext ((e i).left_inv (hVi hy))⟩
  have hqPL : PolyhedralPLInCharts e (fun z => (q z : X0)) K.space :=
    polyhedralPLInCharts_of_one_chart_inverse K hK
      ((K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK) i hKt
  have h0 := hphi.polyhedralPL_hamiltonZeroAmbientMap_comp K hK hqPL
  have h1 := hpsi.polyhedralPL_hamiltonZeroAmbientMap_comp K hK hqPL
  have hg : PolyhedralPLInCharts d (fun z => g (q z)) K.space :=
    h0.continuous_selection hd.domain.cover hd.domain.compatible K hK h1
      (g.continuous.comp_continuousOn hqPL.continuousOn) (fun z _ => hselect (q z))
  exact ⟨K, q, z, hK, hq, hiq, hqz,
    Filter.mem_of_superset (hV.mem_nhds hxV) hVrange, hqPL, hg⟩

theorem exists_hamiltonZero_exterior_relative_slab_pasting
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (psi : Bool → C(H0, H0)) (N : Bool → Set X0)
    (hN : ∀ s, IsClosed (N s))
    (hsep : ∀ s, N s ⊆ (interior (N (!s)))ᶜ)
    (hPL : ∀ s, ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 (psi s)))
    (H : ∀ s, (hamiltonZeroAmbientMap phi).HomotopyRel
      (hamiltonZeroAmbientMap (psi s)) (interior (N s))ᶜ)
    {R : Set X0} (hNR : ∀ s, N s ⊆ R) :
    ∃ chi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi) ∧
      Nonempty (phi.HomotopyRel chi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel chi B0) ∧
      (∀ s, EqOn (hamiltonZeroAmbientMap chi) (hamiltonZeroAmbientMap (psi s)) (N s)) ∧
      (∀ x, ∃ s, hamiltonZeroAmbientMap chi x = hamiltonZeroAmbientMap (psi s) x) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap chi) (interior R)ᶜ,
        (∀ s t x, x ∈ N s → G (t, x) = H s (t, x)) ∧
        ∀ t x, ∃ s, G (t, x) = H s (t, x) := by
  classical
  have hboundary (t : unitInterval) (x : X0) (hx : x ∈ frontier (N false)) :
      H false (t, x) = H true (t, x) := by
    have hx0 : x ∉ interior (N false) := fun hi =>
      disjoint_left.mp disjoint_interior_frontier hi hx
    have hx1 : x ∉ interior (N true) := hsep false ((hN false).frontier_subset hx)
    exact ((H false).prop t x hx0).trans ((H true).prop t x hx1).symm
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
  have hGselect (t : unitInterval) (x : X0) : ∃ s, G (t, x) = H s (t, x) := by
    by_cases hx : x ∈ N false
    · exact ⟨false, by change (if x ∈ N false then _ else _) = _; rw [if_pos hx]⟩
    · exact ⟨true, by change (if x ∈ N false then _ else _) = _; rw [if_neg hx]⟩
  let g : C(X0, X0) := ⟨fun x => G (1, x),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let chi := hamiltonZeroHandleMap g
  have hg (x : X0) : hamiltonZeroAmbientMap chi x = g x := by
    rw [hamiltonZeroAmbientMap_handle]
  have hselect (x : X0) : ∃ s, g x = hamiltonZeroAmbientMap (psi s) x := by
    obtain ⟨s, hs⟩ := hGselect 1 x
    exact ⟨s, hs.trans ((H s).map_one_left x)⟩
  refine ⟨chi, ?_, ⟨hamiltonZeroHandleHomotopy phi G hGzero⟩,
    ⟨F.trans (hamiltonZeroHandleHomotopy phi G hGzero)⟩, ?_, ?_, ?_⟩
  · rw [hamiltonZeroHandleMap_domain]
    apply chartwisePL_hamiltonZero_continuous_selection hd (hPL false) (hPL true) g
    intro x
    obtain ⟨s, hs⟩ := hselect x
    cases s
    · exact Or.inl hs
    · exact Or.inr hs
  · intro s x hx
    exact (hg x).trans ((hGside s 1 x hx).trans ((H s).map_one_left x))
  · intro x
    obtain ⟨s, hs⟩ := hselect x
    exact ⟨s, (hg x).trans hs⟩
  · refine ⟨{
      toFun := G
      continuous_toFun := G.continuous
      map_zero_left := hGzero
      map_one_left := fun x => (hg x).symm
      prop' := ?_ }, hGside, hGselect⟩
    intro t x hx
    obtain ⟨s, hs⟩ := hGselect t x
    exact hs.trans ((H s).prop t x (fun h => hx (interior_mono (hNR s) h)))

theorem HamiltonZeroInstalledTerminalDiskFamily.congr_target
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3} {R : Set X0}
    {phi psi chi : C(H0, H0)} {a b alpha beta u v : ℝ}
    (h : HamiltonZeroInstalledTerminalDiskFamily e d R phi psi a b alpha beta u v)
    (hthird : hamiltonZeroThirdCircleMap chi = hamiltonZeroThirdCircleMap psi)
    (heq : EqOn (hamiltonZeroAmbientMap chi) (hamiltonZeroAmbientMap psi) R) :
    HamiltonZeroInstalledTerminalDiskFamily e d R phi chi a b alpha beta u v := by
  obtain ⟨n, j, first, second, q, hcover, hdis, hprops⟩ := h
  refine ⟨n, j, first, second, q, ?_, hdis, ?_⟩
  · simpa only [hthird] using hcover
  · intro i
    obtain ⟨hj, hji, hjR, hrim, hcompact, hconn, hcomp, hfirst, hsecond,
      hrange, hq, hcoords, hqrim, hvalue⟩ := hprops i
    exact ⟨hj, hji, hjR, hrim, hcompact, hconn, by simpa only [hthird] using hcomp,
      hfirst, hsecond, hrange, hq, hcoords, hqrim,
      fun z => (heq (hjR z.property)).trans (hvalue z)⟩



def HamiltonZeroInstalledSecondSlabDisks {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (R : Set X0) (phi psi : C(H0, H0)) (a b alpha beta : ℝ) : Prop :=
  ∀ side : Bool,
    let N := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
    N ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
    N ⊆ hamiltonZeroSecondCircleMap psi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b) ∧
    EqOn (hamiltonZeroAmbientMap psi) (hamiltonZeroAmbientMap phi) (frontier N) ∧
    ∃ u ∈ Ioo (p / 4) (p / 3), ∃ v ∈ Ioo (2 * p / 3) (3 * p / 4),
      HamiltonZeroTerminalThirdPhaseData e N psi u v ∧
      HamiltonZeroInstalledTerminalDiskFamily e d N phi psi u v alpha beta
        (if side then b else a) (if side then a + p else b) ∧
      ∀ thirdSide : Bool,
        let T := N ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
          AddCircle.closedIntervalArc p (if thirdSide then v else u) (if thirdSide then u + p else v)
        ∀ x : T, Subsingleton (FundamentalGroup T x)

theorem exists_hamiltonZero_simultaneous_terminal_disk_installation
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (geometry : HamiltonZeroSecondPhaseGeometry e R phi a b)
    {cut alpha beta : ℝ} (halpha : cut < alpha) (horder : alpha ≤ beta) (hbeta : beta < cut + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (terminal : ∀ side : Bool,
      let N := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      ∃ u ∈ Ioo (p / 4) (p / 3), ∃ v ∈ Ioo (2 * p / 3) (3 * p / 4),
        HamiltonZeroTerminalThirdPhaseData e N phi u v ∧
        ∀ thirdSide : Bool,
          let T := N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
            AddCircle.closedIntervalArc p (if thirdSide then v else u) (if thirdSide then u + p else v)
          ∀ x : T, Subsingleton (FundamentalGroup T x)) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi ∧
      R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
      HamiltonZeroInstalledSecondSlabDisks e d R phi psi a b alpha beta ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ,
        (∀ t x, (Q0 (G (t, x))).1.1 = hamiltonZeroThirdCircleMap phi x) ∧
        ∀ side : Bool, ∀ t x,
          x ∈ R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b) →
          (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (G (t, x))).1.2 ∈ AddCircle.closedIntervalArc p
            (if side then b else a) (if side then a + p else b) := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  let N := fun side : Bool => R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
    AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
  choose u hu v hv hterminal hgroups using terminal
  have hex (side : Bool) := by
    have hneq : (u side : C0) ≠ (v side : C0) := by
      intro heq
      have huv := (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (show u side ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith [(hu side).1, (hu side).2])
        (show v side ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith [(hv side).1, (hv side).2])).mp heq
      linarith [(hu side).2, (hv side).1]
    have hlow : (if side then (a + b) / 2 else 0) < (if side then b else a) := by
      cases side <;> dsimp <;> linarith
    have hordered : (if side then b else a) ≤ (if side then a + p else b) := by
      cases side <;> dsimp <;> linarith
    have hupp : (if side then a + p else b) < (if side then (a + b) / 2 else 0) + p := by
      cases side <;> dsimp <;> linarith
    exact exists_hamiltonZero_terminal_disk_family_installation hd hphi F
      (geometry.slabs side).1 hneq (hterminal side) halpha horder hbeta
      hlow hordered hupp (inter_subset_left.trans hfirst) inter_subset_right
  choose eta heta Heta Feta hthird hReta hSeta hterminalEta hfamily H hHthird hHarc using hex
  obtain ⟨psi, hpsi, Hpsi, Fpsi, heq, hselect, G, hGside, hGselect⟩ :=
    exists_hamiltonZero_exterior_relative_slab_pasting hd phi F eta N
      (fun s => (geometry.slabs s).1.closed)
      (hamiltonZero_second_slabs_separated ha hab hb geometry) heta H
      (fun _ => inter_subset_left)
  have hsame : hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi := by
    ext x
    obtain ⟨s, hs⟩ := hselect x
    rw [hamiltonZeroThirdCircleMap_ambient, hs, ← hamiltonZeroThirdCircleMap_ambient, hthird]
  have hRlocal (s : Bool) : R ⊆ hamiltonZeroCircleMap (eta s) ⁻¹' AddCircle.closedIntervalArc p alpha beta := by
    intro x hx
    by_cases hxN : x ∈ N s
    · exact hReta s hxN
    · have hfixed : hamiltonZeroAmbientMap (eta s) x = hamiltonZeroAmbientMap phi x :=
        ((H s).map_one_left x).symm.trans ((H s).prop 1 x (fun h => hxN (interior_subset h)))
      rw [mem_preimage, ← hamiltonZeroAmbientMap_circle, hfixed, hamiltonZeroAmbientMap_circle]
      exact hfirst hx
  refine ⟨psi, hpsi, Hpsi, Fpsi, hsame, ?_, ?_, G, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs⟩ := hselect x
    rw [mem_preimage, ← hamiltonZeroAmbientMap_circle, hs, hamiltonZeroAmbientMap_circle]
    exact hRlocal s hx
  · intro s
    refine ⟨?_, ?_, ?_, u s, hu s, v s, hv s, ?_, ?_, ?_⟩
    · intro x hx
      rw [mem_preimage, ← hamiltonZeroAmbientMap_circle, heq s hx, hamiltonZeroAmbientMap_circle]
      exact hReta s hx
    · intro x hx
      rw [mem_preimage, hamiltonZeroSecondCircleMap_ambient, heq s hx,
        ← hamiltonZeroSecondCircleMap_ambient]
      exact hSeta s hx
    · intro x hx
      exact (heq s ((geometry.slabs s).1.closed.frontier_subset hx)).trans
        (((H s).map_one_left x).symm.trans ((H s).prop 1 x hx.2))
    · exact (hterminalEta s).congr (geometry.slabs s).1.closed (heq s)
    · exact (hfamily s).congr_target (hsame.trans (hthird s).symm) (heq s)
    · rw [hsame]
      exact hgroups s
  · intro t x
    obtain ⟨s, hs⟩ := hGselect t x
    rw [hs]
    exact hHthird s t x
  · intro s t x hx
    rw [hGside s t x hx]
    exact hHarc s t x hx

theorem exists_hamiltonZero_source_simultaneous_terminal_disk_installation
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
      ∃ eta psi : C(H0, H0),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 eta) ∧
        Nonempty (phi.HomotopyRel eta B0) ∧
        HamiltonZeroSecondPhaseGeometry e R eta a b ∧
        (∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroSecondCircleMap eta ⁻¹'
          AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b))) ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
        Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ) ∧
        hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap eta ∧
        R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
        HamiltonZeroInstalledSecondSlabDisks e d R eta psi a b alpha beta ∧
        ∃ G : (hamiltonZeroAmbientMap eta).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ,
          (∀ t x, (Q0 (G (t, x))).1.1 = hamiltonZeroThirdCircleMap eta x) ∧
          ∀ side : Bool, ∀ t x,
            x ∈ R ∩ hamiltonZeroSecondCircleMap eta ⁻¹'
              AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b) →
            (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
            (Q0 (G (t, x))).1.2 ∈ AddCircle.closedIntervalArc p
              (if side then b else a) (if side then a + p else b) := by
  obtain ⟨a, ha', b, hb', hreg, _, eta, _, _, _, heta, ⟨Heta⟩, ⟨Feta⟩, ⟨Geta⟩,
      _, _, _, _, _, hReta, geometry, hcuts, _, _, terminal⟩ :=
    exists_hamiltonZero_source_simultaneous_terminal_trivial_groups e d hd phi hphi F0 hI
      ha hab hb hR hRfront hinjR hK hne hr c hc hi ho hzero hside g hg hproduct
  have hterminal : ∀ side : Bool,
      let N := R ∩ hamiltonZeroSecondCircleMap eta ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      ∃ u ∈ Ioo (p / 4) (p / 3), ∃ v ∈ Ioo (2 * p / 3) (3 * p / 4),
        HamiltonZeroTerminalThirdPhaseData e N eta u v ∧
        ∀ thirdSide : Bool,
          let T := N ∩ hamiltonZeroThirdCircleMap eta ⁻¹'
            AddCircle.closedIntervalArc p (if thirdSide then v else u) (if thirdSide then u + p else v)
          ∀ x : T, Subsingleton (FundamentalGroup T x) := by
    intro side
    obtain ⟨u, hu, v, hv, _, hdata, _, hgroups⟩ := terminal side
    exact ⟨u, hu, v, hv, hdata, hgroups⟩
  obtain ⟨psi, hpsi, ⟨Hpsi⟩, Fpsi, hthird, hRpsi, hdisks, G, hGthird, hGarc⟩ :=
    exists_hamiltonZero_simultaneous_terminal_disk_installation hd eta heta Feta
      (by linarith [ha'.1]) (by linarith [ha'.2, hb'.1]) (by linarith [hb'.2])
      geometry ha hab.le hb hReta hterminal
  exact ⟨a, ha', b, hb', hreg, eta, psi, heta, ⟨Heta⟩, geometry, hcuts, hpsi,
    ⟨Heta.trans Hpsi⟩, Fpsi, ⟨Geta.trans G⟩, hthird, hRpsi, hdisks, G, hGthird, hGarc⟩

end PoincareConjecture.M76
