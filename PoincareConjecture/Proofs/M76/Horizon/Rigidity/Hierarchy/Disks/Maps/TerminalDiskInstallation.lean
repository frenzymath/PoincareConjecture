import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.InstalledSecondSlabHierarchy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.TerminalGroups
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.SourceDiskFamilyInstallation

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

def HamiltonZeroInstalledTerminalDiskFamily {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (R : Set X0) (phi psi : C(H0, H0)) (a b alpha beta u v : ℝ) : Prop :=
  ∃ (n : Bool → ℕ) (j : (Σ s : Bool, Fin (n s)) → V2 → X0)
    (first second : (Σ s : Bool, Fin (n s)) → V2 → ℝ)
    (q : (Σ s : Bool, Fin (n s)) → V2 → X0),
    (∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Disk) =
      R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {((if s then b else a : ℝ) : C0)}) ∧
    Pairwise (fun i k => Disjoint (j i '' Disk) (j k '' Disk)) ∧
    ∀ i, PolyhedralPLInCharts e (j i) Disk ∧
      Topology.IsEmbedding (fun z : Disk => j i z) ∧ MapsTo (j i) Disk R ∧
      (∀ z : Disk, j i z ∈ frontier R ↔ (z : V2) ∈ Rim) ∧
      IsCompact (j i '' Disk) ∧ IsPathConnected (j i '' Disk) ∧
      (∀ x ∈ j i '' Disk, connectedComponentIn
        (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {((if i.1 then b else a : ℝ) : C0)}) x =
          j i '' Disk) ∧
      FinitePiecewiseAffineOn (first i) Disk ∧ FinitePiecewiseAffineOn (second i) Disk ∧
      (∀ z ∈ Disk, first i z ∈ Icc alpha beta ∧ second i z ∈ Icc u v) ∧
      PolyhedralPLInCharts d (q i) Disk ∧
      (∀ z ∈ Disk, Q0 (q i z) =
        ((((if i.1 then b else a : ℝ) : C0), (second i z : C0)), (first i z : C0))) ∧
      EqOn (q i) (fun z => hamiltonZeroAmbientMap phi (j i z)) Rim ∧
      ∀ z : Disk, hamiltonZeroAmbientMap psi (j i z) = q i z

theorem exists_hamiltonZero_terminal_disk_family_installation
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R) {a b : ℝ}
    (habC : (a : C0) ≠ (b : C0))
    (terminal : HamiltonZeroTerminalThirdPhaseData e R phi a b)
    {cut alpha beta cut' u v : ℝ}
    (halpha : cut < alpha) (horder : alpha ≤ beta) (hbeta : beta < cut + p)
    (hu : cut' < u) (huv : u ≤ v) (hv : v < cut' + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi ∧
      R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
      R ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p u v ∧
      HamiltonZeroTerminalThirdPhaseData e R psi a b ∧
      HamiltonZeroInstalledTerminalDiskFamily e d R phi psi a b alpha beta u v ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ,
        (∀ t x, (Q0 (G (t, x))).1.1 = hamiltonZeroThirdCircleMap phi x) ∧
        ∀ t x, x ∈ R → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (G (t, x))).1.2 ∈ AddCircle.closedIntervalArc p u v := by
  classical
  have hfamilies (s : Bool) := terminal.disks (if s then b else a)
    (by cases s <;> simp)
  choose n T hcover hdis hprops using hfamilies
  let I := Σ s : Bool, Fin (n s)
  have hmodels (i : I) := (hprops i.1 i.2).2.2.2
  choose H j hj hji hjR hjH hjimage hjrim using hmodels
  have hsub (i : I) : T i.1 i.2 ⊆
      R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {((if i.1 then b else a : ℝ) : C0)} := by
    rw [← hcover i.1]
    exact subset_iUnion (T i.1) i.2
  have hthird (i : I) (z : Disk) :
      hamiltonZeroThirdCircleMap phi (j i z) = ((if i.1 then b else a : ℝ) : C0) := by
    exact (hsub i ((hjimage i).subset ⟨z, z.property, rfl⟩)).2
  have hdisjoint : Pairwise (fun i k : I => Disjoint (j i '' Disk) (j k '' Disk)) := by
    rintro ⟨s, i⟩ ⟨t, k⟩ hik
    by_cases hst : s = t
    · subst t
      rw [hjimage, hjimage]
      exact hdis s (fun h => hik (by cases h; rfl))
    · apply disjoint_left.mpr
      intro x hx hy
      have hxphase := (hsub ⟨s, i⟩ ((hjimage ⟨s, i⟩).subset hx)).2
      have hyphase := (hsub ⟨t, k⟩ ((hjimage ⟨t, k⟩).subset hy)).2
      have heq := hxphase.symm.trans hyphase
      cases s <;> cases t <;> simp_all
  obtain ⟨first, second, q, psi, hfirstPL, hsecondPL, hrange, hq, hcoords, hrim,
      hpsi, Hpsi, Fpsi, hsame, hvalue, hRfirst, hRsecond, G, hGphase, hGarc⟩ :=
    exists_hamiltonZero_source_disk_family_installation hd hphi F heR j hj hji hjR
      (fun i z => (hjrim i z).symm) hdisjoint halpha horder hbeta hu huv hv hfirst hsecond
      (fun i => ((if i.1 then b else a : ℝ) : C0)) hthird
  have hterminal : HamiltonZeroTerminalThirdPhaseData e R psi a b := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hsame]
      exact terminal.geometry.slabs
    · rw [hsame]
      exact terminal.geometry.groups
    · rw [hsame]
      exact terminal.boundary
    · rw [hsame]
      exact terminal.irreducible
    · rw [hsame]
      exact terminal.disks
  refine ⟨psi, hpsi, Hpsi, Fpsi, hsame, hRfirst, hRsecond, hterminal,
    ?_, G, hGphase, hGarc⟩
  refine ⟨n, j, first, second, q, ?_, hdisjoint, ?_⟩
  · intro s
    rw [hsame]
    simpa only [hjimage] using hcover s
  · intro i
    refine ⟨hj i, hji i, hjR i, hjrim i, ?_, ?_, ?_, hfirstPL i, hsecondPL i,
      hrange i, hq i, hcoords i, hrim i, hvalue i⟩
    · rw [hjimage]
      exact (hprops i.1 i.2).1
    · rw [hjimage]
      exact (hprops i.1 i.2).2.1
    · rw [hsame, hjimage]
      exact (hprops i.1 i.2).2.2.1

theorem exists_hamiltonZero_source_terminal_disk_installation
    {ι κ : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F0 : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (hI : IsPLIrreducible e R)
    (hinjR : ∀ x : R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) x))
    {cut alpha beta cut' u v : ℝ}
    (halpha : cut < alpha) (hbeta : beta < cut + p)
    (hu : cut' < u) (hv : v < cut' + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v)
    (j : ℝ × ℝ → X0) (hj : j '' Ann ⊆ frontier R)
    (c : C(Ann, unitInterval × C0)) (hc : IsCoveringMap c)
    (delta0 delta1 : ℝ) (theta : C0)
    (hvalue : ∀ z : Ann, hamiltonZeroAmbientMap phi (j z) =
      hamiltonZeroAnnulusTargetMap delta0 delta1 theta (c z)) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      (∀ t ∈ ({a, b} : Set ℝ), HamiltonZeroThirdCoordinateRegularity e R phi (t : C0)) ∧
      ∃ (eta psi : C(H0, H0)) (A : Set X0), IsCompact A ∧ A ⊆ interior R ∧
        (∀ x ∉ A, hamiltonZeroAmbientMap eta x = hamiltonZeroAmbientMap phi x) ∧
        hamiltonZeroCircleMap eta = hamiltonZeroCircleMap phi ∧
        hamiltonZeroSecondCircleMap eta = hamiltonZeroSecondCircleMap phi ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 eta) ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
        Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ) ∧
        hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap eta ∧
        R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
        R ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p u v ∧
        HamiltonZeroTerminalThirdPhaseData e R psi a b ∧
        HamiltonZeroInstalledTerminalDiskFamily e d R eta psi a b alpha beta u v ∧
        (∀ side : Bool,
          let N := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
          ∀ x : N, Subsingleton (FundamentalGroup N x)) ∧
        ∃ G : (hamiltonZeroAmbientMap eta).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ,
          (∀ t x, (Q0 (G (t, x))).1.1 = hamiltonZeroThirdCircleMap eta x) ∧
          ∀ t x, x ∈ R → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
            (Q0 (G (t, x))).1.2 ∈ AddCircle.closedIntervalArc p u v := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  obtain ⟨a, ha, b, hb, hreg, eta, A, hA, hAR, hfixed, hfirstEq, hsecondEq,
      heta, ⟨Heta⟩, ⟨Feta⟩, ⟨Geta⟩, geom, hboundary, hcuts, hdisks⟩ :=
    exists_hamiltonZero_terminal_third_disk_families e d hd phi hphi F0 hI hinjR
      halpha hbeta hu hv hfirst hsecond j hj c hc delta0 delta1 theta hvalue
  have hab : a < b := by linarith [ha.2, hb.1]
  have habC : (a : C0) ≠ (b : C0) := by
    intro h
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith [ha.1, ha.2])
      (show b ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith [hb.1, hb.2])).mp h)
  have hReta : R ⊆ hamiltonZeroCircleMap eta ⁻¹' AddCircle.closedIntervalArc p alpha beta := by
    rw [hfirstEq]
    exact hfirst
  have hSeta : R ⊆ hamiltonZeroSecondCircleMap eta ⁻¹' AddCircle.closedIntervalArc p u v := by
    rw [hsecondEq]
    exact hsecond
  let z : Ann := Dehn.annulusRimPoint false 0
  have hzR : j z ∈ R := hI.1.closed.frontier_subset (hj ⟨z, z.property, rfl⟩)
  obtain ⟨r, hr, _⟩ := hfirst hzR
  obtain ⟨s, hs, _⟩ := hsecond hzR
  have hboundaryPhi : (frontier R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(a : C0)}).Nonempty := by
    obtain ⟨x, hx, hphase⟩ := hboundary a
    refine ⟨x, hx, ?_⟩
    change hamiltonZeroThirdCircleMap phi x = (a : C0)
    rw [hamiltonZeroThirdCircleMap_ambient, ← hfixed x (fun h => hx.2 (hAR h)),
      ← hamiltonZeroThirdCircleMap_ambient]
    exact hphase
  have hgroups := hamiltonZero_terminal_third_slabs_pi1_subsingleton e phi eta Feta
    hI.1 hinjR hA hAR hfixed (by linarith [ha.1]) hab (by linarith [hb.2])
    hreg geom hboundaryPhi halpha hbeta hu hv hReta hSeta
  obtain ⟨psi, hpsi, ⟨Hpsi⟩, Fpsi, hthird, hRpsi, hSpsi, terminal, installed, G, hGphase, hGarc⟩ :=
    exists_hamiltonZero_terminal_disk_family_installation hd heta Feta hI.1 habC
      ⟨geom, hboundary, hcuts, hdisks⟩ halpha (hr.1.trans hr.2) hbeta hu (hs.1.trans hs.2) hv hReta hSeta
  refine ⟨a, ha, b, hb, hreg, eta, psi, A, hA, hAR, hfixed, hfirstEq, hsecondEq,
    heta, hpsi, ⟨Heta.trans Hpsi⟩, Fpsi, ⟨Geta.trans G⟩, hthird, hRpsi, hSpsi,
    terminal, installed, ?_, G, hGphase, hGarc⟩
  rw [hthird]
  exact hgroups

end PoincareConjecture.M76
