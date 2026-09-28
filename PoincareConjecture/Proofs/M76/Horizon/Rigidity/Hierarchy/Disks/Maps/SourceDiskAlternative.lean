import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.DiskFamilyAlternative
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.Boundary.RetainedRectangleEdges
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.SimultaneousTerminalGroups

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

def HamiltonZeroHomeomorphicDiskInstallation {ι κ η : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (R : Set X0) (phi : C(H0, H0)) (j : η → V2 → X0) (theta : η → C0)
    (alpha beta a b : ℝ) : Prop :=
  ∃ (v w : η → V2 → ℝ) (q : η → V2 → X0)
    (E : η → Disk ≃ₜ (Icc alpha beta ×ˢ Icc a b)) (psi : C(H0, H0)),
    (∀ i, FinitePiecewiseAffineOn (v i) Disk) ∧
    (∀ i, FinitePiecewiseAffineOn (w i) Disk) ∧
    (∀ i, (E i).IsFinitePL) ∧
    (∀ i, ∀ z : Disk, (E i z : ℝ × ℝ) = (v i z, w i z)) ∧
    (∀ i, ∀ z ∈ Disk, v i z ∈ Icc alpha beta ∧ w i z ∈ Icc a b) ∧
    (∀ i, PolyhedralPLInCharts d (q i) Disk) ∧
    (∀ i, ∀ z ∈ Disk, Q0 (q i z) = ((theta i, (w i z : C0)), (v i z : C0))) ∧
    (∀ i, InjOn (q i) Disk) ∧
    (∀ i, EqOn (q i) (fun z => hamiltonZeroAmbientMap phi (j i z)) Rim) ∧
    ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
    Nonempty (phi.HomotopyRel psi B0) ∧
    Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
    hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi ∧
    (∀ i, ∀ z : Disk, hamiltonZeroAmbientMap psi (j i z) = q i z) ∧
    (R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta) ∧
    (R ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∧
    ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel
        (hamiltonZeroAmbientMap psi) (interior R)ᶜ,
      (∀ t x, (Q0 (G (t, x))).1.1 = hamiltonZeroThirdCircleMap phi x) ∧
      ∀ t x, x ∈ R → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
        (Q0 (G (t, x))).1.2 ∈ AddCircle.closedIntervalArc p a b

def HamiltonZeroTerminalDiskAlternative {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (R : Set X0) (phi : C(H0, H0)) (u v alpha beta a b : ℝ) : Prop :=
  ∃ (n : Bool → ℕ) (j : (Σ s : Bool, Fin (n s)) → V2 → X0),
    (∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Disk) =
      R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {((if s then v else u : ℝ) : C0)}) ∧
    Pairwise (fun i k => Disjoint (j i '' Disk) (j k '' Disk)) ∧
    (∀ i, PolyhedralPLInCharts e (j i) Disk ∧
      Topology.IsEmbedding (fun z : Disk => j i z) ∧ MapsTo (j i) Disk R ∧
      (∀ z : Disk, j i z ∈ frontier R ↔ (z : V2) ∈ Rim) ∧
      IsCompact (j i '' Disk) ∧ IsPathConnected (j i '' Disk) ∧
      ∀ x ∈ j i '' Disk, connectedComponentIn
        (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {((if i.1 then v else u : ℝ) : C0)}) x =
          j i '' Disk) ∧
    (HamiltonZeroHomeomorphicDiskInstallation e d R phi j
      (fun i => ((if i.1 then v else u : ℝ) : C0)) alpha beta a b ∨
      ∃ i, HamiltonZeroDiskFailureArc e R phi (j i)
        ((if i.1 then v else u : ℝ) : C0) alpha beta a b)

theorem HamiltonZeroTerminalThirdPhaseData.disk_alternative
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R) {u v : ℝ} (huv : (u : C0) ≠ (v : C0))
    (terminal : HamiltonZeroTerminalThirdPhaseData e R phi u v)
    {cut alpha beta cut' a b : ℝ}
    (halpha : cut < alpha) (hab : alpha < beta) (hbeta : beta < cut + p)
    (ha : cut' < a) (horder : a < b) (hb : b < cut' + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (hedges : ∀ x ∈ frontier R,
      hamiltonZeroCircleMap phi x ∈ ({(alpha : C0), (beta : C0)} : Set C0) ∨
      hamiltonZeroSecondCircleMap phi x ∈ ({(a : C0), (b : C0)} : Set C0)) :
    HamiltonZeroTerminalDiskAlternative e d R phi u v alpha beta a b := by
  classical
  have hfamilies (s : Bool) := terminal.disks (if s then v else u) (by cases s <;> simp)
  choose n T hcover hdis hprops using hfamilies
  let I := Σ s : Bool, Fin (n s)
  have hmodels (i : I) := (hprops i.1 i.2).2.2.2
  choose H j hj hji hjR hjH hjimage hjrim using hmodels
  have hsub (i : I) : T i.1 i.2 ⊆
      R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {((if i.1 then v else u : ℝ) : C0)} := by
    rw [← hcover i.1]
    exact subset_iUnion (T i.1) i.2
  have hthird (i : I) (z : Disk) :
      hamiltonZeroThirdCircleMap phi (j i z) = ((if i.1 then v else u : ℝ) : C0) :=
    (hsub i ((hjimage i).subset ⟨z, z.property, rfl⟩)).2
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
  refine ⟨n, j, ?_, hdisjoint, ?_, ?_⟩
  · intro s
    simpa only [hjimage] using hcover s
  · intro i
    refine ⟨hj i, hji i, hjR i, hjrim i, ?_, ?_, ?_⟩
    · rw [hjimage]
      exact (hprops i.1 i.2).1
    · rw [hjimage]
      exact (hprops i.1 i.2).2.1
    · rw [hjimage]
      exact (hprops i.1 i.2).2.2.1
  · exact exists_hamiltonZero_disk_family_homeomorphic_or_failure_arc hd hphi F heR
      j hj hji hjR (fun i z => (hjrim i z).symm) hdisjoint
      halpha hab hbeta ha horder hb hfirst hsecond
      (fun i => ((if i.1 then v else u : ℝ) : C0)) hthird
      (fun i z hz => hedges (j i z) ((hjrim i ⟨z, sphere_subset_closedBall hz⟩).mpr hz))

theorem exists_hamiltonZero_source_disk_alternatives
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
      ∃ eta : C(H0, H0),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 eta) ∧
        Nonempty (phi.HomotopyRel eta B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel eta B0) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap eta) (interior R)ᶜ) ∧
        R ⊆ hamiltonZeroCircleMap eta ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
        frontier R ⊆ hamiltonZeroCircleMap eta ⁻¹' {(alpha : C0), (beta : C0)} ∧
        HamiltonZeroSecondPhaseGeometry e R eta a b ∧
        (∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroSecondCircleMap eta ⁻¹'
          AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b))) ∧
        (∀ side : Bool,
          let N := R ∩ hamiltonZeroSecondCircleMap eta ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
          ∀ x : N, Function.Injective
            (FundamentalGroup.map (ContinuousMap.inclusion (inter_subset_left : N ⊆ R)) x)) ∧
        ∀ side : Bool,
          let N := R ∩ hamiltonZeroSecondCircleMap eta ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
          ∃ u ∈ Ioo (p / 4) (p / 3), ∃ v ∈ Ioo (2 * p / 3) (3 * p / 4),
            HamiltonZeroTerminalThirdPhaseData e N eta u v ∧
            (∀ thirdSide : Bool,
              let T := N ∩ hamiltonZeroThirdCircleMap eta ⁻¹'
                AddCircle.closedIntervalArc p (if thirdSide then v else u) (if thirdSide then u + p else v)
              ∀ x : T, Subsingleton (FundamentalGroup T x)) ∧
            HamiltonZeroTerminalDiskAlternative e d N eta u v alpha beta
              (if side then b else a) (if side then a + p else b) := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  obtain ⟨a, ha', b, hb', hreg, _, eta, _, _, _, heta, Heta, ⟨Feta⟩, ⟨Geta⟩,
      _, _, _, _, _, hReta, geometry, hcuts, hinj, _, terminal⟩ :=
    exists_hamiltonZero_source_simultaneous_terminal_trivial_groups e d hd phi hphi F0 hI
      ha hab hb hR hRfront hinjR hK hne hr c hc hi ho hzero hside g hg hproduct
  have hfrontEta : frontier R ⊆ hamiltonZeroCircleMap eta ⁻¹' {(alpha : C0), (beta : C0)} := by
    intro x hx
    rw [mem_preimage, ← hamiltonZeroAmbientMap_circle, ← Geta.fst_eq_snd hx.2,
      hamiltonZeroAmbientMap_circle]
    exact hRfront hx
  refine ⟨a, ha', b, hb', hreg, eta, heta, Heta, ⟨Feta⟩, ⟨Geta⟩,
    hReta, hfrontEta, geometry, hcuts, hinj, ?_⟩
  intro side
  obtain ⟨u, hu, v, hv, _, hterminal, _, hgroups⟩ := terminal side
  refine ⟨u, hu, v, hv, hterminal, hgroups, ?_⟩
  have huv : (u : C0) ≠ (v : C0) := by
    intro heq
    have h := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show u ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith [hu.1, hu.2])
      (show v ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith [hv.1, hv.2])).mp heq
    linarith [hu.2, hv.1]
  apply hterminal.disk_alternative hd heta Feta (geometry.slabs side).1 huv
    ha hab hb (cut' := if side then (a + b) / 2 else 0) ?_ ?_ ?_
    (inter_subset_left.trans hReta) inter_subset_right
    (geometry.frontier_rectangle_edges hfrontEta side)
  · cases side <;> dsimp <;> linarith [ha'.1, ha'.2, hb'.1]
  · cases side <;> dsimp <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]
  · cases side <;> dsimp <;> linarith [ha'.2, hb'.1, hb'.2]

end PoincareConjecture.M76
