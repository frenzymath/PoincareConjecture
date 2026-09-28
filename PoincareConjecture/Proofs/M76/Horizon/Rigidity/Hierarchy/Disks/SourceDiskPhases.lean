import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.SourceBoundaryPhases

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

theorem exists_hamiltonZero_terminal_third_disk_families
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
      ∃ (psi : C(H0, H0)) (A : Set X0), IsCompact A ∧ A ⊆ interior R ∧
        (∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
        hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
        hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
        Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ) ∧
        HamiltonZeroThirdPhaseGeometry e R psi a b ∧
        (∀ xi : C0, (frontier R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {xi}).Nonempty) ∧
        (∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
          AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b))) ∧
        ∀ t ∈ ({a, b} : Set ℝ),
          let S := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(t : C0)}
          ∃ (n : ℕ) (T : Fin n → Set X0),
            (⋃ i, T i) = S ∧ Pairwise (fun i k => Disjoint (T i) (T k)) ∧
            ∀ i, IsCompact (T i) ∧ IsPathConnected (T i) ∧
              (∀ x ∈ T i, connectedComponentIn S x = T i) ∧
              ∃ (H : D ≃ₜ T i) (k : V2 → X0), PolyhedralPLInCharts e k D ∧
                Topology.IsEmbedding (fun z : D => k z) ∧ MapsTo k D R ∧
                (∀ z : D, k z = (H z : X0)) ∧ k '' D = T i ∧
                ∀ z : D, k z ∈ frontier R ↔ (z : V2) ∈ Q := by
  obtain ⟨a, ha, b, hb, hreg, psi, A, hA, hAR, hfixed, hfirstEq, hsecondEq,
      hpsi, Hpsi, ⟨Fpsi⟩, Hext, geom, hboundary, hterminal, hcuts⟩ :=
    exists_hamiltonZero_boundary_meeting_third_hierarchy e d hd phi hphi F0 hI hinjR
      halpha hbeta hu hv hfirst hsecond j hj c hc delta0 delta1 theta hvalue
  have hfirstPsi : R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta := by
    rw [hfirstEq]
    exact hfirst
  have hsecondPsi : R ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p u v := by
    rw [hsecondEq]
    exact hsecond
  have hab : a < b := by linarith [ha.2, hb.1]
  have habC : (a : C0) ≠ (b : C0) := by
    intro h
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith [ha.1, ha.2])
      (show b ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith [hb.1, hb.2])).mp h)
  refine ⟨a, ha, b, hb, hreg, psi, A, hA, hAR, hfixed, hfirstEq, hsecondEq,
    hpsi, Hpsi, ⟨Fpsi⟩, Hext, geom, hboundary, hcuts, ?_⟩
  intro t ht
  have halts :
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
              Nonempty (ChartwisePLBall e B (T i)))) := by
    rcases ht with rfl | rfl
    · exact exists_hamiltonZero_third_whole_component_alternatives e phi psi Fpsi hI hA hAR
        hfixed habC (hreg _ (Or.inl rfl)) (geom.slabs false).1 (geom.slabs false).2.1
        halpha hbeta hu hv hfirstPsi hsecondPsi (geom.groups _ (Or.inl rfl))
    · exact exists_hamiltonZero_third_whole_component_alternatives e phi psi Fpsi hI hA hAR
        hfixed habC.symm (hreg _ (Or.inr rfl)) (geom.slabs false).1
        (by simpa only [union_comm] using (geom.slabs false).2.1)
        halpha hbeta hu hv hfirstPsi hsecondPsi (geom.groups _ (Or.inr rfl))
  obtain ⟨n, T, hcover, hdis, hprops⟩ := halts
  refine ⟨n, T, hcover, hdis, ?_⟩
  intro i
  obtain ⟨hTi, hconn, hcomp, hdisk | hsphere⟩ := hprops i
  · exact ⟨hTi, hconn, hcomp, hdisk⟩
  · have hsub : T i ⊆ R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(t : C0)} := by
      rw [← hcover]
      exact subset_iUnion T i
    obtain ⟨x, hx, hxfront⟩ := hterminal t ht (T i) hconn.nonempty hsub hcomp
    exact (disjoint_left.mp hsphere.1 hx hxfront).elim

end PoincareConjecture.M76
