import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Compression.PhaseMap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Compression.SlabCoordinate

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem exists_hamiltonZero_lower_third_slab_map
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F0 : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hN : IsCompact (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b))
    (he : PLDomain e (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(a : C0)}) ∪
          (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(b : C0)})))
    {j : V2 → X0} (hj : PolyhedralPLInCharts e j D)
    (hi : Topology.IsEmbedding (fun z : D => j z))
    (hjN : MapsTo j D (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hproper : ∀ z : D,
      j z ∈ frontier (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) ↔
        (z : V2) ∈ Q)
    (hrim : ∀ z ∈ Q, j z ∈ R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(a : C0)})
    (havoid : ∀ z : D, j z ∉ frontier R) :
    ∃ (P : OriginalDiskProduct e
        (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) j)
      (psi : C(H0, H0)) (A : Set X0) (G : C(unitInterval × X0, X0)),
      MapsTo P.map (D ×ˢ I) (frontier R)ᶜ ∧
      PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
      IsCompact A ∧ PLDomain e A ∧ P.closedStrip ⊆ interior A ∧ A ⊆ interior R ∧
      (∀ x, G (0, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ x, G (1, x) = hamiltonZeroAmbientMap psi x) ∧
      (∀ (t : unitInterval) (x : X0), x ∉ interior A →
        G (t, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ (t : unitInterval) (x : X0), (Q0 (G (t, x))).2 = hamiltonZeroCircleMap phi x) ∧
      (∀ (t : unitInterval) (x : X0),
        (Q0 (G (t, x))).1.2 = hamiltonZeroSecondCircleMap phi x) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi ∧
      (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(a : C0)}) =
        ((R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(a : C0)}) \ P.openStrip) ∪ P.endDisks ∧
      (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(b : C0)}) =
        (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(b : C0)}) ∧
      (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) = P.cutCarrier ∧
      IsOpen ((Subtype.val :
        ↥(R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) → X0) ⁻¹' P.openStrip) ∧
      (∀ z ∈ D ×ˢ I,
        P.map z ∈ frontier (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) →
          P.map z ∈ R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(a : C0)}) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let N := R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b
  have habq : (a : C0) ≠ (b : C0) := by
    intro h
    have haI : a ∈ Ico c (c + p) := ⟨ha.le, by linarith⟩
    have hbI : b ∈ Ico c (c + p) := ⟨by linarith, by linarith⟩
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp h)
  have havoidb (z : D) : hamiltonZeroThirdCircleMap phi (j z) ≠ (b : C0) := by
    intro hz
    have hzb : j z ∈ R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(b : C0)} := ⟨(hjN z.property).1, hz⟩
    have hzfront : j z ∈ frontier N := hfront.symm.subset (Or.inr (Or.inr hzb))
    have hza := hrim z ((hproper z).mp hzfront)
    exact habq (hza.2.symm.trans hz)
  obtain ⟨f, U, hU, hUR, hf, hfPL, hphase, hpos, hzero, hbound, hcontains⟩ :=
    exists_hamiltonZero_shifted_lower_third_slab_coordinate e d hd phi hphi ha hab hb
      (R := R) (by
        rw [hfront]
        congr 1
        ext x
        simp only [mem_union, mem_inter_iff, mem_preimage, mem_insert_iff, mem_singleton_iff]
        tauto)
  have hDU : j '' D ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hcontains (j z) (hjN hz) (havoid ⟨z, hz⟩) (havoidb ⟨z, hz⟩)
  have hD : IsCompact (j '' D) :=
    (isCompact_closedBall (0 : V2) 1).image_of_continuousOn hj.continuousOn
  have hDne : (j '' D).Nonempty := ⟨j 0, 0, mem_closedBall_self zero_le_one, rfl⟩
  obtain ⟨y, hy, hmax⟩ := hD.exists_isMaxOn hDne (hf.abs.mono hDU)
  let rho := (|f y| + (b - a)) / 2
  have hrho : 0 < rho := by dsimp [rho]; linarith [abs_nonneg (f y)]
  have hrhogap : rho < b - a := by dsimp [rho]; linarith [hbound y (hDU hy)]
  have hmaxrho : |f y| < rho := by dsimp [rho]; linarith [hbound y (hDU hy)]
  let eta := (p - (b - a)) / 2
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hetagap : eta < p - (b - a) := by dsimp [eta]; linarith
  have hfnonneg (x : X0) (hx : x ∈ j '' D) : 0 ≤ f x := by
    obtain ⟨z, hz, rfl⟩ := hx
    by_cases hfrontN : j z ∈ frontier N
    · exact ((hzero _ (hDU ⟨z, hz, rfl⟩)).mp hfrontN).ge
    · exact ((hpos _ (hDU ⟨z, hz, rfl⟩)).mp
        ((mem_interior_iff_notMem_frontier (hjN hz)).mpr hfrontN)).le
  let V := U ∩ f ⁻¹' Ioo (-eta) rho
  have hV : IsOpen V := hf.isOpen_inter_preimage hU isOpen_Ioo
  have hDV : j '' D ⊆ V := fun x hx => ⟨hDU hx,
    lt_of_lt_of_le (neg_lt_zero.mpr heta) (hfnonneg x hx),
    (le_abs_self (f x)).trans_lt ((hmax hx).trans_lt hmaxrho)⟩
  obtain ⟨P, hPV, hopen, hcut, hcompact, _, _, _, _, _⟩ :=
    exists_original_disk_cut_domain hN he hj hi hjN hproper hV hDV
  have hSV : P.closedStrip ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact hPV ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hfV (i : ι) : LocallyPiecewiseAffineOn (f ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' V) :=
    (hfPL i).mono ((e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hV)
      (fun _ hx => ⟨hx.1, hx.2.1⟩)
  obtain ⟨psi, A, G, hA, heA, hSA, hAV, hstart, hend, hfixed, hnormal, hsecondnormal,
      hpsi, hF, hF0, hfirst, hsecond, hGa, hGb, hslab⟩ :=
    exists_hamiltonZero_third_coordinate_compression_map hd hphi F0 P hN he hopen hV
      (inter_subset_left.trans hUR) hSV (hf.mono inter_subset_left) hfV
      (fun x hx => hphase x hx.1) (fun x hx => hpos x hx.1) (fun x hx => hzero x hx.1)
      heta hrho hrhogap hetagap (fun _ hx => ⟨hx.2.1.le, hx.2.2.le⟩)
  refine ⟨P, psi, A, G, ?_, hcut, hcompact, hA, heA, hSA,
    hAV.trans (inter_subset_left.trans hUR), hstart, hend, hfixed, hnormal, hsecondnormal,
    hpsi, hF, hF0, hfirst, hsecond, hGa, hGb, hslab, hopen, ?_⟩
  · intro z hz hfrontR
    exact disjoint_left.mp disjoint_interior_frontier (hUR (hPV hz).1) hfrontR
  · intro z hz hfrontN
    refine ⟨interior_subset (hUR (hPV hz).1), ?_⟩
    change hamiltonZeroThirdCircleMap phi (P.map z) = (a : C0)
    rw [hphase _ (hPV hz).1, (hzero _ (hPV hz).1).mp hfrontN]
    simp

end PoincareConjecture.M76
