import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Upper.PhaseMap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Upper.Coordinate

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem exists_wide_upper_source_slab_map
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {phi : C(H, H)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hN : IsCompact (sourceSlab phi a b)) (he : PLDomain e (sourceSlab phi a b))
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    {j : V2 → X} (hj : PolyhedralPLInCharts e j D)
    (hi : Topology.IsEmbedding (fun z : D => j z)) (hjN : MapsTo j D (sourceSlab phi a b))
    (hproper : ∀ z : D, j z ∈ frontier (sourceSlab phi a b) ↔ (z : V2) ∈ Q)
    (hrim : ∀ z ∈ Q, j z ∈ sourceSurface phi (b : C))
    (havoid : ∀ z : D, j z ∉ frontier R) :
    ∃ (P : OriginalDiskProduct e (sourceSlab phi a b) j) (psi : C(H, H)) (A : Set X),
      MapsTo P.map (D ×ˢ I) (frontier R)ᶜ ∧
      PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
      IsCompact A ∧ PLDomain e A ∧ P.closedStrip ⊆ interior A ∧ A ⊆ interior R ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi) ∧
      Nonempty (phi.HomotopyRel psi B) ∧
      Nonempty ((ContinuousMap.id H).HomotopyRel psi B) ∧
      (∀ x : H, ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ interior A →
        psi x = phi x) ∧
      sourceSurface psi (b : C) = (sourceSurface phi (b : C) \ P.openStrip) ∪ P.endDisks ∧
      sourceSurface psi (a : C) = sourceSurface phi (a : C) ∧
      sourceSlab psi a b = P.cutCarrier ∧ psi ⁻¹' B = phi ⁻¹' B ∧
      IsOpen ((Subtype.val : sourceSlab phi a b → X) ⁻¹' P.openStrip) ∧
      (∀ z ∈ D ×ˢ I, P.map z ∈ frontier (sourceSlab phi a b) →
        P.map z ∈ sourceSurface phi (b : C)) := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  have habq : (a : C) ≠ (b : C) := by
    intro h
    have haI : a ∈ Ico c (c + p) := ⟨ha.le, by linarith⟩
    have hbI : b ∈ Ico c (c + p) := ⟨by linarith, by linarith⟩
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp h)
  have havoidb (z : D) : ambientSourcePhase phi (j z) ≠ (a : C) := by
    intro hz
    have hzR := sourceSlab_subset phi a b (hjN z.property)
    have hzb : j z ∈ sourceSurface phi (a : C) := by
      rw [sourceSurface_eq_inter_phase]
      exact ⟨hzR, hz⟩
    have hzfront : j z ∈ frontier (sourceSlab phi a b) := hfront.symm.subset (Or.inr (Or.inl hzb))
    have hza := hrim z ((hproper z).mp hzfront)
    rw [sourceSurface_eq_inter_phase] at hza
    exact habq (hza.2.symm.trans hz).symm
  obtain ⟨f, U, hU, hUR, hf, hfPL, hphase, hpos, hzero, hbound, hcontains⟩ :=
    exists_shifted_upper_slab_coordinate e d hd phi hphi ha hab hb hfront
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
  have hfnonneg (x : X) (hx : x ∈ j '' D) : 0 ≤ f x := by
    obtain ⟨z, hz, rfl⟩ := hx
    by_cases hfrontN : j z ∈ frontier (sourceSlab phi a b)
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
  have hfV (i : α) : LocallyPiecewiseAffineOn (f ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' V) :=
    (hfPL i).mono ((e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hV)
      (fun _ hx => ⟨hx.1, hx.2.1⟩)
  obtain ⟨psi, A, hA, heA, hSA, hAV, hpsi, hF, hF0, hfixed, hGa, hGb, hslab, hboundary⟩ :=
    exists_upper_asymmetric_relative_compression_map hd hphi F0 P hN he hopen hV
      (inter_subset_left.trans hUR) hSV (hf.mono inter_subset_left) hfV
      (fun x hx => hphase x hx.1) (fun x hx => hpos x hx.1) (fun x hx => hzero x hx.1)
      heta hrho hrhogap hetagap (fun _ hx => ⟨hx.2.1.le, hx.2.2.le⟩)
  refine ⟨P, psi, A, ?_, hcut, hcompact, hA, heA, hSA,
    hAV.trans (inter_subset_left.trans hUR), hpsi, hF, hF0, hfixed, hGa, hGb,
    hslab, hboundary, hopen, ?_⟩
  · intro z hz hfrontR
    exact disjoint_left.mp disjoint_interior_frontier (hUR (hPV hz).1) hfrontR
  · intro z hz hfrontN
    rw [sourceSurface_eq_inter_phase]
    refine ⟨interior_subset (hUR (hPV hz).1), ?_⟩
    change ambientSourcePhase phi (P.map z) = (b : C)
    rw [hphase _ (hPV hz).1, (hzero _ (hPV hz).1).mp hfrontN]
    simp

end PoincareConjecture.M76.HamiltonIntervalTorus
