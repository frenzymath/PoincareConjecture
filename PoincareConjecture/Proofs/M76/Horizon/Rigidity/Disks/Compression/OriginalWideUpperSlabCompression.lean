import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.Compression.OriginalUpperAsymmetricCompressionMap
import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductLateralOpenness
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.OriginalShiftedSlabPhaseCoordinate

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance period_positive : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩

theorem ChartwisePLMap.exists_hamiltonZero_wide_upper_slab_compression {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + 64)
    (he : PLDomain e (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b))
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)})
    {j : V2 → X0} (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b))
    (hproper : ∀ z : D, j z ∈ frontier
      (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) ↔ (z : V2) ∈ Q)
    (hrim : ∀ z ∈ Q, hamiltonZeroCircleMap phi (j z) = (b : C0)) :
    let R := hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b
    ∃ (P : OriginalDiskProduct e R j) (G : C(unitInterval × X0, X0)) (N : Set X0),
      PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
      frontier P.cutCarrier = (frontier R \ P.openStrip) ∪ P.endDisks ∧
      IsCompact N ∧ PLDomain e N ∧ P.closedStrip ⊆ interior N ∧
      (∀ x, G (0, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ (t : unitInterval) (x : X0), x ∉ interior N → G (t, x) = hamiltonZeroAmbientMap phi x) ∧
      (fun x => (Q0 (G (1, x))).2) ⁻¹' {(b : C0)} =
        (hamiltonZeroCircleMap phi ⁻¹' {(b : C0)} \ P.openStrip) ∪ P.endDisks ∧
      (∀ t : unitInterval, (fun x => (Q0 (G (t, x))).2) ⁻¹' {(a : C0)} =
        hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}) ∧
      IsOpen ((Subtype.val : frontier R → X0) ⁻¹'
        (P.map '' (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))) ∧
      MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1)
        (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)})ᶜ ∧
      (fun x => (Q0 (G (1, x))).2) ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b = P.cutCarrier ∧
      Disjoint N (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}) ∧
      frontier P.cutCarrier = (fun x => (Q0 (G (1, x))).2) ⁻¹' {(a : C0), (b : C0)} ∧
      let g : C(X0, X0) := ⟨fun x => G (1, x),
        G.continuous.comp (continuous_const.prodMk continuous_id)⟩
      ChartwisePLMap e d
        (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 (hamiltonZeroHandleMap g)) ∧
        Nonempty (phi.HomotopyRel (hamiltonZeroHandleMap g) B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel (hamiltonZeroHandleMap g) B0) := by
  intro R
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  have habq : (b : C0) ≠ (a : C0) := by
    intro h
    have haI : a ∈ Ico c (c + 4 * 16) := ⟨ha.le, by linarith⟩
    have hbI : b ∈ Ico c (c + 4 * 16) := ⟨by linarith, by linarith⟩
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp h.symm)
  have havoid (z : V2) (hz : z ∈ D) : hamiltonZeroCircleMap phi (j z) ≠ (a : C0) := by
    intro h
    have hzfront : j z ∈ frontier R := by rw [hfront]; exact Or.inl h
    have hzrim := (hproper ⟨z, hz⟩).mp hzfront
    exact habq ((hrim z hzrim).symm.trans h)
  obtain ⟨f, U, hU, hf, hfPL, hphase, hpos, hzero, hbound, hcontains⟩ :=
    hphi.exists_hamiltonZero_shifted_upper_slab_coordinate hd ha hab (by linarith) hfront
  have hDU : j '' D ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hcontains (j z) (hDR hz) (havoid z hz)
  have hD : IsCompact (j '' D) :=
    (isCompact_closedBall (0 : V2) 1).image_of_continuousOn hj.continuousOn
  have hDne : (j '' D).Nonempty :=
    ⟨j 0, 0, mem_closedBall_self zero_le_one, rfl⟩
  obtain ⟨y, hy, hmax⟩ := hD.exists_isMaxOn hDne (hf.abs.mono hDU)
  let rho := (|f y| + (b - a)) / 2
  have hrho : 0 < rho := by dsimp only [rho]; linarith [abs_nonneg (f y)]
  have hrhogap : rho < b - a := by dsimp only [rho]; linarith [hbound y (hDU hy)]
  have hmaxrho : |f y| < rho := by dsimp only [rho]; linarith [hbound y (hDU hy)]
  let eta := (4 * (16 : ℝ) - (b - a)) / 2
  have heta : 0 < eta := by dsimp only [eta]; linarith
  have hetagap : eta < 64 - (b - a) := by dsimp only [eta]; linarith
  have hsum : eta + rho < 64 := by linarith
  have hnonneg (x : X0) (hx : x ∈ j '' D) : 0 ≤ f x := by
    have hxU := hDU hx
    by_cases hi : x ∈ interior R
    · exact ((hpos x hxU).mp hi).le
    · have hxR : x ∈ R := by obtain ⟨z, hz, rfl⟩ := hx; exact hDR hz
      have hxfront : x ∈ frontier R := by
        rw [frontier, he.closed.closure_eq]
        exact ⟨hxR, hi⟩
      exact le_of_eq ((hzero x hxU).mp hxfront).symm
  let V := U ∩ f ⁻¹' Ioo (-eta) rho
  have hV : IsOpen V := hf.isOpen_inter_preimage hU isOpen_Ioo
  have hDV : j '' D ⊆ V := by
    intro x hx
    refine ⟨hDU hx, ?_, ?_⟩
    · linarith [hnonneg x hx]
    · exact (le_abs_self (f x)).trans_lt ((hmax hx).trans_lt hmaxrho)
  obtain ⟨P, hPV, hopen, hcut, hcompact, _, hcutfront, _, _, _⟩ :=
    exists_original_disk_cut_domain he.closed.isCompact he hj hemb hDR hproper hV hDV
  have hSV : P.closedStrip ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact hPV ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hfV (i : ι) : LocallyPiecewiseAffineOn (f ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' V) :=
    (hfPL i).mono ((e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hV)
      (fun _ hx => ⟨hx.1, hx.2.1⟩)
  obtain ⟨G, N, hN, heN, hSN, hNV, hGzero, hGfixed, hGa, hGother, hGslab, hGtail⟩ :=
    P.exists_hamiltonZero_upper_asymmetric_compression_map hd hphi F he.closed.isCompact he hopen hV hSV b
      (hf.mono inter_subset_left) hfV (fun x hx => hphase x hx.1)
      (fun x hx => hpos x hx.1) (fun x hx => hzero x hx.1)
      heta hrho hsum (fun x hx => ⟨hx.2.1.le, hx.2.2.le⟩)
  have hboutside : (a : C0) ∉ AddCircle.closedIntervalArc (4 * 16) (b - rho) (b + eta) := by
    rintro ⟨t, ht, htb⟩
    have htI : t ∈ Ico a (a + 4 * (16 : ℝ)) := by
      constructor <;> linarith [ht.1, ht.2]
    have hbI : a ∈ Ico a (a + 4 * (16 : ℝ)) := by
      constructor <;> linarith
    have hteq := (AddCircle.coe_eq_coe_iff_of_mem_Ico htI hbI).mp htb
    linarith [ht.1]
  have hNVavoid : Disjoint N (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hxb
    have hxV := hNV hx
    apply hboutside
    refine ⟨b - f x, ?_, ?_⟩
    · constructor <;> linarith [hxV.2.1, hxV.2.2]
    · exact (AddCircle.coe_sub (4 * (16 : ℝ)) b (f x)).trans
        ((hphase x hxV.1).symm.trans hxb)
  have hVavoid : Disjoint V (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hxb
    apply hboutside
    refine ⟨b - f x, ?_, ?_⟩
    · constructor <;> linarith [hx.2.1, hx.2.2]
    · exact (AddCircle.coe_sub (4 * (16 : ℝ)) b (f x)).trans
        ((hphase x hx.1).symm.trans hxb)
  have hstripavoid : Disjoint P.openStrip (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}) := by
    apply hNVavoid.mono_left
    intro x hx
    apply interior_subset (hSN ?_)
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz.1, hz.2.1.le, hz.2.2.le⟩, rfl⟩
  have hGb := hGother (a : C0) hboutside
  have hnewfront : frontier P.cutCarrier =
      (fun x => (Q0 (G (1, x))).2) ⁻¹' {(a : C0), (b : C0)} := by
    rw [hcutfront, hfront]
    have hsplit (f : X0 → C0) : f ⁻¹' {(a : C0), (b : C0)} =
        (f ⁻¹' {(b : C0)}) ∪ (f ⁻¹' {(a : C0)}) := by ext x; simp [or_comm]
    rw [hsplit, hsplit, hGa, hGb]
    ext x
    have hdis : x ∈ P.openStrip → x ∉ hamiltonZeroCircleMap phi ⁻¹' {(a : C0)} :=
      fun hx => Set.disjoint_left.mp hstripavoid hx
    simp only [mem_union, mem_sdiff]
    tauto
  have hPavoid : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1)
      (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)})ᶜ := by
    intro z hz hzbad
    exact Set.disjoint_left.mp hVavoid (hPV hz) hzbad
  have hlateral := P.isOpen_lateral_image he.closed (by norm_num : (1 / 2 : ℝ) ≤ 1) hopen
  exact ⟨P, G, N, hcut, hcompact, hcutfront, hN, heN, hSN, hGzero,
    hGfixed, hGa, hGb, hlateral, hPavoid, hGslab a hrhogap hetagap rfl, hNVavoid,
    hnewfront, hGtail⟩

end PoincareConjecture.M76
