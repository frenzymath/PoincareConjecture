import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.CompressedCircleModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.ComponentCircleRims
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.ComponentCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.OriginalCyclicAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.SharedBoundaryConeUnion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

open Classical in
theorem exists_hamiltonZero_compressed_component_annulus
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi psi : C(H0, H0)) {R A : Set X0}
    (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {theta other : C0} (hne : theta ≠ other)
    (hreg : HamiltonZeroSecondCoordinateRegularity e R phi theta)
    {a b : ℝ}
    (hN : PLDomain e (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) ∪
          (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {other})))
    (T : Set X0) (hT : T ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta})
    (hcomponent : ∀ x ∈ T, connectedComponentIn
      (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) x = T)
    (hrim : (T ∩ frontier R).Nonempty) (x : T)
    [IsCyclic (FundamentalGroup T x)] [Nontrivial (FundamentalGroup T x)] :
    ∃ H : squareAnnulus 8 1 ≃ₜ T, ∃ f : (ℝ × ℝ) → X0,
      PolyhedralPLInCharts e f (squareAnnulus 8 1) ∧
      (∀ z : squareAnnulus 8 1, f z = (H z : X0)) ∧
      ∀ z : squareAnnulus 8 1,
        depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
          (H z : X0) ∈ frontier R := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let S := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}
  obtain ⟨s, F, K, B, g, hFc, hFi, _, hK, hBK, _, hKs, hBs,
    hgPL, hgi, hFg, hgS, hpure, hcofaces, hlinks,
    m, J, gamma, hJ, hdis, hcover, hfaces⟩ :=
    exists_hamiltonZero_compressed_circle_incidence e phi psi heR hA hAR hfixed hne hreg hN hfront
  let : DecidableEq (s → ℝ × V3) := Classical.decEq _
  have hFK (y : X0) (hy : y ∈ S) : F y ∈ K.space := hKs.symm.subset ⟨y, hy, rfl⟩
  have hgF (y : X0) (hy : y ∈ S) : g (F y) = y := hFi (hFg (F y) (hFK y hy))
  have hTconn : IsConnected T := by
    rw [← hcomponent x x.property]
    exact isConnected_connectedComponentIn_iff.mpr (hT x.property)
  obtain ⟨D, hD⟩ := K.exists_edgeComponentComplex_of_isConnected hK
    (hTconn.image F hFc.continuousOn) (by
      rintro _ ⟨y, hy, rfl⟩
      exact hFK y (hT hy))
  let P := K.edgeComponentComplex D
  have hPK : P.space ⊆ K.space := SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le D)
  have hPg : g '' P.space = T := by
    apply Subset.antisymm
    · rw [← hcomponent x x.property]
      apply ((K.edgeComponentComplex_isPathConnected D).isConnected.image g
        (hgPL.continuousOn.mono hPK)).isPreconnected.subset_connectedComponentIn
      · exact ⟨F x, hD ⟨x, x.property, rfl⟩, hgF x (hT x.property)⟩
      · rintro _ ⟨z, hz, rfl⟩
        exact hgS.subset ⟨z, hPK hz, rfl⟩
    · intro y hy
      exact ⟨F y, hD ⟨y, hy, rfl⟩, hgF y (hT hy)⟩
  have hFT : F '' T = P.space := by
    apply Subset.antisymm hD
    intro z hz
    exact ⟨g z, hPg.subset ⟨z, hz, rfl⟩, hFg z (hPK hz)⟩
  let HC : P.space ≃ₜ T := Homeomorph.ofSetInverse g F P.space T
    (hgPL.continuousOn.mono hPK) hFc.continuousOn
    (fun z hz => hPg.subset ⟨z, hz, rfl⟩)
    (fun y hy => hFT.subset ⟨y, hy, rfl⟩)
    (fun z hz => hFg z (hPK hz)) (fun y hy => hgF y (hT hy))
  have hHC (z : P.space) : (HC z : X0) = g z := rfl
  have hBmem (z : s → ℝ × V3) (hz : z ∈ K.space) : g z ∈ frontier R ↔ z ∈ B.space := by
    rw [hBs]
    constructor
    · intro hzr
      exact ⟨g z, ⟨hgS.subset ⟨z, hz, rfl⟩, hzr⟩, hFg z hz⟩
    · rintro ⟨y, hy, heq⟩
      have hgy : g z = y := hFi ((hFg z hz).trans heq.symm)
      exact hgy.symm ▸ hy.2
  obtain ⟨r, _, hcomponents⟩ := K.exists_component_circle_rims B hK hpure
    (by intro v hv; convert! hlinks v hv) hcofaces
    J gamma hJ hdis (hcover.trans hBs.symm) hfaces
  obtain ⟨hP, _, _, hPconn, _, hJd, hdisd, hcoverd, _, _⟩ := hcomponents D
  let β := {i : Fin m // r i = D}
  let : Fintype β := Fintype.ofFinite β
  have hβ : Nonempty β := by
    obtain ⟨y, hyT, hyr⟩ := hrim
    have hyP : F y ∈ P.space := hFT.subset ⟨y, hyT, rfl⟩
    have hyB : F y ∈ B.space := (hBmem (F y) (hPK hyP)).mp
      ((hgF y (hT hyT)).symm ▸ hyr)
    obtain ⟨i, _⟩ := mem_iUnion.mp (hcoverd.symm.subset ⟨hyP, hyB⟩)
    exact ⟨i⟩
  let : Nonempty β := hβ
  let BP := P ⊓ B
  have hBPs : BP.space = P.space ∩ B.space :=
    K.space_inf_eq_inter_of_le P B (K.edgeComponentComplex_le D) hBK
  have hBPM (z : s → ℝ × V3) (hz : z ∈ P.space) : g z ∈ frontier R ↔ z ∈ BP.space := by
    rw [hBPs, mem_inter_iff, and_iff_right hz]
    exact hBmem z (hPK hz)
  obtain ⟨U, hU, hUP⟩ := exists_open_edge_component_neighborhood K hK D
  have hTU : T = S ∩ F ⁻¹' U := by
    ext y
    constructor
    · intro hy
      have hyP := hFT.subset ⟨y, hy, rfl⟩
      exact ⟨hT hy, (hUP.symm.subset hyP).2⟩
    · rintro ⟨hyS, hyU⟩
      have hyP := hUP.subset ⟨hFK y hyS, hyU⟩
      exact (hgF y hyS) ▸ hPg.subset ⟨F y, hyP, rfl⟩
  have hlocal := restrict_marked_surface_charts_to_open_piece e (hU.preimage hFc) hTU
    (exists_hamiltonZero_compressed_marked_surface_chart e phi psi heR hA hAR hfixed hne hreg hN hfront)
  let xP := HC.symm x
  let Egroup := HC.symm.fundamentalGroupMulEquiv x
  let : IsCyclic (FundamentalGroup P.space xP) := isCyclic_of_surjective Egroup Egroup.surjective
  let : Nontrivial (FundamentalGroup P.space xP) := Egroup.injective.nontrivial
  obtain ⟨order, Aparam, hAparam, hlo, hhi, f, hf, hfeq⟩ :=
    exists_hamiltonZero_original_cyclic_marked_annulus e hN
      (by intro y hy; rw [hfront]; exact Or.inr (Or.inl (hT hy)))
      P BP hP inf_le_left HC g hHC (hgPL.restrict_finite P hP hPK) hBPM hlocal
      (fun i : β => J i.val) (fun i => le_inf (hJd i).1 (hJd i).2.1)
      hdisd (hcoverd.trans hBPs.symm) (fun i => gamma i.val) (fun i => (hJd i).2.2.2)
      hPconn.isConnected xP
  refine ⟨Aparam.trans HC, f, hf, fun z => (hfeq z).trans (hHC (Aparam z)).symm, ?_⟩
  intro z
  change depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔ g (Aparam z) ∈ frontier R
  rw [hlo z, hhi z, hBmem (Aparam z) (hPK (Aparam z).property)]
  have hm : (Aparam z : s → ℝ × V3) ∈ B.space ↔
      ∃ i : β, (Aparam z : s → ℝ × V3) ∈ (J i.val).space := by
    rw [← mem_iUnion, hcoverd, mem_inter_iff, and_iff_right (Aparam z).property]
  rw [hm]
  constructor
  · rintro (hl | hr)
    · exact ⟨order false, hl⟩
    · exact ⟨order true, hr⟩
  · rintro ⟨i, hi⟩
    obtain ⟨b, rfl⟩ := order.surjective i
    cases b
    · exact Or.inl hi
    · exact Or.inr hi

end PoincareConjecture.M76
