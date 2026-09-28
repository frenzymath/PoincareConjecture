import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandCutContacts
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapBandGluing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_inter_subset_frontier_of_regular
    {A B : Set AnnulusCoordinates} (hB : closure (interior B) = B)
    (hinter : A ∩ B ⊆ frontier B) : A ∩ B ⊆ frontier A := by
  have hd : Disjoint (interior A) (interior B) := by
    apply disjoint_left.mpr
    intro z hzA hzB
    exact disjoint_left.mp disjoint_interior_frontier hzB
      (hinter ⟨interior_subset hzA, interior_subset hzB⟩)
  have hd' := hd.closure_right isOpen_interior
  rw [hB] at hd'
  exact fun _ hz => ⟨subset_closure hz.1, fun hint => disjoint_left.mp hd' hint hz.2⟩

section Band

variable {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

theorem m64Intrinsic_band_cap_inter_subset_frontier
    {C A : Set AnnulusCoordinates} (hAC : A ⊆ C)
    (hinter : C ∩ B.carrier ⊆ B.leftCut ∪ B.rightCut) :
    A ∩ B.carrier ⊆ frontier A := by
  apply m64Intrinsic_inter_subset_frontier_of_regular B.closure_interior_carrier
  intro z hz
  apply B.outer_boundaries_subset_frontier
  rcases hinter ⟨hAC hz.1, hz.2⟩ with hl | hr
  · exact Or.inl (Or.inr hl)
  · exact Or.inr hr

theorem m64Intrinsic_cap_attachment_cut_subset_chord
    (face : SmoothFace AnnulusCoordinates) (right : Bool)
    {U K C N : Set AnnulusCoordinates}
    (hregion : B.carrier \ B.lowerArc ⊆ U) (hdisj : Disjoint U K)
    (hface : face.carrier ⊆ C)
    (hinter : C ∩ B.carrier ⊆ B.leftCut ∪ B.rightCut)
    (hselected : N ∩ C ⊆ face.carrier)
    (hfront : N ∩ frontier face.carrier ⊆ K ∪ (face.boundary 0).map '' Icc (0 : ℝ) 1)
    (hcutN : (B.endpointEdge right).map '' Icc (0 : ℝ) 1 ⊆ N)
    (hcutC : (B.endpointEdge right).map '' Icc (0 : ℝ) 1 ⊆ C)
    (hbase : (B.endpointEdge right).map 0 ∈ (face.boundary 0).map '' Icc (0 : ℝ) 1) :
    (B.endpointEdge right).map '' Icc (0 : ℝ) 1 ⊆
      (face.boundary 0).map '' Icc (0 : ℝ) 1 := by
  rintro z ⟨t, ht, rfl⟩
  by_cases ht0 : t = 0
  · exact ht0 ▸ hbase
  have hzN := hcutN ⟨t, ht, rfl⟩
  have hzC := hcutC ⟨t, ht, rfl⟩
  have hzB := B.isClosed_carrier.frontier_subset
    (B.endpointEdge_subset_frontier right ⟨t, ht, rfl⟩)
  have hzfront := m64Intrinsic_band_cap_inter_subset_frontier B hface hinter
    ⟨hselected ⟨hzN, hzC⟩, hzB⟩
  apply (hfront ⟨hzN, hzfront⟩).resolve_left
  intro hzK
  exact disjoint_left.mp hdisj (m64Intrinsic_band_positive_endpoint_subset_region B right
    hregion ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩, rfl⟩) hzK

theorem m64Intrinsic_cap_attachment_open_cut_interior
    (face : SmoothFace AnnulusCoordinates)
    (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (basis : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : convexHull ℝ (range basis) ⊆ C.source)
    (hcarrier : face.carrier = C '' convexHull ℝ (range basis))
    (hboundary : ∀ k : Fin 3, (face.boundary k).map = C ∘
      affineChartSegment (basis (k.succAbove 0)) (basis (k.succAbove 1)))
    (right terminal : Bool) {N : Set AnnulusCoordinates}
    (hbase : (B.endpointEdge right).map 0 =
      (face.boundary 0).map (if terminal then 1 else 0))
    (hfar : (face.boundary 0).map (if terminal then 0 else 1) ∉ N)
    (hcutN : (B.endpointEdge right).map '' Icc (0 : ℝ) 1 ⊆ N)
    (hshared : (B.endpointEdge right).map '' Icc (0 : ℝ) 1 ⊆
      (face.boundary 0).map '' Icc (0 : ℝ) 1)
    (hinter : face.carrier ∩ B.carrier ⊆ frontier face.carrier) :
    (B.endpointEdge right).map '' Ioo (0 : ℝ) 1 ⊆ interior (face.carrier ∪ B.carrier) := by
  rintro z ⟨u, hu, rfl⟩
  have hzN := hcutN ⟨u, Ioo_subset_Icc_self hu, rfl⟩
  obtain ⟨t, ht, htu⟩ := hshared ⟨u, Ioo_subset_Icc_self hu, rfl⟩
  have hbaseNe : (B.endpointEdge right).map u ≠ (B.endpointEdge right).map 0 := by
    intro heq
    exact hu.1.ne' (B.endpointEdge_injective right (Ioo_subset_Icc_self hu)
      (by norm_num) heq)
  have ht0 : t ≠ 0 := by
    intro ht0
    rw [ht0] at htu
    cases terminal
    · exact hbaseNe (htu.symm.trans hbase.symm)
    · exact hfar (htu.symm ▸ hzN)
  have ht1 : t ≠ 1 := by
    intro ht1
    rw [ht1] at htu
    cases terminal
    · exact hfar (htu.symm ▸ hzN)
    · exact hbaseNe (htu.symm.trans hbase.symm)
  rw [← htu]
  exact m64Intrinsic_cap_band_attachment_interior face C basis hsource hcarrier hboundary
    B 0 right ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩ hu
    htu hshared hinter

end Band

end PoincareConjecture
