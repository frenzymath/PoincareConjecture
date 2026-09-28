import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Boundary.LabelPasting
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Copies



set_option autoImplicit false
open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.NonspanningChainGeometry

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)
local notation "Strip" => PolygonalCrossingResolution.source

open PolygonalCrossingResolution NonspanningChainBoundaryData

variable {SA SM SC : Set P2} {pA pL pR pC : I01 → P2}
  (s : NonspanningChainGeometry SA SM SC pA pL pR pC)

theorem exists_boundary_label {X : Type*} (f u : P2 → X) (Z : Set X)
    (hSA : IsClosed SA) (hSM : IsClosed SM) (hSC : IsClosed SC)
    (hQA : frontier SA = (SA ∩ f ⁻¹' Z) ∪ range pA)
    (hQM : frontier SM = ((SM ∩ f ⁻¹' Z) ∪ range pR) ∪ range pL)
    (hQC : frontier SC = (SC ∩ f ⁻¹' Z) ∪ range pC)
    (hQS : stripRim = ((Strip ∩ u ⁻¹' Z) ∪ arm (-1)) ∪ arm 1)
    (hmarkA : range pA ∩ f ⁻¹' Z = {pA 0, pA 1})
    (hmarkL : range pL ∩ f ⁻¹' Z = {pL 0, pL 1})
    (hmarkR : range pR ∩ f ⁻¹' Z = {pR 0, pR 1})
    (hmarkC : range pC ∩ f ⁻¹' Z = {pC 0, pC 1})
    (hplus : arm 1 ∩ u ⁻¹' Z = {(0, 1), (1, 1)})
    (hminus : arm (-1) ∩ u ⁻¹' Z = {(0, -1), (1, -1)})
    (hdisj : Disjoint (range pL) (range pR))
    (hA : ∀ t, f (pA t) = u ((t : ℝ), 1))
    (hL : ∀ t, f (pL t) = u ((t : ℝ), -1))
    (hR : ∀ t, f (pR t) = u ((t : ℝ), -1))
    (hC : ∀ t, f (pC t) = u ((t : ℝ), 1)) :
    ∃ g : P2 → X,
      frontier T = T ∩ g ⁻¹' Z ∧
      (∀ x : SA, g (s.copyA x) = f x) ∧
      (∀ x : Strip, g (s.copyL x) = u x) ∧
      (∀ x : SM, g (s.copyM x) = f x) ∧
      (∀ x : Strip, g (s.copyR x) = u x) ∧
      ∀ x : SC, g (s.copyC x) = f x := by
  let B := s.boundary
  have hAS : range pA ⊆ SA := (subset_union_left.trans B.first_union.subset).trans
    hSA.frontier_subset
  have hLS : range pL ⊆ SM := (subset_union_left.trans B.middle_union.subset).trans
    hSM.frontier_subset
  have hCS : range pC ⊆ SC := (subset_union_left.trans B.last_union.subset).trans
    hSC.frontier_subset
  have hplusS : arm 1 ⊆ Strip := by
    intro x hx
    exact ⟨hx.1, by rw [show x.2 = 1 from hx.2]; norm_num⟩
  have hminusS : arm (-1) ⊆ Strip := by
    intro x hx
    exact ⟨hx.1, by rw [show x.2 = -1 from hx.2]; norm_num⟩
  have hpm : arm 1 ∩ arm (-1) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h0 : x.2 = 1 := hx.1.2
    have h1 : x.2 = -1 := hx.2.2
    linarith
  obtain ⟨g1, h1A, h1L, hpre1⟩ := exists_attachment_label s.nA s.nL f u
    (by
      intro x y hxy
      obtain ⟨t, hx, hy⟩ := (s.fiberAL x y).mp hxy
      rw [hx, hy]
      exact hA t) (f 0)
  obtain ⟨hD1, hV1⟩ := remaining_eq_mark s.nA s.nL hAS hplusS
    B.first_union B.left_union B.first_inter B.left_inter hQA hQS hmarkA hplus hpm
    h1L (hpre1 Z) B.first_outgoing
    (show ((0, -1) : P2) ∈ Strip by norm_num [source])
    (show ((1, -1) : P2) ∈ Strip by norm_num [source]) hminus B.first_remaining_union
    (by simpa [B.first_parameter] using B.first_remaining_inter)
  have hV1mark : B.firstOutgoing ∩ g1 ⁻¹' Z = {B.firstParameter 0, B.firstParameter 1} := by
    simpa [B.first_parameter] using hV1
  have hV1S : B.firstOutgoing ⊆ T := by
    rw [B.first_outgoing]
    rintro z ⟨x, _, rfl⟩
    exact Or.inr (s.nL x).property
  obtain ⟨g2, h2old, h2M, hpre2⟩ := exists_attachment_label s.mL s.nM g1 f
    (by
      intro x y hxy
      obtain ⟨t, hx, hy⟩ := (s.fiberM x y).mp hxy
      rw [hx, hy, h1L]
      exact (hL t).symm) (f 0)
  obtain ⟨hBAML, hV⟩ := remaining_eq_mark s.mL s.nM hV1S hLS
    rfl B.middle_union B.first_remaining_inter B.middle_inter
    (by rw [hD1, union_comm]) hQM hV1mark hmarkL
    (disjoint_iff_inter_eq_empty.mp hdisj) h2M (hpre2 Z) B.middle_outgoing
    (s.pR_mem 0) (s.pR_mem 1) hmarkR B.middle_remaining_union
    (by simpa only [B.middle_parameter] using B.middle_remaining_inter)
  have hVmark : B.middleOutgoing ∩ g2 ⁻¹' Z = {B.middleParameter 0, B.middleParameter 1} := by
    simpa only [B.middle_parameter] using hV
  have hVS : B.middleOutgoing ⊆ T := by
    rw [B.middle_outgoing]
    rintro z ⟨x, _, rfl⟩
    exact Or.inr (s.nM x).property
  obtain ⟨g3, h3old, h3R, hpre3⟩ := exists_attachment_label s.nAML s.nR g2 u
    (by
      intro x y hxy
      obtain ⟨t, hx, hy⟩ := (s.fiberR x y).mp hxy
      rw [hx, hy, h2M]
      exact hR t) (f 0)
  have hQS' : stripRim = ((Strip ∩ u ⁻¹' Z) ∪ arm 1) ∪ arm (-1) := by
    rw [hQS]
    ac_rfl
  obtain ⟨hDlast, hV2⟩ := remaining_eq_mark s.nAML s.nR hVS hminusS
    rfl B.right_union B.middle_remaining_inter B.right_inter
    (by rw [hBAML, union_comm]) hQS' hVmark hminus
    (by rw [inter_comm]; exact hpm) h3R (hpre3 Z) B.last_outgoing
    (show ((0, 1) : P2) ∈ Strip by norm_num [source])
    (show ((1, 1) : P2) ∈ Strip by norm_num [source]) hplus B.last_remaining_union
    (by simpa [B.last_parameter] using B.last_remaining_inter)
  have hV2mark : B.lastOutgoing ∩ g3 ⁻¹' Z = {B.lastParameter 0, B.lastParameter 1} := by
    simpa [B.last_parameter] using hV2
  have hV2S : B.lastOutgoing ⊆ T := by
    rw [B.last_outgoing]
    rintro z ⟨x, _, rfl⟩
    exact Or.inr (s.nR x).property
  obtain ⟨g4, h4old, h4C, hpre4⟩ := exists_attachment_label s.mR s.nC g3 f
    (by
      intro x y hxy
      obtain ⟨t, hx, hy⟩ := (s.fiberC x y).mp hxy
      rw [hx, hy, h3R]
      exact (hC t).symm) (f 0)
  have hrim := marked_attachment_rim_eq (fun x : T => (s.mR x : P2))
    (fun x : SC => (s.nC x : P2)) hV2S hCS rfl B.last_union
      B.last_remaining_inter B.last_inter
      (by rw [hDlast, union_comm])
      (show frontier SC = ((SC ∩ f ⁻¹' Z) ∪ ∅) ∪ range pC by simpa using hQC)
      hV2mark hmarkC (inter_empty _) (hpre4 Z)
  have hfront : frontier T = T ∩ g4 ⁻¹' Z := by
    rw [B.whole_frontier]
    simpa only [preimage_empty, image_empty, union_empty] using hrim
  refine ⟨g4, hfront, ?_, ?_, ?_, ?_, h4C⟩
  · intro x
    change g4 (s.mR _) = f x
    dsimp only [rightDiskCopy, leftDiskCopy]
    rw [h4old, h3old, h2old, h1A]
  · intro x
    change g4 (s.mR _) = u x
    dsimp only [rightDiskCopy, leftDiskCopy]
    rw [h4old, h3old, h2old, h1L]
  · intro x
    change g4 (s.mR _) = f x
    dsimp only [rightDiskCopy, leftDiskCopy]
    rw [h4old, h3old, h2M]
  · intro x
    change g4 (s.mR _) = u x
    dsimp only [rightDiskCopy, leftDiskCopy]
    rw [h4old, h3R]

end PoincareConjecture.M76.Dehn.NonspanningChainGeometry
