import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.MarkedDiskChain
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.ResolutionStripBoundary

/-!
# The alternate five-piece resolution with its complete marked boundary

Construct the first exterior disk, left resolution strip, middle disk, right
resolution strip, and last exterior disk by four actual interval attachments.
The old tube frontier condition determines the new disk's entire marked boundary.
See Dehn039, section 6, and Hatcher, section 3.1, printed pp. 56--57.
-/

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareMT.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "i0" => (0 : unitInterval)
local notation "i1" => (1 : unitInterval)
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)

/-- Construct the actual alternate resolution from its original exterior
pieces and tube. The eight finite PL source identifications, all five map
restrictions, full image and preimages, and complete marked boundary survive. -/
theorem exists_marked_alternate_resolution_disk_map
    {EA EM EC F X ι : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [FiniteDimensional ℝ EA]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    [NormedAddCommGroup EC] [NormedSpace ℝ EC] [FiniteDimensional ℝ EC]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {SA QA WA : Set EA} {SM QM LM RM : Set EM} {SC QC WC : Set EC}
    {aA bA : EA} {aL bL aR bR : EM} {aC bC : EC}
    (hSA : IsFinitePLBallPair P2 SA QA) (hSM : IsFinitePLBallPair P2 SM QM)
    (hSC : IsFinitePLBallPair P2 SC QC)
    (hWA : IsFinitePLBallPair ℝ WA {aA, bA})
    (hLM : IsFinitePLBallPair ℝ LM {aL, bL})
    (hRM : IsFinitePLBallPair ℝ RM {aR, bR})
    (hWC : IsFinitePLBallPair ℝ WC {aC, bC})
    (hWAQ : WA ⊆ QA) (hLMQ : LM ⊆ QM) (hRMQ : RM ⊆ QM) (hWCQ : WC ⊆ QC)
    (hdisj : Disjoint LM RM) (habA : aA ≠ bA) (habL : aL ≠ bL) (habC : aC ≠ bC)
    (pA : I01 ≃ₜ WA) (pL : I01 ≃ₜ LM) (pR : I01 ≃ₜ RM) (pC : I01 ≃ₜ WC)
    (hpA : pA.IsFinitePL) (hpL : pL.IsFinitePL)
    (hpR : pR.IsFinitePL) (hpC : pC.IsFinitePL)
    (hpA0 : (pA i0 : EA) = aA) (hpA1 : (pA i1 : EA) = bA)
    (hpL0 : (pL i0 : EM) = aL) (hpL1 : (pL i1 : EM) = bL)
    (hpR0 : (pR i0 : EM) = aR) (hpR1 : (pR i1 : EM) = bR)
    (hpC0 : (pC i0 : EC) = aC) (hpC1 : (pC i1 : EC) = bC)
    {fA : EA → X} {fM : EM → X} {fC : EC → X} {τ : C3 → X}
    (hfA : PolyhedralPLInCharts e fA SA) (hfM : PolyhedralPLInCharts e fM SM)
    (hfC : PolyhedralPLInCharts e fC SC) (hτ : PolyhedralPLInCharts e τ tube)
    (hA : ∀ t : I01, fA (pA t) = τ (((-1, 1), (t : ℝ)) : C3))
    (hL : ∀ t : I01, fM (pL t) = τ (((-1, -1), (t : ℝ)) : C3))
    (hR : ∀ t : I01, fM (pR t) = τ (((1, -1), (t : ℝ)) : C3))
    (hC : ∀ t : I01, fC (pC t) = τ (((1, 1), (t : ℝ)) : C3))
    (Z : Set X) (hτF : ∀ z ∈ tube, τ z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1)
    (hQA : QA = (SA ∩ fA ⁻¹' Z) ∪ WA)
    (hQM : QM = ((SM ∩ fM ⁻¹' Z) ∪ RM) ∪ LM)
    (hQC : QC = (SC ∩ fC ⁻¹' Z) ∪ WC)
    (hmarkA : WA ∩ fA ⁻¹' Z = {aA, bA})
    (hmarkL : LM ∩ fM ⁻¹' Z = {aL, bL})
    (hmarkR : RM ∩ fM ⁻¹' Z = {aR, bR})
    (hmarkC : WC ∩ fC ⁻¹' Z = {aC, bC}) :
    ∃ (nA : SA ≃ₜ TR) (nL : source ≃ₜ TL) (mL : T ≃ₜ TR) (nM : SM ≃ₜ TL)
      (nAML : T ≃ₜ TR) (nR : source ≃ₜ TL) (mR : T ≃ₜ TR) (nC : SC ≃ₜ TL)
      (g : P2 → X),
      let k := fun x : T ↦ (mR ⟨nAML x, Or.inl (nAML x).property⟩ : P2)
      let jA := fun x : SA ↦ k ⟨mL ⟨nA x, Or.inl (nA x).property⟩,
        Or.inl (mL ⟨nA x, Or.inl (nA x).property⟩).property⟩
      let jL := fun x : source ↦ k ⟨mL ⟨nL x, Or.inr (nL x).property⟩,
        Or.inl (mL ⟨nL x, Or.inr (nL x).property⟩).property⟩
      let jM := fun x : SM ↦ k ⟨nM x, Or.inr (nM x).property⟩
      let jR := fun x : source ↦ (mR ⟨nR x, Or.inr (nR x).property⟩ : P2)
      nA.IsFinitePL ∧ nL.IsFinitePL ∧ mL.IsFinitePL ∧ nM.IsFinitePL ∧
      nAML.IsFinitePL ∧ nR.IsFinitePL ∧ mR.IsFinitePL ∧ nC.IsFinitePL ∧
      PolyhedralPLInCharts e g T ∧
      (∀ x : SA, g (jA x) = fA x) ∧
      (∀ x : source, g (jL x) = τ (alternate (1 / 4) false x)) ∧
      (∀ x : SM, g (jM x) = fM x) ∧
      (∀ x : source, g (jR x) = τ (alternate (1 / 4) true x)) ∧
      (∀ x : SC, g (nC x) = fC x) ∧
      g '' T = (((fA '' SA ∪ τ '' (alternate (1 / 4) false '' source)) ∪
        fM '' SM) ∪ τ '' (alternate (1 / 4) true '' source)) ∪ fC '' SC ∧
      IsFinitePLBallPair P2 T (T ∩ g ⁻¹' Z) ∧
      ∀ U : Set X, T ∩ g ⁻¹' U =
        (((jA '' {x : SA | fA x ∈ U} ∪
          jL '' {x : source | τ (alternate (1 / 4) false x) ∈ U}) ∪
          jM '' {x : SM | fM x ∈ U}) ∪
          jR '' {x : source | τ (alternate (1 / 4) true x) ∈ U}) ∪
          (fun x : SC ↦ (nC x : P2)) '' {x : SC | fC x ∈ U} := by
  have hb : (1 / 4 : ℝ) < 1 := by norm_num
  have hrect : IsFinitePLBallPair P2 source stripRim :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  obtain ⟨hminus, pminus, hpminus, hpminusVal⟩ := exists_arm_parameter (-1)
  obtain ⟨hplus, pplus, hpplus, hpplusVal⟩ := exists_arm_parameter 1
  have hminusQ : arm (-1) ⊆ stripRim := fun _ hx ↦ Or.inr ⟨hx.1, Or.inl hx.2⟩
  have hplusQ : arm 1 ⊆ stripRim := fun _ hx ↦ Or.inr ⟨hx.1, Or.inr hx.2⟩
  have hdisjoint : Disjoint (arm (-1)) (arm 1) := by
    apply disjoint_left.mpr
    intro x hx hy
    have hneg : x.2 = -1 := hx.2
    have hpos : x.2 = 1 := hy.2
    linarith
  have hends (u : ℝ) : ((0, u) : P2) ≠ (1, u) := by
    intro heq
    have h01 : (0 : ℝ) = 1 := congrArg Prod.fst heq
    norm_num at h01
  have hchartEnds {V : Set P2} (q : I01 ≃ₜ V) : (q i0 : P2) ≠ (q i1 : P2) := by
    intro heq
    have h01 := congrArg (fun t : I01 ↦ (t : ℝ)) (q.injective (Subtype.ext heq))
    norm_num at h01
  have hstrip (positive : Bool) :
      PolyhedralPLInCharts e (τ ∘ alternate (1 / 4) positive) source := by
    have hs := (finitePiecewiseAffineOn_maps (1 / 4) positive).2
    have hcopy := hs
    obtain ⟨K, hK, hKs, _⟩ := hcopy
    have hr : FinitePiecewiseAffineOn (alternate (1 / 4) positive) K.space := by
      simpa only [hKs] using hs
    have hm : MapsTo (alternate (1 / 4) positive) K.space tube := by
      simpa only [hKs] using (mapsTo_tube hb.le positive).2
    simpa only [hKs] using hτ.comp_finitePiecewiseAffineOn K hK hr hm
  have hrim (positive : Bool) : stripRim =
      ((source ∩ (τ ∘ alternate (1 / 4) positive) ⁻¹' Z) ∪ arm (-1)) ∪ arm 1 := by
    have hpre := resolution_strip_frontier_preimage τ hτF hb.le true positive
    simp only [resolutionMap, ↓reduceIte] at hpre
    rw [hpre]
    exact stripRim_eq_ends_union_arms
  have hmark (positive : Bool) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      arm u ∩ (τ ∘ alternate (1 / 4) positive) ⁻¹' Z = {(0, u), (1, u)} := by
    simpa only [resolutionMap, ↓reduceIte] using
      resolution_strip_arm_frontier_inter τ hτF hb.le hu true positive
  have hagreeA (t : I01) : fA (pA t) =
      (τ ∘ alternate (1 / 4) false) (pplus t) := by
    change fA (pA t) = τ (alternate (1 / 4) false (pplus t))
    rw [hpplusVal, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.2.2]
    exact hA t
  have hagreeL (t : I01) : (τ ∘ alternate (1 / 4) false) (pminus t) = fM (pL t) := by
    change τ (alternate (1 / 4) false (pminus t)) = fM (pL t)
    rw [hpminusVal, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.2.1]
    exact (hL t).symm
  obtain ⟨nA, nL, pAL, gAL, V1, q1, hnA, hnL, _, _, _, _, _,
      hgAL, hgA, hgL, himAL, hpreAL, hballAL, _, hV1, hq1, hq1val, hmarkV1⟩ :=
    exists_marked_interval_disk_map e hcompat hSA hrect hWA hplus hWAQ hplusQ
      habA (hends 1) pA pplus hpA hpplus hpA0 hpA1 (hpplusVal 0) (hpplusVal 1)
      hfA (hstrip false) hagreeA Z hQA hmarkA (hmark false 1 (by norm_num))
      hminus hminusQ (Set.disjoint_iff_inter_eq_empty.mp hdisjoint.symm)
      pminus hpminus (hpminusVal 0) (hpminusVal 1) (hrim false)
      (hmark false (-1) (by norm_num))
  have hagreeM (t : I01) : gAL (q1 t) = fM (pL t) := by
    rw [hq1val, hgL]
    exact hagreeL t
  obtain ⟨mL, nM, pAML, gAML, V, q, hmL, hnM, _, _, _, _, _,
      hgAML, hgALkeep, hgM, himAML, hpreAML, hballAML, _, hV, hq, hqval, hmarkV⟩ :=
    exists_marked_interval_disk_map e hcompat hballAL hSM hV1 hLM
      subset_union_right hLMQ (hchartEnds q1) habL q1 pL hq1 hpL rfl rfl hpL0 hpL1
      hgAL hfM hagreeM Z rfl hmarkV1 hmarkL hRM hRMQ
      (Set.disjoint_iff_inter_eq_empty.mp hdisj) pR hpR hpR0 hpR1 hQM hmarkR
  have hagreeR (t : I01) : gAML (q t) =
      (τ ∘ alternate (1 / 4) true) (pminus t) := by
    rw [hqval, hgM]
    change fM (pR t) = τ (alternate (1 / 4) true (pminus t))
    rw [hpminusVal, (arm_endpoints hb (t : ℝ)).2.2.2.2.1]
    exact hR t
  have hagreeC (t : I01) : (τ ∘ alternate (1 / 4) true) (pplus t) = fC (pC t) := by
    change τ (alternate (1 / 4) true (pplus t)) = fC (pC t)
    rw [hpplusVal, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.1]
    exact (hC t).symm
  have hrimR : stripRim =
      ((source ∩ (τ ∘ alternate (1 / 4) true) ⁻¹' Z) ∪ arm 1) ∪ arm (-1) := by
    rw [hrim true]
    ac_rfl
  obtain ⟨nAML, nR, mR, nC, g, hnAML, hnR, hmR, hnC, _, _,
      hg, hgOld, hgR, hgC, him, hball, hpre⟩ :=
    exists_three_piece_marked_disk_map e hcompat hballAML hrect hSC hV hminus hplus hWC
      subset_union_right hminusQ hplusQ hWCQ hdisjoint (hchartEnds q) (hends (-1)) habC
      q pminus pplus pC hq hpminus hpplus hpC rfl rfl
      (hpminusVal 0) (hpminusVal 1) (hpplusVal 0) (hpplusVal 1) hpC0 hpC1
      hgAML (hstrip true) hfC hagreeR hagreeC Z rfl hrimR hQC hmarkV
      (hmark true (-1) (by norm_num)) (hmark true 1 (by norm_num)) hmarkC
  let k := fun x : T ↦ (mR ⟨nAML x, Or.inl (nAML x).property⟩ : P2)
  let jA := fun x : SA ↦ k ⟨mL ⟨nA x, Or.inl (nA x).property⟩,
    Or.inl (mL ⟨nA x, Or.inl (nA x).property⟩).property⟩
  let jL := fun x : source ↦ k ⟨mL ⟨nL x, Or.inr (nL x).property⟩,
    Or.inl (mL ⟨nL x, Or.inr (nL x).property⟩).property⟩
  let jM := fun x : SM ↦ k ⟨nM x, Or.inr (nM x).property⟩
  let jR := fun x : source ↦ (mR ⟨nR x, Or.inr (nR x).property⟩ : P2)
  have hfinalA (x : SA) : g (jA x) = fA x := by
    change g (k _) = _
    rw [hgOld, hgALkeep, hgA]
  have hfinalL (x : source) : g (jL x) = τ (alternate (1 / 4) false x) := by
    change g (k _) = _
    rw [hgOld, hgALkeep, hgL]
    rfl
  have hfinalM (x : SM) : g (jM x) = fM x := by
    change g (k _) = _
    rw [hgOld, hgM]
  refine ⟨nA, nL, mL, nM, nAML, nR, mR, nC, g,
    hnA, hnL, hmL, hnM, hnAML, hnR, hmR, hnC,
    hg, hfinalA, hfinalL, hfinalM, hgR, hgC, ?_, hball, ?_⟩
  · rw [him, himAML, himAL]
    simp only [image_comp]
  · intro U
    ext y
    constructor
    · intro hy
      rcases (hpre U).subset hy with (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩
      · rcases (hpreAML U).subset ⟨x.property, hx⟩ with ⟨z, hz, hzx⟩ | ⟨z, hz, hzx⟩
        · rcases (hpreAL U).subset ⟨z.property, hz⟩ with ⟨w, hw, hwz⟩ | ⟨w, hw, hwz⟩
          · refine Or.inl (Or.inl (Or.inl (Or.inl ⟨w, hw, ?_⟩)))
            exact congrArg k (Subtype.ext ((congrArg (fun z : T ↦ (mL z : P2))
              (Subtype.ext hwz)).trans hzx))
          · refine Or.inl (Or.inl (Or.inl (Or.inr ⟨w, hw, ?_⟩)))
            exact congrArg k (Subtype.ext ((congrArg (fun z : T ↦ (mL z : P2))
              (Subtype.ext hwz)).trans hzx))
        · exact Or.inl (Or.inl (Or.inr ⟨z, hz, congrArg k (Subtype.ext hzx)⟩))
      · exact Or.inl (Or.inr ⟨x, hx, rfl⟩)
      · exact Or.inr ⟨x, hx, rfl⟩
    · rintro ((((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) |
        ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
      · refine ⟨Or.inl (mR _).property, ?_⟩
        change g (jA x) ∈ U
        rw [hfinalA]
        exact hx
      · refine ⟨Or.inl (mR _).property, ?_⟩
        change g (jL x) ∈ U
        rw [hfinalL]
        exact hx
      · refine ⟨Or.inl (mR _).property, ?_⟩
        change g (jM x) ∈ U
        rw [hfinalM]
        exact hx
      · refine ⟨Or.inl (mR _).property, ?_⟩
        change g (jR x) ∈ U
        rw [hgR]
        exact hx
      · refine ⟨Or.inr (nC x).property, ?_⟩
        change g (nC x) ∈ U
        rw [hgC]
        exact hx

end PoincareMT.M76.Dehn.PolygonalCrossingResolution
