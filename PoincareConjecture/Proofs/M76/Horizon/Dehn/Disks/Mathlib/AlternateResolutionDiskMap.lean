import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ThreeDiskChainMap
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonalStripDiskAttachment











set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)

private theorem transport_arm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S W : Set E} {a b : E} (n : S ≃ₜ TL) (hn : n.IsFinitePL)
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hWS : W ⊆ S)
    (p : I01 ≃ₜ W) (hp : p.IsFinitePL)
    (hp0 : (p (0 : unitInterval) : E) = a)
    (hp1 : (p (1 : unitInterval) : E) = b) :
    ∃ (V : Set P2) (q : I01 ≃ₜ V),
      IsFinitePLBallPair ℝ V {(q 0 : P2), (q 1 : P2)} ∧ q.IsFinitePL ∧
      (∀ t : I01, (q t : P2) = n ⟨p t, hWS (p t).property⟩) ∧
      V = (fun x : S ↦ (n x : P2)) '' (Subtype.val ⁻¹' W) := by
  obtain ⟨f, hf, hval⟩ := hn
  have hinj : InjOn f S := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (n.injective (Subtype.ext
      ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm))))
  have hcopy := hW
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hfW : FinitePiecewiseAffineOn f W := by
    rw [← hKs]
    exact hf.restrict K hK (hKs.subset.trans hWS)
  obtain ⟨j, hj, hjval⟩ := hfW.exists_homeomorph_image (hinj.mono hWS)
  let q := p.trans j
  have hqval (t : I01) : (q t : P2) = f (p t) := hjval (p t)
  refine ⟨f '' W, q, ?_, hp.trans hj, ?_, ?_⟩
  · have h := hW.image hfW (hinj.mono hWS)
    rw [image_pair] at h
    simpa only [hqval, hp0, hp1] using h
  · intro t
    exact (hqval t).trans (hval ⟨p t, hWS (p t).property⟩).symm
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hWS hx⟩, hx, hval ⟨x, hWS hx⟩⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hval x).symm⟩







theorem exists_alternate_resolution_disk_map
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
    (hpA0 : (pA (0 : unitInterval) : EA) = aA)
    (hpA1 : (pA (1 : unitInterval) : EA) = bA)
    (hpL0 : (pL (0 : unitInterval) : EM) = aL)
    (hpL1 : (pL (1 : unitInterval) : EM) = bL)
    (hpR0 : (pR (0 : unitInterval) : EM) = aR)
    (hpR1 : (pR (1 : unitInterval) : EM) = bR)
    (hpC0 : (pC (0 : unitInterval) : EC) = aC)
    (hpC1 : (pC (1 : unitInterval) : EC) = bC)
    {fA : EA → X} {fM : EM → X} {fC : EC → X} {τ : C3 → X}
    (hfA : PolyhedralPLInCharts e fA SA) (hfM : PolyhedralPLInCharts e fM SM)
    (hfC : PolyhedralPLInCharts e fC SC) (hτ : PolyhedralPLInCharts e τ tube)
    (hA : ∀ t : I01, fA (pA t) = τ (((-1, 1), (t : ℝ)) : C3))
    (hL : ∀ t : I01, fM (pL t) = τ (((-1, -1), (t : ℝ)) : C3))
    (hR : ∀ t : I01, fM (pR t) = τ (((1, -1), (t : ℝ)) : C3))
    (hC : ∀ t : I01, fC (pC t) = τ (((1, 1), (t : ℝ)) : C3)) :
    ∃ (D : Set P2) (BC : Set EC)
      (nA : SA ≃ₜ TR) (nL : source ≃ₜ TL) (mL : T ≃ₜ TR) (nM : SM ≃ₜ TL)
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
      IsFinitePLBallPair ℝ BC {aC, bC} ∧ WC ∪ BC = QC ∧ WC ∩ BC = {aC, bC} ∧
      (∀ t : I01, jA ⟨pA t, hSA.1 (hWAQ (pA t).property)⟩ =
        jL ⟨((t : ℝ), 1), ⟨t.property, by norm_num⟩⟩) ∧
      (∀ t : I01, jL ⟨((t : ℝ), -1), ⟨t.property, by norm_num⟩⟩ =
        jM ⟨pL t, hSM.1 (hLMQ (pL t).property)⟩) ∧
      (∀ t : I01, jM ⟨pR t, hSM.1 (hRMQ (pR t).property)⟩ =
        jR ⟨((t : ℝ), -1), ⟨t.property, by norm_num⟩⟩) ∧
      (∀ t : I01, jR ⟨((t : ℝ), 1), ⟨t.property, by norm_num⟩⟩ =
        (nC ⟨pC t, hSC.1 (hWCQ (pC t).property)⟩ : P2)) ∧
      PolyhedralPLInCharts e g T ∧
      (∀ x : SA, g (jA x) = fA x) ∧
      (∀ x : source, g (jL x) = τ (alternate (1 / 4) false x)) ∧
      (∀ x : SM, g (jM x) = fM x) ∧
      (∀ x : source, g (jR x) = τ (alternate (1 / 4) true x)) ∧
      (∀ x : SC, g (nC x) = fC x) ∧
      g '' T = (((fA '' SA ∪ τ '' (alternate (1 / 4) false '' source)) ∪
        fM '' SM) ∪ τ '' (alternate (1 / 4) true '' source)) ∪ fC '' SC ∧
      IsFinitePLBallPair P2 T
        ((fun x : T ↦ (mR x : P2)) '' (Subtype.val ⁻¹' D) ∪
          (fun x : SC ↦ (nC x : P2)) '' (Subtype.val ⁻¹' BC)) ∧
      (∀ Z : Set X, T ∩ g ⁻¹' Z =
        (((jA '' {x : SA | fA x ∈ Z} ∪
          jL '' {x : source | τ (alternate (1 / 4) false x) ∈ Z}) ∪
          jM '' {x : SM | fM x ∈ Z}) ∪
          jR '' {x : source | τ (alternate (1 / 4) true x) ∈ Z}) ∪
          (fun x : SC ↦ (nC x : P2)) '' {x : SC | fC x ∈ Z}) ∧
      ∃ (BA : Set EA) (BL D1 BAML BR V1 V V2 : Set P2) (BM : Set EM)
        (q1 : I01 ≃ₜ V1) (q : I01 ≃ₜ V) (q2 : I01 ≃ₜ V2),
        q1.IsFinitePL ∧ q.IsFinitePL ∧ q2.IsFinitePL ∧
        WA ∪ BA = QA ∧ WA ∩ BA = {aA, bA} ∧
        arm 1 ∪ BL = stripRim ∧ arm 1 ∩ BL = {(0, 1), (1, 1)} ∧
        V1 = (fun x : source ↦ (nL x : P2)) '' (Subtype.val ⁻¹' arm (-1)) ∧
        (∀ t : I01, (q1 t : P2) =
          nL ⟨((t : ℝ), -1), ⟨t.property, by norm_num⟩⟩) ∧
        V1 ∪ D1 = (fun x : SA ↦ (nA x : P2)) '' (Subtype.val ⁻¹' BA) ∪
          (fun x : source ↦ (nL x : P2)) '' (Subtype.val ⁻¹' BL) ∧
        V1 ∩ D1 = {(q1 0 : P2), (q1 1 : P2)} ∧
        LM ∪ BM = QM ∧ LM ∩ BM = {aL, bL} ∧
        V = (fun x : SM ↦ (nM x : P2)) '' (Subtype.val ⁻¹' RM) ∧
        (∀ t : I01, (q t : P2) = nM ⟨pR t, hSM.1 (hRMQ (pR t).property)⟩) ∧
        V ∪ BAML = (fun x : T ↦ (mL x : P2)) '' (Subtype.val ⁻¹' D1) ∪
          (fun x : SM ↦ (nM x : P2)) '' (Subtype.val ⁻¹' BM) ∧
        V ∩ BAML = {(q 0 : P2), (q 1 : P2)} ∧
        arm (-1) ∪ BR = stripRim ∧ arm (-1) ∩ BR = {(0, -1), (1, -1)} ∧
        V2 = (fun x : source ↦ (nR x : P2)) '' (Subtype.val ⁻¹' arm 1) ∧
        (∀ t : I01, (q2 t : P2) =
          nR ⟨((t : ℝ), 1), ⟨t.property, by norm_num⟩⟩) ∧
        V2 ∪ D = (fun x : T ↦ (nAML x : P2)) '' (Subtype.val ⁻¹' BAML) ∪
          (fun x : source ↦ (nR x : P2)) '' (Subtype.val ⁻¹' BR) ∧
        V2 ∩ D = {(q2 0 : P2), (q2 1 : P2)} ∧
        (∀ (x : SA) (y : source), (nA x : P2) = nL y ↔
          ∃ t : I01, (x : EA) = pA t ∧ (y : P2) = ((t : ℝ), 1)) ∧
        (∀ (z : T) (y : SM), (mL z : P2) = nM y ↔
          ∃ t : I01, (z : P2) = q1 t ∧ (y : EM) = pL t) ∧
        (∀ (x : SA) (y : SM),
          (mL ⟨nA x, Or.inl (nA x).property⟩ : P2) ≠ nM y) ∧
        (∀ (x : T) (y : source), (nAML x : P2) = nR y ↔
          ∃ t : I01, (x : P2) = q t ∧ (y : P2) = ((t : ℝ), -1)) ∧
        (∀ (z : T) (y : SC), (mR z : P2) = nC y ↔
          ∃ t : I01, (z : P2) = q2 t ∧ (y : EC) = pC t) ∧
        (∀ (x : T) (y : SC),
          (mR ⟨nAML x, Or.inl (nAML x).property⟩ : P2) ≠ nC y) := by
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
    intro h
    have h01 : (0 : ℝ) = 1 := congrArg Prod.fst h
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
  have hagreeA (t : I01) : fA (pA t) =
      (τ ∘ alternate (1 / 4) false) (pplus t) := by
    change fA (pA t) = τ (alternate (1 / 4) false (pplus t))
    rw [hpplusVal, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.2.2]
    exact hA t
  have hagreeL (t : I01) : (τ ∘ alternate (1 / 4) false) (pminus t) = fM (pL t) := by
    change τ (alternate (1 / 4) false (pminus t)) = fM (pL t)
    rw [hpminusVal, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.2.1]
    exact (hL t).symm
  obtain ⟨BA, BL, V1, D1, BM, nA, nL, q1, mL, nM, gAML,
      _, _, hWAB, hWABi, hplusBL, hplusBLi, hV1, hq1PL, hq1, _, hBM,
      hV1D1, hV1D1i, hLMB, hLMBi,
      hnA, hnL, hmL, hnM, hseamA, hseamL, hfiberAL, hfiberAM, hdisjAM,
      hgAML, hgA, hgL, hgM,
      himAML, hballAML, hpreAML⟩ :=
    exists_three_disk_chain_map e hcompat hSA hrect hSM hWA hplus hminus hLM
      hWAQ hplusQ hminusQ hLMQ hdisjoint.symm habA (hends 1) habL
      pA pplus pminus pL hpA hpplus hpminus hpL
      hpA0 hpA1 (hpplusVal 0) (hpplusVal 1) (hpminusVal 0) (hpminusVal 1)
      hpL0 hpL1 hfA (hstrip false) hfM hagreeA hagreeL
  let QAML := (fun x : T ↦ (mL x : P2)) '' (Subtype.val ⁻¹' D1) ∪
    (fun x : SM ↦ (nM x : P2)) '' (Subtype.val ⁻¹' BM)
  have hRMB : RM ⊆ BM := by
    intro x hx
    exact (hLMB.symm.subset (hRMQ hx)).resolve_left
      (fun hxl ↦ disjoint_left.mp hdisj hxl hx)
  obtain ⟨V, q, hV, hq, hqVal, hVeq⟩ :=
    transport_arm nM hnM hRM (hRMQ.trans hSM.1) pR hpR hpR0 hpR1
  have hVQ : V ⊆ QAML := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hVeq.subset hy
    exact Or.inr ⟨x, hRMB hx, rfl⟩
  have hqEnds : (q 0 : P2) ≠ (q 1 : P2) := by
    intro h
    have h01 := congrArg (fun t : I01 ↦ (t : ℝ)) (q.injective (Subtype.ext h))
    norm_num at h01
  have hagreeR (t : I01) : gAML (q t) =
      (τ ∘ alternate (1 / 4) true) (pminus t) := by
    rw [hqVal, hgM]
    change fM (pR t) = τ (alternate (1 / 4) true (pminus t))
    rw [hpminusVal, (arm_endpoints hb (t : ℝ)).2.2.2.2.1]
    exact hR t
  have hagreeC (t : I01) : (τ ∘ alternate (1 / 4) true) (pplus t) = fC (pC t) := by
    change τ (alternate (1 / 4) true (pplus t)) = fC (pC t)
    rw [hpplusVal, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.1]
    exact (hC t).symm
  obtain ⟨BAML, BR, V2, D, BC, nAML, nR, q2, mR, nC, g,
      _, _, hVBAML, hVBAMLi, hminusBR, hminusBRi, hV2, hq2PL, hq2, _, hBC,
      hV2D, hV2Di, hWCB, hWCBi,
      hnAML, hnR, hmR, hnC, hseamR, hseamC, hfiberR, hfiberC, hdisjC,
      hg, hgOld, hgR, hgC,
      him, hball, hpre⟩ :=
    exists_three_disk_chain_map e hcompat hballAML hrect hSC hV hminus hplus hWC
      hVQ hminusQ hplusQ hWCQ hdisjoint hqEnds (hends (-1)) habC
      q pminus pplus pC hq hpminus hpplus hpC
      rfl rfl (hpminusVal 0) (hpminusVal 1) (hpplusVal 0) (hpplusVal 1)
      hpC0 hpC1 hgAML (hstrip true) hfC hagreeR hagreeC
  let k := fun x : T ↦ (mR ⟨nAML x, Or.inl (nAML x).property⟩ : P2)
  let jA := fun x : SA ↦ k ⟨mL ⟨nA x, Or.inl (nA x).property⟩,
    Or.inl (mL ⟨nA x, Or.inl (nA x).property⟩).property⟩
  let jL := fun x : source ↦ k ⟨mL ⟨nL x, Or.inr (nL x).property⟩,
    Or.inl (mL ⟨nL x, Or.inr (nL x).property⟩).property⟩
  let jM := fun x : SM ↦ k ⟨nM x, Or.inr (nM x).property⟩
  let jR := fun x : source ↦ (mR ⟨nR x, Or.inr (nR x).property⟩ : P2)
  have hparamMinus (t : I01) :
      (⟨pminus t, hrect.1 (hminusQ (pminus t).property)⟩ : source) =
        ⟨((t : ℝ), -1), ⟨t.property, by norm_num⟩⟩ := Subtype.ext (hpminusVal t)
  have hparamPlus (t : I01) :
      (⟨pplus t, hrect.1 (hplusQ (pplus t).property)⟩ : source) =
        ⟨((t : ℝ), 1), ⟨t.property, by norm_num⟩⟩ := Subtype.ext (hpplusVal t)
  have hfinalA (x : SA) : g (jA x) = fA x :=
    (hgOld _).trans (hgA x)
  have hfinalL (x : source) : g (jL x) = τ (alternate (1 / 4) false x) :=
    (hgOld _).trans (hgL x)
  have hfinalM (x : SM) : g (jM x) = fM x := (hgOld _).trans (hgM x)
  refine ⟨D, BC, nA, nL, mL, nM, nAML, nR, mR, nC, g,
    hnA, hnL, hmL, hnM, hnAML, hnR, hmR, hnC, hBC, hWCB, hWCBi,
    ?_, ?_, ?_, ?_, hg, hfinalA, hfinalL, hfinalM, hgR, hgC, ?_, hball, ?_, ?_⟩
  · intro t
    have h := hseamA t
    rw [hparamPlus] at h
    exact congrArg (fun z : T ↦ k ⟨mL z, Or.inl (mL z).property⟩) (Subtype.ext h)
  · intro t
    have h := hseamL t
      ⟨nL ⟨((t : ℝ), -1), ⟨t.property, by norm_num⟩⟩,
        Or.inr (nL ⟨((t : ℝ), -1), ⟨t.property, by norm_num⟩⟩).property⟩
      ((hq1 t).trans (congrArg (fun z : source ↦ (nL z : P2)) (hparamMinus t))).symm
    exact congrArg k (Subtype.ext h)
  · intro t
    have h := hseamR t
    have hx : (⟨q t, hballAML.1 (hVQ (q t).property)⟩ : T) =
        ⟨nM ⟨pR t, hSM.1 (hRMQ (pR t).property)⟩,
          Or.inr (nM ⟨pR t, hSM.1 (hRMQ (pR t).property)⟩).property⟩ :=
      Subtype.ext (hqVal t)
    rw [hx, hparamMinus] at h
    exact congrArg (fun z : T ↦ (mR z : P2)) (Subtype.ext h)
  · intro t
    apply hseamC t
    exact ((hq2 t).trans (congrArg (fun z : source ↦ (nR z : P2)) (hparamPlus t))).symm
  · rw [himAML] at him
    simpa only [image_image, Function.comp_def] using him
  · intro Z
    ext y
    constructor
    · intro hy
      rcases (hpre Z).subset hy with (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩
      · rcases (hpreAML Z).subset ⟨x.property, hx⟩ with
          (⟨z, hz, hzx⟩ | ⟨z, hz, hzx⟩) | ⟨z, hz, hzx⟩
        · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨z, hz, congrArg k (Subtype.ext hzx)⟩)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨z, hz, congrArg k (Subtype.ext hzx)⟩)))
        · exact Or.inl (Or.inl (Or.inr ⟨z, hz, congrArg k (Subtype.ext hzx)⟩))
      · exact Or.inl (Or.inr ⟨x, hx, rfl⟩)
      · exact Or.inr ⟨x, hx, rfl⟩
    · rintro ((((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) |
          ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
      · refine ⟨Or.inl (mR _).property, ?_⟩
        change g (jA x) ∈ Z
        rwa [hfinalA]
      · refine ⟨Or.inl (mR _).property, ?_⟩
        change g (jL x) ∈ Z
        rwa [hfinalL]
      · refine ⟨Or.inl (mR _).property, ?_⟩
        change g (jM x) ∈ Z
        rwa [hfinalM]
      · refine ⟨Or.inl (mR _).property, ?_⟩
        change g (mR ⟨nR x, Or.inr (nR x).property⟩) ∈ Z
        rwa [hgR]
      · refine ⟨Or.inr (nC x).property, ?_⟩
        change g (nC x) ∈ Z
        rwa [hgC]
  · refine ⟨BA, BL, D1, BAML, BR, V1, V, V2, BM, q1, q, q2,
      hq1PL, hq, hq2PL, hWAB, hWABi, hplusBL, hplusBLi, hV1, ?_, hV1D1, hV1D1i,
      hLMB, hLMBi, hVeq, hqVal, hVBAML, hVBAMLi, hminusBR, hminusBRi,
      hV2, ?_, hV2D, hV2Di, ?_, hfiberAM, hdisjAM, ?_, hfiberC, hdisjC⟩
    · intro t
      exact (hq1 t).trans (congrArg (fun z : source ↦ (nL z : P2)) (hparamMinus t))
    · intro t
      exact (hq2 t).trans (congrArg (fun z : source ↦ (nR z : P2)) (hparamPlus t))
    · intro x y
      simpa only [hpplusVal] using hfiberAL x y
    · intro x y
      simpa only [hpminusVal] using hfiberR x y

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
