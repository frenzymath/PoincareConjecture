import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.MarkedOutgoingTraversal
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.NormalizedMarkedTraversal
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.MiddleRimIntervals
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.StripSourceEndPaths
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.AlternateResolutionSources

set_option autoImplicit false

open Set Metric Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1
local notation "i0" => (0 : unitInterval)
local notation "i1" => (1 : unitInterval)
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)

theorem exists_normalized_alternate_resolution_disk_map_with_sources
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
    (Z : Set X) (hτZ : ∀ z ∈ tube, τ z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1)
    (hQA : QA = (SA ∩ fA ⁻¹' Z) ∪ WA)
    (hQM : QM = ((SM ∩ fM ⁻¹' Z) ∪ RM) ∪ LM)
    (hQC : QC = (SC ∩ fC ⁻¹' Z) ∪ WC)
    (hmarkA : WA ∩ fA ⁻¹' Z = {aA, bA})
    (hmarkL : LM ∩ fM ⁻¹' Z = {aL, bL})
    (hmarkR : RM ∩ fM ⁻¹' Z = {aR, bR})
    (hmarkC : WC ∩ fC ⁻¹' Z = {aC, bC}) :
    ∃ (d0 : MarkedResolutionEndData Z τ (1 / 4) 0)
      (d1 : MarkedResolutionEndData Z τ (1 / 4) 1)
      (J K : Set EM) (qA : I01 ≃ₜ (SA ∩ fA ⁻¹' Z : Set EA))
      (qC : I01 ≃ₜ (SC ∩ fC ⁻¹' Z : Set EC)) (qD : I01 ≃ₜ J) (qB : I01 ≃ₜ K)
      (a : Path d0.a d1.a) (c : Path d1.c d0.c) (g : V2 → X) (R : Path d0.c d0.c),
      Nonempty (AlternateResolutionSources SA SM SC source
        (fun t ↦ pA t) (fun t ↦ pL t) (fun t ↦ pR t) (fun t ↦ pC t)
        (fun t ↦ ⟨((t : ℝ), -1), t.property, by norm_num⟩)
        (fun t ↦ ⟨((t : ℝ), 1), t.property, by norm_num⟩)
        fA (τ ∘ alternate (1 / 4) false) fM (τ ∘ alternate (1 / 4) true) fC g) ∧
      qA.IsFinitePL ∧ qC.IsFinitePL ∧ qD.IsFinitePL ∧ qB.IsFinitePL ∧
      (qA i0 : EA) = aA ∧ (qA i1 : EA) = bA ∧
      (qC i0 : EC) = aC ∧ (qC i1 : EC) = bC ∧
      (qD i0 : EM) = aL ∧ (qB i1 : EM) = bL ∧
      Disjoint J K ∧ J ∪ K = SM ∩ fM ⁻¹' Z ∧
      (∀ t : I01, (a t : X) = fA (qA t)) ∧
      (∀ t : I01, (c.symm t : X) = fC (qC t)) ∧
      PolyhedralPLInCharts e g D ∧
      g '' D = (((fA '' SA ∪ τ '' (alternate (1 / 4) false '' source)) ∪
        fM '' SM) ∪ τ '' (alternate (1 / 4) true '' source)) ∪ fC '' SC ∧
      (∀ x ∈ D, g x ∈ Z ↔ x ∈ Q) ∧
      (∀ t : I01, (R t : X) = g (squareRimLoop t)) ∧
      ((∃ (d : Path d0.l d0.r) (β : Path d1.r d1.l),
        (qD i1 : EM) = aR ∧ (qB i0 : EM) = bR ∧
        (∀ t : I01, (d t : X) = fM (qD t)) ∧
        (∀ t : I01, (β t : X) = fM (qB t)) ∧
        R.Homotopic (((((((d0.R.symm.trans d.symm).trans d0.L).trans a).trans
          d1.L.symm).trans β.symm).trans d1.R).trans c)) ∨
      (∃ (d : Path d0.l d1.r) (β : Path d0.r d1.l),
        (qD i1 : EM) = bR ∧ (qB i0 : EM) = aR ∧
        (∀ t : I01, (d t : X) = fM (qD t)) ∧
        (∀ t : I01, (β t : X) = fM (qB t)) ∧
        R.Homotopic (((((((d0.R.symm.trans β).trans d1.L).trans a.symm).trans
          d0.L.symm).trans d).trans d1.R).trans c))) := by
  have hb : (1 / 4 : ℝ) < 1 := by norm_num
  have hτmark := fun z hz ht ↦ (hτZ z hz).mpr ht
  obtain ⟨d0⟩ := nonempty_marked_resolution_end_data τ hτ.continuousOn hτmark hb 0 (by simp)
  obtain ⟨d1⟩ := nonempty_marked_resolution_end_data τ hτ.continuousOn hτmark hb 1 (by simp)
  have hAI := outer_disk_old_rim_is_interval (hQA ▸ hSA) hWA habA hmarkA
  have hCI := outer_disk_old_rim_is_interval (hQC ▸ hSC) hWC habC hmarkC
  obtain ⟨qA, hqA, hqA0, hqA1⟩ := hAI.exists_unitInterval_chart_with_endpoints habA
  obtain ⟨qC, hqC, hqC0, hqC1⟩ := hCI.exists_unitInterval_chart_with_endpoints habC
  have hAa : fA aA = (d0.a : X) := by
    rw [d0.a_val]
    simpa only [hpA0] using hA i0
  have hAb : fA bA = (d1.a : X) := by
    rw [d1.a_val]
    simpa only [hpA1] using hA i1
  have hCa : fC aC = (d0.c : X) := by
    rw [d0.c_val]
    simpa only [hpC0] using hC i0
  have hCb : fC bC = (d1.c : X) := by
    rw [d1.c_val]
    simpa only [hpC1] using hC i1
  have hLa : fM aL = (d0.l : X) := by
    rw [d0.l_val]
    simpa only [hpL0] using hL i0
  have hLb : fM bL = (d1.l : X) := by
    rw [d1.l_val]
    simpa only [hpL1] using hL i1
  have hRa : fM aR = (d0.r : X) := by
    rw [d0.r_val]
    simpa only [hpR0] using hR i0
  have hRb : fM bR = (d1.r : X) := by
    rw [d1.r_val]
    simpa only [hpR1] using hR i1
  let a : Path d0.a d1.a :=
    { toFun t := ⟨fA (qA t), (qA t).property.2⟩
      continuous_toFun := (hfA.continuousOn.comp_continuous
        (continuous_subtype_val.comp qA.continuous) (fun t ↦ (qA t).property.1)).subtype_mk _
      source' := Subtype.ext ((congrArg fA hqA0).trans hAa)
      target' := Subtype.ext ((congrArg fA hqA1).trans hAb) }
  let cForward : Path d0.c d1.c :=
    { toFun t := ⟨fC (qC t), (qC t).property.2⟩
      continuous_toFun := (hfC.continuousOn.comp_continuous
        (continuous_subtype_val.comp qC.continuous) (fun t ↦ (qC t).property.1)).subtype_mk _
      source' := Subtype.ext ((congrArg fC hqC0).trans hCa)
      target' := Subtype.ext ((congrArg fC hqC1).trans hCb) }
  have hrect : IsFinitePLBallPair P2 source stripRim :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  obtain ⟨hminus, pminus, hpminus, hpminusVal⟩ := exists_arm_parameter (-1)
  obtain ⟨hplus, pplus, hpplus, hpplusVal⟩ := exists_arm_parameter 1
  have hminusQ : arm (-1) ⊆ stripRim := fun _ hx ↦ Or.inr ⟨hx.1, Or.inl hx.2⟩
  have hplusQ : arm 1 ⊆ stripRim := fun _ hx ↦ Or.inr ⟨hx.1, Or.inr hx.2⟩
  have hdisjStrip : arm (-1) ∩ arm 1 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hn : x.2 = -1 := hx.1.2
    have hp : x.2 = 1 := hx.2.2
    linarith
  have hends (u : ℝ) : ((0, u) : P2) ≠ (1, u) := by
    intro heq
    have h01 : (0 : ℝ) = 1 := congrArg Prod.fst heq
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
    have hpre := resolution_strip_frontier_preimage τ hτZ hb.le true positive
    simp only [resolutionMap, ↓reduceIte] at hpre
    rw [hpre]
    exact stripRim_eq_ends_union_arms
  have hmark (positive : Bool) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      arm u ∩ (τ ∘ alternate (1 / 4) positive) ⁻¹' Z = {(0, u), (1, u)} :=
    resolution_strip_arm_frontier_inter τ hτZ hb.le hu true positive
  have hmarkEnd (positive : Bool) (t : I01) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1)
      (s : I01) : (τ ∘ alternate (1 / 4) positive) (stripSourceEndPath t s) ∈ Z :=
    stripSourceEndPath_maps_to_mark τ hτmark hb.le true positive t ht s
  have hagreeA (t : I01) : fA (pA t) =
      (τ ∘ alternate (1 / 4) false) (pplus t) := by
    change fA (pA t) = τ (alternate (1 / 4) false (pplus t))
    rw [hpplusVal, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.2.2]
    exact hA t
  let αL := ((stripSourceEndPath 0).map continuous_subtype_val).cast rfl (hpplusVal 0)
  let βA := (intervalChartPath qA).cast (hpA0.trans hqA0.symm) (hpA1.trans hqA1.symm)
  let γL := ((stripSourceEndPath 1).symm.map continuous_subtype_val).cast (hpplusVal 1) rfl
  obtain ⟨gAL, V1, q1, PAL, hgAL, himAL, hballAL, hV1, hq1, hq1ends, hcontact1,
    hq1map, hPALS, hPALZ, hPALval, hsAL⟩ :=
    exists_marked_outgoing_traversal_with_sources e hcompat hSA hrect hWA hplus hWAQ hplusQ
      habA (hends 1) pA pplus hpA hpplus hpA0 hpA1 (hpplusVal 0) (hpplusVal 1)
      hfA (hstrip false) hagreeA Z hQA hmarkA (hmark false 1 (by norm_num))
      hminus hminusQ (by rw [inter_comm]; exact hdisjStrip)
      pminus hpminus (hpminusVal 0) (hpminusVal 1) (hrim false)
      (hmark false (-1) (by norm_num)) 0 1 αL βA γL
      (fun t ↦ (stripSourceEndPath 0 t).property) (fun t ↦ (qA t).property.1)
      (fun t ↦ ((stripSourceEndPath 1).symm t).property)
      (hmarkEnd false 0 (by simp)) (fun t ↦ (qA t).property.2)
      (fun t ↦ hmarkEnd false 1 (by simp) _)
      d0.L a d1.L.symm (fun t ↦ d0.L_val t) (fun _ ↦ rfl) (fun t ↦ d1.L_val _)
  let UAL := (d0.L.trans a).trans d1.L.symm
  have hagreeM (t : I01) : gAL (q1 t) = fM (pL t) := by
    rw [hq1map]
    change τ (alternate (1 / 4) false (pminus t)) = fM (pL t)
    rw [hpminusVal, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.2.1]
    exact (hL t).symm
  have hfinish (s t : I01) (P : Path (q1 s : P2) (q1 t : P2))
      (hPS : ∀ r : I01, P r ∈ T) (hPZ : ∀ r : I01, gAL (P r) ∈ Z)
      {z1 z2 : Z} (B : Path z1 z2) (hB : ∀ r : I01, (B r : X) = gAL (P r))
      (αM : Path aR (pL s : EM)) (γM : Path (pL t : EM) bR)
      (hαS : ∀ r : I01, αM r ∈ SM) (hγS : ∀ r : I01, γM r ∈ SM)
      (hαZ : ∀ r : I01, fM (αM r) ∈ Z) (hγZ : ∀ r : I01, fM (γM r) ∈ Z)
      (A : Path d0.r z1) (C : Path z2 d1.r)
      (hAval : ∀ r : I01, (A r : X) = fM (αM r))
      (hCval : ∀ r : I01, (C r : X) = fM (γM r)) :
      ∃ (g : V2 → X) (R : Path d0.c d0.c),
        Nonempty (AlternateResolutionSources SA SM SC source
          (fun t ↦ pA t) (fun t ↦ pL t) (fun t ↦ pR t) (fun t ↦ pC t)
          (fun t ↦ ⟨((t : ℝ), -1), t.property, by norm_num⟩)
          (fun t ↦ ⟨((t : ℝ), 1), t.property, by norm_num⟩)
          fA (τ ∘ alternate (1 / 4) false) fM (τ ∘ alternate (1 / 4) true) fC g) ∧
        PolyhedralPLInCharts e g D ∧
        g '' D = (((fA '' SA ∪ τ '' (alternate (1 / 4) false '' source)) ∪
          fM '' SM) ∪ τ '' (alternate (1 / 4) true '' source)) ∪ fC '' SC ∧
        (∀ x ∈ D, g x ∈ Z ↔ x ∈ Q) ∧
        (∀ r : I01, (R r : X) = g (squareRimLoop r)) ∧
        R.Homotopic (((d0.R.symm.trans ((A.trans B).trans C)).trans d1.R).trans
          cForward.symm) := by
    obtain ⟨gAML, VM, qM, PM, hgAML, himAML, hballAML, hVM, hqM, hqMends,
      hcontactM, hqMmap, hPMS, hPMZ, hPMval, hsM⟩ :=
      exists_marked_outgoing_traversal_with_sources e hcompat hballAL hSM hV1 hLM
        subset_union_right hLMQ hq1ends habL q1 pL hq1 hpL rfl rfl hpL0 hpL1
        hgAL hfM hagreeM Z rfl hcontact1 hmarkL hRM hRMQ
        (Set.disjoint_iff_inter_eq_empty.mp hdisj) pR hpR hpR0 hpR1 hQM hmarkR
        s t αM P γM hαS hPS hγS hαZ hPZ hγZ A B C hAval hB hCval
    have hagreeR (r : I01) : gAML (qM r) =
        (τ ∘ alternate (1 / 4) true) (pminus r) := by
      rw [hqMmap]
      change fM (pR r) = τ (alternate (1 / 4) true (pminus r))
      rw [hpminusVal, (arm_endpoints hb (r : ℝ)).2.2.2.2.1]
      exact hR r
    have hrimR : stripRim =
        ((source ∩ (τ ∘ alternate (1 / 4) true) ⁻¹' Z) ∪ arm 1) ∪ arm (-1) := by
      rw [hrim true]
      ac_rfl
    let αR := ((stripSourceEndPath 0).symm.map continuous_subtype_val).cast
      rfl (hpminusVal 0)
    let γR := ((stripSourceEndPath 1).map continuous_subtype_val).cast (hpminusVal 1) rfl
    obtain ⟨gAMLR, VC, qLast, PLast, hgAMLR, himAMLR, hballAMLR, hVC, hqLast,
      hqLastends, hcontactLast, hqLastmap, hPLastS, hPLastZ, hPLastval, hsR⟩ :=
      exists_marked_outgoing_traversal_with_sources e hcompat hballAML hrect hVM hminus
        subset_union_right hminusQ hqMends (hends (-1)) qM pminus hqM hpminus rfl rfl
        (hpminusVal 0) (hpminusVal 1) hgAML (hstrip true) hagreeR Z rfl hcontactM
        (hmark true (-1) (by norm_num)) hplus hplusQ hdisjStrip pplus hpplus
        (hpplusVal 0) (hpplusVal 1) hrimR (hmark true 1 (by norm_num))
        0 1 αR PM γR (fun r ↦ ((stripSourceEndPath 0).symm r).property) hPMS
        (fun r ↦ (stripSourceEndPath 1 r).property)
        (fun r ↦ hmarkEnd true 0 (by simp) _) hPMZ (hmarkEnd true 1 (by simp))
        d0.R.symm ((A.trans B).trans C) d1.R
        (fun r ↦ d0.R_val _) hPMval (fun r ↦ d1.R_val r)
    have hagreeC (r : I01) : gAMLR (qLast r) = fC (pC r) := by
      rw [hqLastmap]
      change τ (alternate (1 / 4) true (pplus r)) = fC (pC r)
      rw [hpplusVal, (arm_endpoints hb (r : ℝ)).2.2.2.2.2.1]
      exact (hC r).symm
    obtain ⟨g, R, hg, him, hproper, hRval, hRhom, hsC⟩ :=
      exists_normalized_marked_traversal_with_sources e hcompat hballAMLR hSC hVC hWC
        subset_union_right hWCQ hqLastends habC qLast pC hqLast hpC rfl rfl hpC0 hpC1
        hgAMLR hfC hagreeC Z rfl hQC hcontactLast hmarkC PLast
        ((intervalChartPath qC).cast hqC0.symm hqC1.symm)
        hPLastS (fun r ↦ (qC r).property.1) hPLastZ (fun r ↦ (qC r).property.2)
        d0.c d1.c ((d0.R.symm.trans ((A.trans B).trans C)).trans d1.R) cForward
        hPLastval (fun _ ↦ rfl)
    refine ⟨g, R, ?_, hg, ?_, hproper, hRval, hRhom⟩
    · obtain ⟨nA, nL, pAL, hnA, hnL, _, _, _, _, _, _, hkeepA, hkeepL,
        hfiberAL, _, _, hq1val⟩ := hsAL
      obtain ⟨mL, nM, pM, hmL, hnM, _, _, _, _, _, _, hkeepAL, hkeepM,
        hfiberM, _, _, hqMval⟩ := hsM
      obtain ⟨nAML, nR, pR', hnAML, hnR, _, _, _, _, _, _, hkeepAML, hkeepR,
        hfiberR, _, _, hqLastval⟩ := hsR
      obtain ⟨mR, nC, H, pC', hsC⟩ := hsC
      dsimp only at hsC
      obtain ⟨hmR, hnC, hH, _, _, _, _, _, _, hkeepAMLR, hkeepC, hfiberC, _⟩ := hsC
      refine ⟨⟨nA, nL, mL, nM, nAML, nR, mR, nC, H,
        hnA, hnL, hmL, hnM, hnAML, hnR, hmR, hnC, hH,
        fun t ↦ hSM.1 (hRMQ (pR t).property),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hkeepC⟩⟩
      · intro x y
        simpa only [hpplusVal, Subtype.ext_iff] using hfiberAL x y
      · intro x y
        simpa only [hq1val, hpminusVal] using hfiberM x y
      · intro x y
        simpa only [hqMval, hpminusVal, Subtype.ext_iff] using hfiberR x y
      · intro x y
        have heq : (H.symm (rightDiskCopy mR x) : V2) =
            H.symm (leftDiskCopy nC y) ↔ (mR x : P2) = nC y := by
          constructor
          · intro h
            exact congrArg Subtype.val (H.symm.injective (Subtype.ext h))
          · intro h
            exact congrArg (fun z : T ↦ (H.symm z : V2)) (Subtype.ext h)
        rw [← heq]
        simpa only [rightDiskCopy, leftDiskCopy, hqLastval, hpplusVal] using hfiberC x y
      · intro x
        dsimp only [rightDiskCopy, leftDiskCopy]
        rw [hkeepAMLR, hkeepAML, hkeepAL, hkeepA]
      · intro x
        dsimp only [rightDiskCopy, leftDiskCopy]
        rw [hkeepAMLR, hkeepAML, hkeepAL, hkeepL]
      · intro x
        dsimp only [rightDiskCopy, leftDiskCopy]
        rw [hkeepAMLR, hkeepAML, hkeepM]
      · intro x
        dsimp only [rightDiskCopy, leftDiskCopy]
        rw [hkeepAMLR, hkeepR]
    · rw [him, himAMLR, himAML, himAL]
      simp only [image_image, Function.comp_def]
  have habR : aR ≠ bR := by
    intro heq
    have h01 := congrArg (fun t : I01 ↦ (t : ℝ))
      (pR.injective (Subtype.ext (hpR0.trans (heq.trans hpR1.symm))))
    norm_num at h01
  have hSM' : IsFinitePLBallPair P2 SM (((SM ∩ fM ⁻¹' Z) ∪ LM) ∪ RM) := by
    have h := hQM ▸ hSM
    convert h using 1
    ac_rfl
  obtain ⟨J, K, u, v, huvpair, huv, hJ, hK, hJKdisj, hJK, _, _, _, _⟩ :=
    exists_middle_disk_old_rim_intervals hSM' hLM hRM habL habR hdisj hmarkL hmarkR
  have huR : u ∈ RM := hRM.1 (huvpair.subset (Or.inl rfl))
  have hvR : v ∈ RM := hRM.1 (huvpair.subset (Or.inr rfl))
  have haLu : aL ≠ u := fun heq ↦
    Set.disjoint_left.mp hdisj (hLM.1 (Or.inl rfl)) (heq.symm ▸ huR)
  have hvbL : v ≠ bL := fun heq ↦
    Set.disjoint_left.mp hdisj (hLM.1 (Or.inr rfl)) (heq ▸ hvR)
  obtain ⟨qD, hqD, hqD0, hqD1⟩ := hJ.exists_unitInterval_chart_with_endpoints haLu
  obtain ⟨qB, hqB, hqB0, hqB1⟩ := hK.exists_unitInterval_chart_with_endpoints hvbL
  have hJmark : J ⊆ SM ∩ fM ⁻¹' Z := subset_union_left.trans hJK.subset
  have hKmark : K ⊆ SM ∩ fM ⁻¹' Z := subset_union_right.trans hJK.subset
  rcases Set.pair_eq_pair_iff.mp huvpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · let d : Path d0.l d0.r :=
      { toFun t := ⟨fM (qD t), (hJmark (qD t).property).2⟩
        continuous_toFun := (hfM.continuousOn.comp_continuous
          (continuous_subtype_val.comp qD.continuous)
          (fun t ↦ (hJmark (qD t).property).1)).subtype_mk _
        source' := Subtype.ext ((congrArg fM hqD0).trans hLa)
        target' := Subtype.ext ((congrArg fM hqD1).trans hRa) }
    let β : Path d1.r d1.l :=
      { toFun t := ⟨fM (qB t), (hKmark (qB t).property).2⟩
        continuous_toFun := (hfM.continuousOn.comp_continuous
          (continuous_subtype_val.comp qB.continuous)
          (fun t ↦ (hKmark (qB t).property).1)).subtype_mk _
        source' := Subtype.ext ((congrArg fM hqB0).trans hRb)
        target' := Subtype.ext ((congrArg fM hqB1).trans hLb) }
    let αM := (intervalChartPath qD).symm.cast hqD1.symm (hpL0.trans hqD0.symm)
    let γM := (intervalChartPath qB).symm.cast (hpL1.trans hqB1.symm) hqB0.symm
    obtain ⟨g, R, hsources, hg, him, hproper, hRval, hRhom⟩ :=
      hfinish 0 1 PAL hPALS hPALZ UAL hPALval αM γM
        (fun t ↦ (hJmark (qD _).property).1) (fun t ↦ (hKmark (qB _).property).1)
        (fun t ↦ (hJmark (qD _).property).2) (fun t ↦ (hKmark (qB _).property).2)
        d.symm β.symm (fun _ ↦ rfl) (fun _ ↦ rfl)
    refine ⟨d0, d1, J, K, qA, qC, qD, qB, a, cForward.symm, g, R,
      hsources, hqA, hqC, hqD, hqB, hqA0, hqA1, hqC0, hqC1, hqD0, hqB1,
      hJKdisj, hJK, fun _ ↦ rfl, ?_, hg, him, hproper, hRval,
      Or.inl ⟨d, β, hqD1, hqB0, fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩⟩
    · intro t
      simp only [Path.symm_symm]
      rfl
    · apply hRhom.trans
      apply Path.Homotopic.Quotient.eq.mp
      simp only [UAL, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]
  · let d : Path d0.l d1.r :=
      { toFun t := ⟨fM (qD t), (hJmark (qD t).property).2⟩
        continuous_toFun := (hfM.continuousOn.comp_continuous
          (continuous_subtype_val.comp qD.continuous)
          (fun t ↦ (hJmark (qD t).property).1)).subtype_mk _
        source' := Subtype.ext ((congrArg fM hqD0).trans hLa)
        target' := Subtype.ext ((congrArg fM hqD1).trans hRb) }
    let β : Path d0.r d1.l :=
      { toFun t := ⟨fM (qB t), (hKmark (qB t).property).2⟩
        continuous_toFun := (hfM.continuousOn.comp_continuous
          (continuous_subtype_val.comp qB.continuous)
          (fun t ↦ (hKmark (qB t).property).1)).subtype_mk _
        source' := Subtype.ext ((congrArg fM hqB0).trans hRa)
        target' := Subtype.ext ((congrArg fM hqB1).trans hLb) }
    let αM := (intervalChartPath qB).cast hqB0.symm (hpL1.trans hqB1.symm)
    let γM := (intervalChartPath qD).cast (hpL0.trans hqD0.symm) hqD1.symm
    obtain ⟨g, R, hsources, hg, him, hproper, hRval, hRhom⟩ :=
      hfinish 1 0 PAL.symm (fun t ↦ hPALS _) (fun t ↦ hPALZ _) UAL.symm
        (fun t ↦ hPALval _) αM γM
        (fun t ↦ (hKmark (qB t).property).1) (fun t ↦ (hJmark (qD t).property).1)
        (fun t ↦ (hKmark (qB t).property).2) (fun t ↦ (hJmark (qD t).property).2)
        β d (fun _ ↦ rfl) (fun _ ↦ rfl)
    refine ⟨d0, d1, J, K, qA, qC, qD, qB, a, cForward.symm, g, R,
      hsources, hqA, hqC, hqD, hqB, hqA0, hqA1, hqC0, hqC1, hqD0, hqB1,
      hJKdisj, hJK, fun _ ↦ rfl, ?_, hg, him, hproper, hRval,
      Or.inr ⟨d, β, hqD1, hqB0, fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩⟩
    · intro t
      simp only [Path.symm_symm]
      rfl
    · apply hRhom.trans
      apply Path.Homotopic.Quotient.eq.mp
      simp only [UAL, Path.trans_symm, Path.symm_symm,
        Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]

theorem exists_normalized_alternate_resolution_disk_map
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
    (Z : Set X) (hτZ : ∀ z ∈ tube, τ z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1)
    (hQA : QA = (SA ∩ fA ⁻¹' Z) ∪ WA)
    (hQM : QM = ((SM ∩ fM ⁻¹' Z) ∪ RM) ∪ LM)
    (hQC : QC = (SC ∩ fC ⁻¹' Z) ∪ WC)
    (hmarkA : WA ∩ fA ⁻¹' Z = {aA, bA})
    (hmarkL : LM ∩ fM ⁻¹' Z = {aL, bL})
    (hmarkR : RM ∩ fM ⁻¹' Z = {aR, bR})
    (hmarkC : WC ∩ fC ⁻¹' Z = {aC, bC}) :
    ∃ (d0 : MarkedResolutionEndData Z τ (1 / 4) 0)
      (d1 : MarkedResolutionEndData Z τ (1 / 4) 1)
      (J K : Set EM) (qA : I01 ≃ₜ (SA ∩ fA ⁻¹' Z : Set EA))
      (qC : I01 ≃ₜ (SC ∩ fC ⁻¹' Z : Set EC)) (qD : I01 ≃ₜ J) (qB : I01 ≃ₜ K)
      (a : Path d0.a d1.a) (c : Path d1.c d0.c) (g : V2 → X) (R : Path d0.c d0.c),
      qA.IsFinitePL ∧ qC.IsFinitePL ∧ qD.IsFinitePL ∧ qB.IsFinitePL ∧
      (qA i0 : EA) = aA ∧ (qA i1 : EA) = bA ∧
      (qC i0 : EC) = aC ∧ (qC i1 : EC) = bC ∧
      (qD i0 : EM) = aL ∧ (qB i1 : EM) = bL ∧
      Disjoint J K ∧ J ∪ K = SM ∩ fM ⁻¹' Z ∧
      (∀ t : I01, (a t : X) = fA (qA t)) ∧
      (∀ t : I01, (c.symm t : X) = fC (qC t)) ∧
      PolyhedralPLInCharts e g D ∧
      g '' D = (((fA '' SA ∪ τ '' (alternate (1 / 4) false '' source)) ∪
        fM '' SM) ∪ τ '' (alternate (1 / 4) true '' source)) ∪ fC '' SC ∧
      (∀ x ∈ D, g x ∈ Z ↔ x ∈ Q) ∧
      (∀ t : I01, (R t : X) = g (squareRimLoop t)) ∧
      ((∃ (d : Path d0.l d0.r) (β : Path d1.r d1.l),
        (qD i1 : EM) = aR ∧ (qB i0 : EM) = bR ∧
        (∀ t : I01, (d t : X) = fM (qD t)) ∧
        (∀ t : I01, (β t : X) = fM (qB t)) ∧
        R.Homotopic (((((((d0.R.symm.trans d.symm).trans d0.L).trans a).trans
          d1.L.symm).trans β.symm).trans d1.R).trans c)) ∨
      (∃ (d : Path d0.l d1.r) (β : Path d0.r d1.l),
        (qD i1 : EM) = bR ∧ (qB i0 : EM) = aR ∧
        (∀ t : I01, (d t : X) = fM (qD t)) ∧
        (∀ t : I01, (β t : X) = fM (qB t)) ∧
        R.Homotopic (((((((d0.R.symm.trans β).trans d1.L).trans a.symm).trans
          d0.L.symm).trans d).trans d1.R).trans c))) := by
  obtain ⟨d0, d1, J, K, qA, qC, qD, qB, a, c, g, R, _, h⟩ :=
    exists_normalized_alternate_resolution_disk_map_with_sources e hcompat hSA hSM hSC
      hWA hLM hRM hWC hWAQ hLMQ hRMQ hWCQ hdisj habA habL habC
      pA pL pR pC hpA hpL hpR hpC hpA0 hpA1 hpL0 hpL1 hpR0 hpR1 hpC0 hpC1
      hfA hfM hfC hτ hA hL hR hC Z hτZ hQA hQM hQC hmarkA hmarkL hmarkR hmarkC
  exact ⟨d0, d1, J, K, qA, qC, qD, qB, a, c, g, R, h⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
