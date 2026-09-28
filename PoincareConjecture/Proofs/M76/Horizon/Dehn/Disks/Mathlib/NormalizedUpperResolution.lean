import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.NormalizedMarkedTraversal
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.MarkedAttachmentTraversal
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.StripSourceEndPaths
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.UpperResolutionSources










set_option autoImplicit false

open Set Metric Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)



theorem exists_normalized_upper_resolution_disk_map_with_sources
    {EA EC F X ι : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [FiniteDimensional ℝ EA]
    [NormedAddCommGroup EC] [NormedSpace ℝ EC] [FiniteDimensional ℝ EC]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {SA QA WA : Set EA} {SC QC WC : Set EC} {aA bA : EA} {aC bC : EC}
    (hSA : IsFinitePLBallPair P2 SA QA) (hSC : IsFinitePLBallPair P2 SC QC)
    (hWA : IsFinitePLBallPair ℝ WA {aA, bA})
    (hWC : IsFinitePLBallPair ℝ WC {aC, bC})
    (hWAQ : WA ⊆ QA) (hWCQ : WC ⊆ QC) (habA : aA ≠ bA) (habC : aC ≠ bC)
    (pA : I01 ≃ₜ WA) (pC : I01 ≃ₜ WC) (hpA : pA.IsFinitePL) (hpC : pC.IsFinitePL)
    (hpA0 : (pA (0 : unitInterval) : EA) = aA)
    (hpA1 : (pA (1 : unitInterval) : EA) = bA)
    (hpC0 : (pC (0 : unitInterval) : EC) = aC)
    (hpC1 : (pC (1 : unitInterval) : EC) = bC)
    {fA : EA → X} {fC : EC → X} {τ : C3 → X}
    (hfA : PolyhedralPLInCharts e fA SA) (hfC : PolyhedralPLInCharts e fC SC)
    (hτ : PolyhedralPLInCharts e τ tube)
    (hleft : ∀ t : I01, fA (pA t) = τ ((-1, 1), t))
    (hright : ∀ t : I01, fC (pC t) = τ ((1, 1), t))
    (Z : Set X) (hτZ : ∀ z ∈ tube, τ z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1)
    (hQA : QA = (SA ∩ fA ⁻¹' Z) ∪ WA) (hQC : QC = (SC ∩ fC ⁻¹' Z) ∪ WC)
    (hmarkA : WA ∩ fA ⁻¹' Z = {aA, bA}) (hmarkC : WC ∩ fC ⁻¹' Z = {aC, bC}) :
    ∃ (d0 : MarkedResolutionEndData Z τ (1 / 4) 0)
      (d1 : MarkedResolutionEndData Z τ (1 / 4) 1)
      (qA : I01 ≃ₜ (SA ∩ fA ⁻¹' Z : Set EA))
      (qC : I01 ≃ₜ (SC ∩ fC ⁻¹' Z : Set EC))
      (a : Path d0.a d1.a) (c : Path d1.c d0.c) (g : V2 → X) (R : Path d0.c d0.c),
      Nonempty (UpperResolutionSources SA SC source (fun t ↦ pA t) (fun t ↦ pC t)
        (fun t ↦ ⟨((t : ℝ), -1), t.property, by norm_num⟩)
        (fun t ↦ ⟨((t : ℝ), 1), t.property, by norm_num⟩)
        fA (τ ∘ strip (1 / 4) true) fC g) ∧
      qA.IsFinitePL ∧ qC.IsFinitePL ∧
      (qA (0 : unitInterval) : EA) = aA ∧ (qA (1 : unitInterval) : EA) = bA ∧
      (qC (0 : unitInterval) : EC) = aC ∧ (qC (1 : unitInterval) : EC) = bC ∧
      (∀ t : I01, (a t : X) = fA (qA t)) ∧
      (∀ t : I01, (c.symm t : X) = fC (qC t)) ∧
      PolyhedralPLInCharts e g D ∧
      g '' D = (fA '' SA ∪ τ '' (strip (1 / 4) true '' source)) ∪ fC '' SC ∧
      (∀ x ∈ D, g x ∈ Z ↔ x ∈ Q) ∧
      (∀ t : I01, (R t : X) = g (squareRimLoop t)) ∧
      R.Homotopic (((d0.U.symm.trans a).trans d1.U).trans c) := by
  have hb : (1 / 4 : ℝ) < 1 := by norm_num
  have hτmark := fun z hz ht ↦ (hτZ z hz).mpr ht
  obtain ⟨d0⟩ := nonempty_marked_resolution_end_data τ hτ.continuousOn hτmark hb 0 (by simp)
  obtain ⟨d1⟩ := nonempty_marked_resolution_end_data τ hτ.continuousOn hτmark hb 1 (by simp)
  have hSA' : IsFinitePLBallPair P2 SA ((SA ∩ fA ⁻¹' Z) ∪ WA) := hQA ▸ hSA
  have hSC' : IsFinitePLBallPair P2 SC ((SC ∩ fC ⁻¹' Z) ∪ WC) := hQC ▸ hSC
  have hAI := outer_disk_old_rim_is_interval hSA' hWA habA hmarkA
  have hCI := outer_disk_old_rim_is_interval hSC' hWC habC hmarkC
  obtain ⟨qA, hqA, hqA0, hqA1⟩ := hAI.exists_unitInterval_chart_with_endpoints habA
  obtain ⟨qC, hqC, hqC0, hqC1⟩ := hCI.exists_unitInterval_chart_with_endpoints habC
  have hAa : fA aA = (d0.a : X) := by
    rw [d0.a_val]
    simpa only [hpA0] using hleft 0
  have hAb : fA bA = (d1.a : X) := by
    rw [d1.a_val]
    simpa only [hpA1] using hleft 1
  have hCa : fC aC = (d0.c : X) := by
    rw [d0.c_val]
    simpa only [hpC0] using hright 0
  have hCb : fC bC = (d1.c : X) := by
    rw [d1.c_val]
    simpa only [hpC1] using hright 1
  let a : Path d0.a d1.a :=
    { toFun := fun t ↦ ⟨fA (qA t), (qA t).property.2⟩
      continuous_toFun := (hfA.continuousOn.comp_continuous
        (continuous_subtype_val.comp qA.continuous) (fun t ↦ (qA t).property.1)).subtype_mk _
      source' := Subtype.ext ((congrArg fA hqA0).trans hAa)
      target' := Subtype.ext ((congrArg fA hqA1).trans hAb) }
  let cForward : Path d0.c d1.c :=
    { toFun := fun t ↦ ⟨fC (qC t), (qC t).property.2⟩
      continuous_toFun := (hfC.continuousOn.comp_continuous
        (continuous_subtype_val.comp qC.continuous) (fun t ↦ (qC t).property.1)).subtype_mk _
      source' := Subtype.ext ((congrArg fC hqC0).trans hCa)
      target' := Subtype.ext ((congrArg fC hqC1).trans hCb) }
  have hrect : IsFinitePLBallPair P2 source stripRim :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  obtain ⟨hL, pL, hpL, hpLval⟩ := exists_arm_parameter (-1)
  obtain ⟨hR, pR, hpR, hpRval⟩ := exists_arm_parameter 1
  have hLQ : arm (-1) ⊆ stripRim := fun _ hx => Or.inr ⟨hx.1, Or.inl hx.2⟩
  have hRQ : arm 1 ⊆ stripRim := fun _ hx => Or.inr ⟨hx.1, Or.inr hx.2⟩
  have hdisj : arm (-1) ∩ arm 1 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hn : x.2 = -1 := hx.1.2
    have hp : x.2 = 1 := hx.2.2
    linarith
  have hends : ((0, -1) : P2) ≠ (1, -1) := by
    intro h
    have h01 : (0 : ℝ) = 1 := congrArg Prod.fst h
    norm_num at h01
  have hs := (finitePiecewiseAffineOn_maps (1 / 4) true).1
  have hsCopy := hs
  obtain ⟨K, hK, hKs, _⟩ := hsCopy
  have hfS : PolyhedralPLInCharts e (τ ∘ strip (1 / 4) true) source := by
    have hreg : FinitePiecewiseAffineOn (strip (1 / 4) true) K.space := by
      simpa only [hKs] using hs
    have hmap : MapsTo (strip (1 / 4) true) K.space tube := by
      simpa only [hKs] using (mapsTo_tube hb.le true).1
    simpa only [hKs] using hτ.comp_finitePiecewiseAffineOn K hK hreg hmap
  have hagreeL (t : I01) : fA (pA t) = (τ ∘ strip (1 / 4) true) (pL t) := by
    change fA (pA t) = τ (strip (1 / 4) true (pL t))
    rw [hpLval, (arm_endpoints hb (t : ℝ)).1]
    exact hleft t
  have hQS : stripRim =
      ((source ∩ (τ ∘ strip (1 / 4) true) ⁻¹' Z) ∪ arm 1) ∪ arm (-1) := by
    have hpre : source ∩ (τ ∘ strip (1 / 4) true) ⁻¹' Z = stripEnds :=
      resolution_strip_frontier_preimage τ hτZ hb.le false true
    rw [hpre, stripRim_eq_ends_union_arms]
    ac_rfl
  have hmarkL := resolution_strip_arm_frontier_inter τ hτZ hb.le
    (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) false true
  have hmarkR := resolution_strip_arm_frontier_inter τ hτZ hb.le
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) false true
  obtain ⟨nA, nS, p, gAS, V, q, hnA, hnS, _, _, _, hnAp, hnSp,
      hgAS, hkeepA, hkeepS, himAS, _, hballAS, _, hV, hq, hqval, hcontact⟩ :=
    exists_marked_interval_disk_map e hcompat hSA hrect hWA hL hWAQ hLQ
      habA hends pA pL hpA hpL hpA0 hpA1 (hpLval 0) (hpLval 1)
      hfA hfS hagreeL Z hQA hmarkA hmarkL hR hRQ hdisj pR hpR
      (hpRval 0) (hpRval 1) hQS hmarkR
  let a0 : SA := ⟨pA 0, hSA.1 (hWAQ (pA 0).property)⟩
  let a1 : SA := ⟨pA 1, hSA.1 (hWAQ (pA 1).property)⟩
  let β : Path a0 a1 :=
    { toFun := fun t ↦ ⟨qA t, (qA t).property.1⟩
      continuous_toFun := (continuous_subtype_val.comp qA.continuous).subtype_mk _
      source' := Subtype.ext (hqA0.trans hpA0.symm)
      target' := Subtype.ext (hqA1.trans hpA1.symm) }
  have hβ : ∀ t : I01, fA (β t) ∈ Z := fun t ↦ (qA t).property.2
  have hseam0 : (nS (stripSourceCorner 0 false) : P2) = nA a0 := by
    have heq : (⟨pL 0, hrect.1 (hLQ (pL 0).property)⟩ : source) =
        stripSourceCorner 0 false := Subtype.ext (hpLval 0)
    rw [← heq]
    exact (hnSp 0).trans (hnAp 0).symm
  have hseam1 : (nA a1 : P2) = nS (stripSourceCorner 1 false) := by
    have heq : (⟨pL 1, hrect.1 (hLQ (pL 1).property)⟩ : source) =
        stripSourceCorner 1 false := Subtype.ext (hpLval 1)
    rw [← heq]
    exact (hnAp 1).trans (hnSp 1).symm
  have hqcorner (t : I01) : (q t : P2) = nS (stripSourceCorner t true) := by
    rw [hqval]
    exact congrArg (fun x : source ↦ (nS x : P2)) (Subtype.ext (hpRval t))
  have hqends : (q (0 : unitInterval) : P2) ≠ q (1 : unitInterval) := by
    intro h
    have h01 := congrArg (fun t : I01 ↦ (t : ℝ)) (q.injective (Subtype.ext h))
    norm_num at h01
  have hV' : IsFinitePLBallPair ℝ V
      {(nS (stripSourceCorner 0 true) : P2), (nS (stripSourceCorner 1 true) : P2)} := by
    simpa only [hqcorner] using hV
  have hends' : (nS (stripSourceCorner 0 true) : P2) ≠ nS (stripSourceCorner 1 true) := by
    simpa only [hqcorner] using hqends
  have hcontact' : V ∩ gAS ⁻¹' Z =
      {(nS (stripSourceCorner 0 true) : P2), (nS (stripSourceCorner 1 true) : P2)} := by
    simpa only [hqcorner] using hcontact
  have hα (t : I01) : (τ ∘ strip (1 / 4) true) ((stripSourceEndPath 0).symm t) ∈ Z :=
    stripSourceEndPath_maps_to_mark τ hτmark hb.le false true 0 (by simp) _
  have hγ (t : I01) : (τ ∘ strip (1 / 4) true) (stripSourceEndPath 1 t) ∈ Z :=
    stripSourceEndPath_maps_to_mark τ hτmark hb.le false true 1 (by simp) t
  obtain ⟨hB, uB, aB, bB, vB, αB, βB, γB, P, hu, ha, hbB, hv,
    hαlift, hβlift, hγlift, hP, hαtarget, hβtarget, hγtarget, _, _⟩ :=
    exists_marked_attachment_traversal nA nS hgAS.continuousOn hkeepA hkeepS
      hseam0 hseam1 (stripSourceEndPath 0).symm β (stripSourceEndPath 1)
      hα hβ hγ hballAS hV' hends' hcontact'
  have hq0u : (q (0 : unitInterval) : P2) = uB := (hqcorner 0).trans hu.symm
  have hq1v : (q (1 : unitInterval) : P2) = vB := (hqcorner 1).trans hv.symm
  let P0 := (P.map continuous_subtype_val).cast hq0u hq1v
  let P1 := (intervalChartPath qC).cast hqC0.symm hqC1.symm
  let U := (d0.U.symm.trans a).trans d1.U
  have hvalue (t : I01) : (U t : X) = gAS (P0 t) := by
    change (U t : X) = gAS (P t)
    rw [hP]
    dsimp only [U]
    simp only [Path.trans_apply]
    split_ifs
    · rw [hαlift, hkeepS]
      exact (d0.U_val _)
    · rw [hβlift, hkeepA]
      rfl
    · rw [hγlift, hkeepS]
      exact d1.U_val _
  have hagreeC (t : I01) : gAS (q t) = fC (pC t) := by
    rw [hqcorner, hkeepS]
    change τ (strip (1 / 4) true ((t : ℝ), 1)) = fC (pC t)
    rw [(arm_endpoints hb (t : ℝ)).2.1]
    exact (hright t).symm
  obtain ⟨g, R, hg, him, hproper, hRval, hRhom, hsources⟩ :=
    exists_normalized_marked_traversal_with_sources e hcompat hballAS hSC hV hWC
      subset_union_right hWCQ hqends habC q pC hq hpC rfl rfl hpC0 hpC1
      hgAS hfC hagreeC Z rfl hQC hcontact hmarkC
      P0 P1 (fun t ↦ (P t).property.1) (fun t ↦ (qC t).property.1)
      (fun t ↦ (P t).property.2) (fun t ↦ (qC t).property.2)
      d0.c d1.c U cForward hvalue (fun _ ↦ rfl)
  refine ⟨d0, d1, qA, qC, a, cForward.symm, g, R,
    ?_, hqA, hqC, hqA0, hqA1, hqC0, hqC1, fun _ ↦ rfl, ?_, hg, ?_,
    hproper, hRval, hRhom⟩
  · obtain ⟨m, nC, H, pC', hsources⟩ := hsources
    dsimp only at hsources
    obtain ⟨hm, hnC, hH, _, _, _, _, _, _, hkeepAS, hkeepC, hfiberC, _⟩ := hsources
    refine ⟨⟨nA, nS, m, nC, H, ?_, ?_, hm, hnC, hH, ?_, ?_, ?_, ?_, hkeepC⟩⟩
    · assumption
    · assumption
    · intro x y
      have hfiber := prescribed_interval_source_eq_iff
        (hWAQ.trans hSA.1) (hLQ.trans hrect.1) nA nS pA pL p hnAp hnSp x y
      constructor
      · intro hxy
        have huniq := prescribed_interval_source_existsUnique
          (hWAQ.trans hSA.1) (hLQ.trans hrect.1) nA nS pA pL p hnAp hnSp x y hxy
        simpa only [hpLval, Subtype.ext_iff] using huniq
      · rintro ⟨t, ht, _⟩
        apply hfiber.mpr
        refine ⟨t, ht.1, ?_⟩
        simpa only [hpLval] using congrArg Subtype.val ht.2
    · intro x y
      have heq : (H.symm (rightDiskCopy m x) : V2) = H.symm (leftDiskCopy nC y) ↔
          (m x : P2) = nC y := by
        constructor
        · intro h
          exact congrArg Subtype.val (H.symm.injective (Subtype.ext h))
        · intro h
          exact congrArg (fun z : T ↦ (H.symm z : V2)) (Subtype.ext h)
      rw [← heq]
      simpa only [rightDiskCopy, leftDiskCopy, hqcorner, stripSourceCorner, ↓reduceIte] using
        hfiberC x y
    · intro x
      dsimp only [rightDiskCopy]
      rw [hkeepAS, hkeepA]
    · intro x
      dsimp only [rightDiskCopy, leftDiskCopy]
      rw [hkeepAS, hkeepS]
  · intro t
    simp only [Path.symm_symm]
    rfl
  · rw [him, himAS]
    simp only [image_image, Function.comp_def]



theorem exists_normalized_upper_resolution_disk_map
    {EA EC F X ι : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [FiniteDimensional ℝ EA]
    [NormedAddCommGroup EC] [NormedSpace ℝ EC] [FiniteDimensional ℝ EC]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {SA QA WA : Set EA} {SC QC WC : Set EC} {aA bA : EA} {aC bC : EC}
    (hSA : IsFinitePLBallPair P2 SA QA) (hSC : IsFinitePLBallPair P2 SC QC)
    (hWA : IsFinitePLBallPair ℝ WA {aA, bA})
    (hWC : IsFinitePLBallPair ℝ WC {aC, bC})
    (hWAQ : WA ⊆ QA) (hWCQ : WC ⊆ QC) (habA : aA ≠ bA) (habC : aC ≠ bC)
    (pA : I01 ≃ₜ WA) (pC : I01 ≃ₜ WC) (hpA : pA.IsFinitePL) (hpC : pC.IsFinitePL)
    (hpA0 : (pA (0 : unitInterval) : EA) = aA)
    (hpA1 : (pA (1 : unitInterval) : EA) = bA)
    (hpC0 : (pC (0 : unitInterval) : EC) = aC)
    (hpC1 : (pC (1 : unitInterval) : EC) = bC)
    {fA : EA → X} {fC : EC → X} {τ : C3 → X}
    (hfA : PolyhedralPLInCharts e fA SA) (hfC : PolyhedralPLInCharts e fC SC)
    (hτ : PolyhedralPLInCharts e τ tube)
    (hleft : ∀ t : I01, fA (pA t) = τ ((-1, 1), t))
    (hright : ∀ t : I01, fC (pC t) = τ ((1, 1), t))
    (Z : Set X) (hτZ : ∀ z ∈ tube, τ z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1)
    (hQA : QA = (SA ∩ fA ⁻¹' Z) ∪ WA) (hQC : QC = (SC ∩ fC ⁻¹' Z) ∪ WC)
    (hmarkA : WA ∩ fA ⁻¹' Z = {aA, bA}) (hmarkC : WC ∩ fC ⁻¹' Z = {aC, bC}) :
    ∃ (d0 : MarkedResolutionEndData Z τ (1 / 4) 0)
      (d1 : MarkedResolutionEndData Z τ (1 / 4) 1)
      (qA : I01 ≃ₜ (SA ∩ fA ⁻¹' Z : Set EA))
      (qC : I01 ≃ₜ (SC ∩ fC ⁻¹' Z : Set EC))
      (a : Path d0.a d1.a) (c : Path d1.c d0.c) (g : V2 → X) (R : Path d0.c d0.c),
      qA.IsFinitePL ∧ qC.IsFinitePL ∧
      (qA (0 : unitInterval) : EA) = aA ∧ (qA (1 : unitInterval) : EA) = bA ∧
      (qC (0 : unitInterval) : EC) = aC ∧ (qC (1 : unitInterval) : EC) = bC ∧
      (∀ t : I01, (a t : X) = fA (qA t)) ∧
      (∀ t : I01, (c.symm t : X) = fC (qC t)) ∧
      PolyhedralPLInCharts e g D ∧
      g '' D = (fA '' SA ∪ τ '' (strip (1 / 4) true '' source)) ∪ fC '' SC ∧
      (∀ x ∈ D, g x ∈ Z ↔ x ∈ Q) ∧
      (∀ t : I01, (R t : X) = g (squareRimLoop t)) ∧
      R.Homotopic (((d0.U.symm.trans a).trans d1.U).trans c) := by
  obtain ⟨d0, d1, qA, qC, a, c, g, R, _, h⟩ :=
    exists_normalized_upper_resolution_disk_map_with_sources e hcompat hSA hSC hWA hWC
      hWAQ hWCQ habA habC pA pC hpA hpC hpA0 hpA1 hpC0 hpC1 hfA hfC hτ hleft hright
      Z hτZ hQA hQC hmarkA hmarkC
  exact ⟨d0, d1, qA, qC, a, c, g, R, h⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
