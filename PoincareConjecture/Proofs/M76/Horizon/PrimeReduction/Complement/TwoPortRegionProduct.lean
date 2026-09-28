import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.CircleSurgeryBoundary
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusFinitePL
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryPieceGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

private theorem finitePL_rectangle_affine {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : P2 →ᴬ[ℝ] F) :
    FinitePiecewiseAffineOn A (rectangle (4 * 8) 1) := by
  have hbox := (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 4 * 8)).prod
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hbox
  exact ⟨K, hK, hKs, K.affineOnFaces_affine A⟩

private noncomputable def squareBandPeriod (p : P2) : C3 :=
  (wrappedStripMap 8 (p.1, 0), p.2)

private theorem squareBandPeriod_finitePL :
    FinitePiecewiseAffineOn squareBandPeriod (rectangle (4 * 8) 1) := by
  let A : P2 →ᴬ[ℝ] P2 :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap.prod
      (ContinuousAffineMap.const ℝ P2 0)
  have hA := finitePL_rectangle_affine A
  have hw := finitePiecewiseAffineOn_wrappedStripMap
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8)
  have hmap : MapsTo A (rectangle (4 * 8) 1) (rectangle (4 * 8) 1) := by
    intro p hp
    exact ⟨hp.1, by norm_num [A]⟩
  exact (hw.comp hA hmap).prod_mk
    (finitePL_rectangle_affine (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap)

private theorem squareBandPeriod_fibers
    (x : P2) (hx : x ∈ rectangle (4 * 8) 1)
    (y : P2) (hy : y ∈ rectangle (4 * 8) 1) :
    squareBandPeriod x = squareBandPeriod y ↔ x.2 = y.2 ∧
      (x.1 : AddCircle (4 * 8 : ℝ)) = (y.1 : AddCircle (4 * 8 : ℝ)) := by
  have hxval := annulusMap_coe (by norm_num : (0 : ℝ) < 8)
    (by norm_num : (4 : ℝ) * |(0 : ℝ)| < 8) hx.1
  have hyval := annulusMap_coe (by norm_num : (0 : ℝ) < 8)
    (by norm_num : (4 : ℝ) * |(0 : ℝ)| < 8) hy.1
  constructor
  · intro h
    have heq := congrArg Prod.fst h
    change wrappedStripMap 8 (x.1, 0) = wrappedStripMap 8 (y.1, 0) at heq
    rw [← hxval, ← hyval] at heq
    have hi := injective_annulusMap (d := (0 : ℝ))
      (by norm_num : (0 : ℝ) < 8) (by norm_num : (4 : ℝ) * 0 < 8)
    have hp := hi (a₁ := ((x.1 : AddCircle (4 * 8 : ℝ)), ⟨0, by norm_num⟩))
      (a₂ := ((y.1 : AddCircle (4 * 8 : ℝ)), ⟨0, by norm_num⟩)) heq
    have hpc : (x.1 : AddCircle (4 * 8 : ℝ)) =
        (y.1 : AddCircle (4 * 8 : ℝ)) := congrArg Prod.fst hp
    exact ⟨congrArg (fun z : C3 => z.2) h, hpc⟩
  · rintro ⟨ht, hs⟩
    apply Prod.ext
    · change wrappedStripMap 8 (x.1, 0) = wrappedStripMap 8 (y.1, 0)
      rw [← hxval, ← hyval, hs]
    · exact ht

private theorem zero_annulus_eq_frontier :
    squareAnnulus 8 0 = frontier (_root_.Dehn.annulusSquare 8 0) := by
  ext p
  rw [mem_squareAnnulus_iff_depth, _root_.Dehn.mem_frontier_annulusSquare_iff]
  simp only [neg_zero, mem_Icc]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => by simp [h]⟩

private theorem squareBandPeriod_image :
    squareBandPeriod '' rectangle (4 * 8) 1 =
      frontier (_root_.Dehn.annulusSquare 8 0) ×ˢ Icc (-1 : ℝ) 1 := by
  have himage := wrappedStripMap_image (L := (8 : ℝ)) (d := (0 : ℝ))
    (by norm_num) (by norm_num)
  rw [zero_annulus_eq_frontier] at himage
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨himage.subset ⟨(p.1, 0), ⟨hp.1, by norm_num⟩, rfl⟩, hp.2⟩
  · intro hz
    obtain ⟨p, hp, hval⟩ := himage.symm.subset hz.1
    have hp0 : p.2 = 0 := le_antisymm hp.2.2 (by simpa using hp.2.1)
    refine ⟨(p.1, z.2), ⟨hp.1, hz.2⟩, ?_⟩
    apply Prod.ext
    · change wrappedStripMap 8 (p.1, 0) = z.1
      simpa only [← hp0] using hval
    · rfl

theorem exists_square_product_band_annulus :
    ∃ c : squareAnnulus 8 1 ≃ₜ
        (frontier (_root_.Dehn.annulusSquare 8 0) ×ˢ Icc (-1 : ℝ) 1 : Set C3),
      c.IsFinitePL ∧ ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * 8)) (u : Icc (-1 : ℝ) 1),
        (c ⟨annulusMap 8 (by norm_num) ((s : AddCircle (4 * 8 : ℝ)), u),
          _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : C3) =
            (wrappedStripMap 8 (s, 0), (u : ℝ)) := by
  obtain ⟨c, hc, _, hperiod, _⟩ := _root_.Dehn.exists_finitePL_annulus_of_periodic_strip
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8)
    squareBandPeriod squareBandPeriod_finitePL squareBandPeriod_fibers
  exact ⟨c.trans (Homeomorph.setCongr squareBandPeriod_image),
    hc.setCongr rfl squareBandPeriod_image, hperiod⟩

private theorem periodic_annulus_rim_mem_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B q : Set E} (c : squareAnnulus 8 1 ≃ₜ B) (φ : P2 → E)
    (hperiod : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * 8)) (u : Icc (-1 : ℝ) 1),
      (c ⟨annulusMap 8 (by norm_num) ((s : AddCircle (4 * 8 : ℝ)), u),
        _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : E) = φ (s,u))
    {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1)
    (hq : (fun s => φ (s,u)) '' Icc 0 (4 * 8) = q) (p : squareAnnulus 8 1) :
    (c p : E) ∈ q ↔ depth 8 p = u := by
  constructor
  · intro hp
    obtain ⟨s, hs, hsp⟩ := hq.symm.subset hp
    let z : squareAnnulus 8 1 :=
      ⟨annulusMap 8 (by norm_num) ((s : AddCircle (4 * 8 : ℝ)), u),
        _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ ⟨u, hu⟩⟩
    have heq : z = p := c.injective (Subtype.ext ((hperiod s hs ⟨u, hu⟩).trans hsp))
    rw [← heq]
    exact depth_annulusMap (by norm_num) (by have := abs_le.mpr hu; linarith) _
  · intro hp
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8) p
    rw [hp] at hsp
    apply hq.subset
    refine ⟨s, hs, ?_⟩
    exact (hperiod s hs ⟨u, hu⟩).symm.trans
      (congrArg (fun z : squareAnnulus 8 1 => (c z : E)) (Subtype.ext hsp.symm))

theorem exists_circle_band_product_comparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {β : ℝ} (hβ : 0 < β) (τ : C3 → E)
    (hτ : FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc 0 β))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0))) :
    let band := (fun z : P2 => τ ((z.1,0),z.2)) ''
      (Icc (-1/4:ℝ) (1/4) ×ˢ Icc 0 β)
    ∃ e : band ≃ₜ
        (frontier (_root_.Dehn.annulusSquare 8 0) ×ˢ Icc (-1 : ℝ) 1 : Set C3),
      e.IsFinitePL ∧ ∀ (b : Bool) (x : band),
        (x : E) ∈ (fun t => τ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β ↔
          (e x : C3) ∈ frontier (_root_.Dehn.annulusSquare 8 0) ×ˢ
            {if b then (1 : ℝ) else -1} := by
  obtain ⟨c, hc, _, hperiod⟩ := exists_circle_sphere_band_annulus hβ τ hτ hfib
  obtain ⟨d, hd, hdperiod⟩ := exists_square_product_band_annulus
  have hdheight (p : squareAnnulus 8 1) : (d p : C3).2 = depth 8 p := by
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8) p
    let u : Icc (-1 : ℝ) 1 := ⟨depth 8 p, mem_squareAnnulus_iff_depth.mp p.property⟩
    have heq : (⟨annulusMap 8 (by norm_num) ((s : AddCircle (4 * 8 : ℝ)), u),
        _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ :
        squareAnnulus 8 1) = p := Subtype.ext hsp.symm
    have h := congrArg (fun z : C3 => z.2) (hdperiod s hs u)
    rwa [heq] at h
  refine ⟨c.symm.trans d, hc.symm.trans hd, ?_⟩
  intro b x
  have hu : (if b then (1 : ℝ) else -1) ∈ Icc (-1 : ℝ) 1 := by
    cases b <;> norm_num
  have hq : (fun s => τ (((if b then (1 : ℝ) else -1) / 4, 0), β/32*s)) ''
      Icc 0 (4*8) = (fun t => τ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β := by
    cases b <;> simpa using cap_circle_period_rescaling hβ τ _
  have hmem := periodic_annulus_rim_mem_iff c
    (fun z : P2 => τ ((z.2/4,0),β/32*z.1)) hperiod hu hq (c.symm x)
  rw [c.apply_symm_apply] at hmem
  rw [hmem]
  change depth 8 (c.symm x) = _ ↔
    (d (c.symm x) : C3).1 ∈ frontier (_root_.Dehn.annulusSquare 8 0) ∧
      (d (c.symm x) : C3).2 = _
  rw [hdheight]
  exact (and_iff_right (d (c.symm x)).property.1).symm

private theorem extend_two_disjoint_caps
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {band : Set E} {Band : Set F} (caps q : Bool → Set E) (Caps Q : Bool → Set F)
    (hcaps : ∀ b, IsFinitePLBallPair P2 (caps b) (q b))
    (hCaps : ∀ b, IsFinitePLBallPair P2 (Caps b) (Q b))
    (hmeet : ∀ b, caps b ∩ band = q b) (hMeet : ∀ b, Caps b ∩ Band = Q b)
    (hdis : Disjoint (caps true) (caps false)) (hDis : Disjoint (Caps true) (Caps false))
    (e : band ≃ₜ Band) (he : e.IsFinitePL)
    (hmem : ∀ b (x : band), (x : E) ∈ q b ↔ (e x : F) ∈ Q b) :
    ∃ H : (caps false ∪ (caps true ∪ band) : Set E) ≃ₜ
        (Caps false ∪ (Caps true ∪ Band) : Set F), H.IsFinitePL ∧
      ∀ b (x : (caps false ∪ (caps true ∪ band) : Set E)),
        (x : E) ∈ caps b ↔ (H x : F) ∈ Caps b := by
  obtain ⟨G, hG, hkeep, hGcap, hGband⟩ :=
    (hcaps true).exists_union_homeomorph_of_boundary_piece (hCaps true)
      (hmeet true) (hMeet true) e he (hmem true)
  have hqband (b : Bool) : q b ⊆ band := by rw [← hmeet b]; exact inter_subset_right
  have hQband (b : Bool) : Q b ⊆ Band := by rw [← hMeet b]; exact inter_subset_right
  have hinter : caps false ∩ (caps true ∪ band) = q false := by
    rw [inter_union_distrib_left, hdis.symm.inter_eq, empty_union, hmeet false]
  have hInter : Caps false ∩ (Caps true ∪ Band) = Q false := by
    rw [inter_union_distrib_left, hDis.symm.inter_eq, empty_union, hMeet false]
  have hmemG (x : (caps true ∪ band : Set E)) :
      (x : E) ∈ q false ↔ (G x : F) ∈ Q false := by
    by_cases hx : (x : E) ∈ band
    · have hv := congrArg (fun z : (Caps true ∪ Band : Set F) => (z : F))
        (hkeep ⟨x, hx⟩)
      change (G x : F) = e ⟨x, hx⟩ at hv
      rw [hv]
      exact hmem false ⟨x, hx⟩
    · exact iff_of_false (fun h => hx (hqband false h))
        (fun h => hx ((hGband x).mpr (hQband false h)))
  obtain ⟨H, hH, hHkeep, hHfalse, _⟩ :=
    (hcaps false).exists_union_homeomorph_of_boundary_piece (hCaps false)
      hinter hInter G hG hmemG
  let g := G.restrictSubsets subset_union_left subset_union_left hGcap
  have hkeeptrue (x : caps true) :
      H ⟨x, Or.inr (Or.inl x.property)⟩ =
        ⟨g x, Or.inr (Or.inl (g x).property)⟩ := by
    apply Subtype.ext
    exact congrArg (fun z : (Caps false ∪ (Caps true ∪ Band) : Set F) => (z : F))
      (hHkeep ⟨x, Or.inl x.property⟩)
  have hHtrue := H.mem_subset_iff_of_extension g
    (subset_union_left.trans subset_union_right)
    (subset_union_left.trans subset_union_right) hkeeptrue
  exact ⟨H, hH, fun b => by cases b; exact hHfalse; exact hHtrue⟩

theorem exists_circle_two_port_boundary_comparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {β : ℝ} (hβ : 0 < β) (τ : C3 → E)
    (hτ : FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc 0 β))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0)))
    {M : Set E}
    (hsphere : ∀ z ∈ signedTubeDiamond ×ˢ Icc 0 β, τ z ∈ M ↔ z.1.2 = 0)
    (caps : Bool → Set E)
    (hcaps : ∀ b, IsFinitePLBallPair P2 (caps b)
      ((fun t => τ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β))
    (hcapM : ∀ b, caps b ∩ M =
      (fun t => τ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β)
    (hdis : Disjoint (caps true) (caps false)) :
    let band := (fun z : P2 => τ ((z.1,0),z.2)) ''
      (Icc (-1/4:ℝ) (1/4) ×ˢ Icc 0 β)
    let D := _root_.Dehn.annulusSquare 8 0
    ∃ H : (band ∪ (caps true ∪ caps false) : Set E) ≃ₜ
        ((frontier D ×ˢ Icc (-1 : ℝ) 1) ∪ (D ×ˢ {(-1 : ℝ), 1}) : Set C3),
      H.IsFinitePL ∧ ∀ b (x : (band ∪ (caps true ∪ caps false) : Set E)),
        (x : E) ∈ caps b ↔ (H x : C3) ∈ D ×ˢ {if b then (1 : ℝ) else -1} := by
  dsimp only
  let band := (fun z : P2 => τ ((z.1,0),z.2)) ''
    (Icc (-1/4:ℝ) (1/4) ×ˢ Icc 0 β)
  let D := _root_.Dehn.annulusSquare 8 0
  let Band : Set C3 := frontier D ×ˢ Icc (-1 : ℝ) 1
  let q : Bool → Set E := fun b =>
    (fun t => τ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β
  let Caps : Bool → Set C3 := fun b => D ×ˢ {if b then (1 : ℝ) else -1}
  let Q : Bool → Set C3 := fun b => frontier D ×ˢ {if b then (1 : ℝ) else -1}
  have hD : IsFinitePLBallPair P2 D (frontier D) :=
    _root_.Dehn.isFinitePLBallPair_annulusSquare (by norm_num)
  have hbandM : band ⊆ M := by
    rintro _ ⟨z, hz, rfl⟩
    apply (hsphere _ ⟨(signedTubeDiamond_coordinate_iff _).mpr ?_, hz.2⟩).mpr rfl
    rw [abs_zero, add_zero, abs_le]
    constructor <;> linarith [hz.1.1, hz.1.2]
  have hmeet (b : Bool) : caps b ∩ band = q b := by
    apply Subset.antisymm
    · exact fun _ hx => (hcapM b).subset ⟨hx.1, hbandM hx.2⟩
    · rintro _ hx
      refine ⟨(hcaps b).1 hx, ?_⟩
      obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨(if b then 1/4 else -1/4,t), ⟨by cases b <;> norm_num, ht⟩, rfl⟩
  have hMeet (b : Bool) : Caps b ∩ Band = Q b := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.2.1, hz.1.2⟩
    · intro hz
      refine ⟨⟨hD.1 hz.1, hz.2⟩, hz.1, ?_⟩
      rw [show z.2 = if b then (1 : ℝ) else -1 from hz.2]
      cases b <;> norm_num
  have hDis : Disjoint (Caps true) (Caps false) := by
    apply disjoint_left.mpr
    intro z hz ht
    have hz1 : z.2 = 1 := hz.2
    have hz0 : z.2 = -1 := ht.2
    linarith
  obtain ⟨e, he, hmem⟩ := exists_circle_band_product_comparison hβ τ hτ hfib
  obtain ⟨H, hH, hHcaps⟩ := extend_two_disjoint_caps caps q Caps Q hcaps
    (fun b => hD.prod_singleton _) hmeet hMeet hdis hDis e he hmem
  have hsrc : caps false ∪ (caps true ∪ band) = band ∪ (caps true ∪ caps false) := by
    ext x; simp only [mem_union]; tauto
  have htgt : Caps false ∪ (Caps true ∪ Band) =
      (frontier D ×ˢ Icc (-1 : ℝ) 1) ∪ (D ×ˢ {(-1 : ℝ), 1}) := by
    ext z
    simp only [Caps, Band, Bool.false_eq_true, if_false, if_true,
      mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  exact ⟨(Homeomorph.setCongr hsrc.symm).trans (H.trans (Homeomorph.setCongr htgt)),
    hH.setCongr hsrc htgt, fun b x => hHcaps b ⟨x, hsrc.symm.subset x.property⟩⟩

theorem exists_circle_two_port_region_comparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {β : ℝ} (hβ : 0 < β) (τ : C3 → E)
    (hτ : FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc 0 β))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0)))
    {M : Set E}
    (hsphere : ∀ z ∈ signedTubeDiamond ×ˢ Icc 0 β, τ z ∈ M ↔ z.1.2 = 0)
    (caps : Bool → Set E)
    (hcaps : ∀ b, IsFinitePLBallPair P2 (caps b)
      ((fun t => τ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β))
    (hcapM : ∀ b, caps b ∩ M =
      (fun t => τ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β)
    (hdis : Disjoint (caps true) (caps false))
    {R : Set E}
    (hR : IsFinitePLBallPair C3 R
      (((fun z : P2 => τ ((z.1,0),z.2)) ''
        (Icc (-1/4:ℝ) (1/4) ×ˢ Icc 0 β)) ∪ (caps true ∪ caps false))) :
    let D := _root_.Dehn.annulusSquare 8 0
    ∃ H : R ≃ₜ (D ×ˢ Icc (-1 : ℝ) 1 : Set C3),
      H.IsFinitePL ∧ ∀ b (x : R),
        (x : E) ∈ caps b ↔ (H x : C3) ∈ D ×ˢ {if b then (1 : ℝ) else -1} := by
  dsimp only
  let D := _root_.Dehn.annulusSquare 8 0
  let band := (fun z : P2 => τ ((z.1,0),z.2)) ''
    (Icc (-1/4:ℝ) (1/4) ×ˢ Icc 0 β)
  let B := band ∪ (caps true ∪ caps false)
  let Q := (frontier D ×ˢ Icc (-1 : ℝ) 1) ∪ (D ×ˢ {(-1 : ℝ), 1})
  have hD : IsFinitePLBallPair P2 D (frontier D) :=
    _root_.Dehn.isFinitePLBallPair_annulusSquare (by norm_num)
  have hP : IsFinitePLBallPair C3 (D ×ˢ Icc (-1 : ℝ) 1) Q :=
    hD.prod (isFinitePLBallPair_Icc (by norm_num))
  obtain ⟨eb, heb, hebcaps⟩ :=
    exists_circle_two_port_boundary_comparison hβ τ hτ hfib hsphere caps hcaps hcapM hdis
  obtain ⟨H, hH, hkeep, _⟩ := hR.exists_extension hP eb heb
  refine ⟨H, hH, fun b => ?_⟩
  have hcb : caps b ⊆ B := by
    intro x hx
    cases b
    · exact Or.inr (Or.inr hx)
    · exact Or.inr (Or.inl hx)
  have hCQ : D ×ˢ {if b then (1 : ℝ) else -1} ⊆ Q := by
    intro x hx
    apply Or.inr
    refine ⟨hx.1, ?_⟩
    cases b
    · exact Or.inl hx.2
    · exact Or.inr hx.2
  let ec := eb.restrictSubsets hcb hCQ (hebcaps b)
  exact H.mem_subset_iff_of_extension ec (hcb.trans hR.1) (hCQ.trans hP.1)
    (fun x => hkeep ⟨x, hcb x.property⟩)

theorem exists_circle_two_port_product_handle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {β : ℝ} (hβ : 0 < β) (τ : C3 → E)
    (hτ : FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc 0 β))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0)))
    {M : Set E}
    (hsphere : ∀ z ∈ signedTubeDiamond ×ˢ Icc 0 β, τ z ∈ M ↔ z.1.2 = 0)
    (caps : Bool → Set E)
    (hcaps : ∀ b, IsFinitePLBallPair P2 (caps b)
      ((fun t => τ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β))
    (hcapM : ∀ b, caps b ∩ M =
      (fun t => τ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β)
    (hdis : Disjoint (caps true) (caps false))
    {R : Set E}
    (hR : IsFinitePLBallPair C3 R
      (((fun z : P2 => τ ((z.1,0),z.2)) ''
        (Icc (-1/4:ℝ) (1/4) ×ˢ Icc 0 β)) ∪ (caps true ∪ caps false))) :
    let D := _root_.Dehn.annulusSquare 8 0
    ∃ C : (↑D × unitInterval) ≃ₜ R,
      ((Homeomorph.Set.prod D (Icc (0 : ℝ) 1)).trans C).IsFinitePL ∧
      ∀ b z, (C z : E) ∈ caps b ↔ z.2 = if b then 1 else 0 := by
  dsimp only
  let D := _root_.Dehn.annulusSquare 8 0
  obtain ⟨H, hH, hHcaps⟩ :=
    exists_circle_two_port_region_comparison hβ τ hτ hfib hsphere caps hcaps hcapM hdis hR
  obtain ⟨e, he, he0, he1⟩ :=
    (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)).exists_unitInterval_chart_with_endpoints
      (by norm_num : (-1 : ℝ) ≠ 1)
  change (e (0 : unitInterval) : ℝ) = -1 at he0
  change (e (1 : unitInterval) : ℝ) = 1 at he1
  let C : (↑D × unitInterval) ≃ₜ R :=
    ((Homeomorph.refl D).prodCongr e).trans
      ((Homeomorph.Set.prod D (Icc (-1 : ℝ) 1)).symm.trans H.symm)
  have hDid : (Homeomorph.refl D).IsFinitePL := by
    have hD : IsFinitePLBallPair P2 D (frontier D) :=
      _root_.Dehn.isFinitePLBallPair_annulusSquare (by norm_num)
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKD, _⟩, _⟩, _⟩ :=
      hD
    exact ⟨id, ⟨K, hK, hKD, K.affineOnFaces_affine
      (ContinuousAffineMap.id ℝ P2)⟩, fun _ => rfl⟩
  refine ⟨C, ?_, ?_⟩
  · exact (hDid.prod he).trans hH.symm
  · intro b z
    have h := hHcaps b (C z)
    change (C z : E) ∈ caps b ↔
      (H (H.symm ((Homeomorph.Set.prod D (Icc (-1 : ℝ) 1)).symm
        (((Homeomorph.refl D).prodCongr e) z))) : C3) ∈
        D ×ˢ {if b then (1 : ℝ) else -1} at h
    rw [H.apply_symm_apply] at h
    change (C z : E) ∈ caps b ↔ z.1.val ∈ D ∧
      (e z.2 : ℝ) = if b then 1 else -1 at h
    rw [h, and_iff_right z.1.property]
    have hendpoint : (e (if b then (1 : unitInterval) else 0) : ℝ) =
        if b then 1 else -1 := by
      cases b <;> assumption
    constructor
    · intro hz
      apply e.injective
      exact Subtype.ext (hz.trans hendpoint.symm)
    · intro hz
      rw [hz]
      exact hendpoint

end PoincareConjecture.M76
