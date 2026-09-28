import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.RemovedComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Contacts.CutOverlap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.Matching.SuccessiveCuts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.Domain
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.Assembly

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution BoundaryAssembly

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "Disk" => closedBall (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

private theorem closure_image_of_compact_closure
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {A B : Set E} {f : E → X} (hAB : closure A = B)
    (hB : IsCompact B) (hf : ContinuousOn f B) : closure (f '' A) = f '' B := by
  apply Subset.antisymm
  · exact closure_minimal (image_mono (hAB ▸ subset_closure))
      (hB.image_of_continuousOn hf).isClosed
  · rw [← hAB] at hf ⊢
    exact hf.image_closure

theorem closure_removed_longitudinal_slice
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b)) (t : I) :
    closure (removedLongitudinalSlice U r P t) =
      ⋃ i, range (fun z => pieceParameter U P r i (z,t)) := by
  rw [piece_slice_eq,removedLongitudinalSlice,closure_union,closure_iUnion_of_finite]
  congr 1
  · apply closure_image_of_compact_closure
    · rw [closure_prod_eq,closure_prod_eq,closure_Ioo (by linarith : -r ≠ r),
        closure_singleton]
      rfl
    · exact (isCompact_Icc.prod isCompact_Icc).prod isCompact_singleton
    · exact U.pl.continuousOn.mono (fun z hz => closedTube_subset hr1 ⟨hz.1,hz.2 ▸ t.property⟩)
  · apply iUnion_congr
    intro b
    apply closure_image_of_compact_closure
    · rw [closure_prod_eq,closure_prod_eq,isClosed_Icc.closure_eq,
        closure_Ioo (by norm_num : (-1/2 : ℝ) ≠ 1/2),closure_singleton]
      norm_num [stripBase]
    · exact (isCompact_Icc.prod isCompact_Icc).prod isCompact_singleton
    · exact (diskStrip_properties (P b)).1.continuousOn.mono (fun z hz => ⟨hz.1,hz.2 ▸ t.property⟩)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}
  (U : OriginalIntervalTube e R W S T C D f₀ f₁)
  (hR : IsCompact R) (he : PLDomain e R)
  {r w : ℝ} (hw : 0 < w) (hr1 : r ≤ 1)
  {j : Bool → V2 → X}
  (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
  (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
  (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w/ρ b ≤ 1)
  (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J, (P b).map (z,s) = F b (z,(w/ρ b)*s))
  (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
    F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
  (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
    F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)

include hR he hw hr1 F ρ hρ hρr hwρ hmark harms hlateral

theorem relative_closure_removed_longitudinal_slice
    (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    closure ((Subtype.val : connectedComponentIn (frontier R) (U.map ((0,0),t)) → X) ⁻¹'
      removedLongitudinalSlice U r P t) =
      Subtype.val ⁻¹' (⋃ i, range (fun z => pieceParameter U P r i (z,t))) := by
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    Subtype.image_preimage_coe,inter_eq_right.mpr
      (removed_longitudinal_slice_subset_component U hR he hw hr1 P F ρ hρ hρr hwρ
        hmark harms hlateral t ht),
    closure_removed_longitudinal_slice U ((hρ false).trans (hρr false)) hr1 P t]

theorem closed_neighborhood_inter_component
    (hdistinct : connectedComponentIn (frontier R) (U.map ((0,0),0)) ≠
      connectedComponentIn (frontier R) (U.map ((0,0),1)))
    (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    (⋃ i, range (pieceParameter U P r i)) ∩
      connectedComponentIn (frontier R) (U.map ((0,0),t)) =
        ⋃ i, range (fun z => pieceParameter U P r i (z,t)) := by
  apply Subset.antisymm
  · rintro x ⟨hx,hxt⟩
    obtain ⟨i,⟨z,s⟩,rfl⟩ := mem_iUnion.mp hx
    have hs := (pieceMap_mem_original_frontier_iff U hR he hw hr1 P F ρ hρ hρr hwρ
      hmark harms hlateral i z.property s.property).mp
        (connectedComponentIn_subset _ _ hxt)
    have hxs := closed_longitudinal_slice_subset_component U hR he hw hr1 P F ρ
      hρ hρr hwρ hmark harms hlateral s hs (mem_iUnion.mpr ⟨i,mem_range_self z⟩)
    have heq := (connectedComponentIn_eq hxs).trans (connectedComponentIn_eq hxt).symm
    have hst : (s : ℝ) = t := by
      rcases hs with hs | hs <;> rcases ht with ht | ht
      · exact hs.trans ht.symm
      · exact False.elim (hdistinct (by simpa only [hs,ht] using heq))
      · exact False.elim (hdistinct (by simpa only [hs,ht] using heq.symm))
      · exact hs.trans ht.symm
    have hst' : s = t := Subtype.ext hst
    subst s
    exact mem_iUnion.mpr ⟨i,mem_range_self z⟩
  · intro x hx
    refine ⟨?_,closed_longitudinal_slice_subset_component U hR he hw hr1 P F ρ hρ hρr hwρ
      hmark harms hlateral t ht hx⟩
    obtain ⟨i,z,rfl⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i,mem_range_self (z,t)⟩

theorem removed_longitudinal_slice_relative_frontier
    (hrlt : r < 1)
    (hdis : Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)))
    (hopen : ∀ b v, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
        ((P b).map '' (Disk ×ˢ Ioo (-v) v))))
    (hdistinct : connectedComponentIn (frontier R) (U.map ((0,0),0)) ≠
      connectedComponentIn (frontier R) (U.map ((0,0),1)))
    (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    let Z := connectedComponentIn (frontier R) (U.map ((0,0),t))
    let O := (Subtype.val : Z → X) ⁻¹' removedLongitudinalSlice U r P t
    let N := (Subtype.val : Z → X) ⁻¹'
      (⋃ i, range (fun z => pieceParameter U P r i (z,t)))
    IsOpen O ∧ closure O = N ∧
      frontier O = (Subtype.val : Z → X) ⁻¹'
        (⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {(t : ℝ)})) := by
  dsimp only
  let Z := connectedComponentIn (frontier R) (U.map ((0,0),t))
  let O := U.map '' openTube r ∪ (P false).openStrip ∪ (P true).openStrip
  let N := U.map '' closedTube r ∪ ((P false).closedStrip ∪ (P true).closedStrip)
  have hr := (hρ false).trans (hρr false)
  have hcQ := TubeExterior.OriginalIntervalTube.isCompact_exterior U hR he hr hr1
  have heQ := TubeExterior.OriginalIntervalTube.plDomain_exterior U hR he hr hrlt
  have hopen₀ := hopen false (1/2) (by norm_num) (by norm_num)
  obtain ⟨Q₁,hmap,_,_,_,hcompact,hsdis,hopen₁,_⟩ :=
    exists_unchanged_product_in_disjoint_cut (P false) (P true) hcQ heQ hopen₀ hdis
      (hopen true)
  have hcut : Q₁.cutCarrier = R \ O := by
    simp only [OriginalDiskProduct.cutCarrier,OriginalDiskProduct.openStrip,hmap,O]
    ext x
    simp only [mem_sdiff,mem_union]
    tauto
  have hOopen : IsOpen ((Subtype.val : R → X) ⁻¹' O) := by
    have hc := hcompact.isClosed.preimage (continuous_subtype_val : Continuous (Subtype.val : R → X))
    have heq : (Subtype.val : R → X) ⁻¹' Q₁.cutCarrier =
        ((Subtype.val : R → X) ⁻¹' O)ᶜ := by
      ext x
      simp only [hcut,mem_preimage,mem_sdiff,x.property,true_and,mem_compl_iff]
    rw [heq] at hc
    exact isClosed_compl_iff.mp hc
  have hZR : Z ⊆ R := (connectedComponentIn_subset _ _).trans he.closed.frontier_subset
  have hOZ := hOopen.preimage (continuous_inclusion hZR)
  have hslice := removed_neighborhood_inter_component U hR he hw hr1 P F ρ hρ hρr hwρ
    hmark harms hlateral hdistinct t ht
  have hpre : (Subtype.val : Z → X) ⁻¹' O = Subtype.val ⁻¹' removedLongitudinalSlice U r P t := by
    ext x
    exact ⟨fun hx => hslice.subset ⟨hx,x.property⟩,
      fun hx => (hslice.symm.subset hx).1⟩
  change IsOpen ((Subtype.val : Z → X) ⁻¹' O) at hOZ
  rw [hpre] at hOZ
  have hclosure := relative_closure_removed_longitudinal_slice U hR he hw hr1 P F ρ hρ hρr
    hwρ hmark harms hlateral t ht
  refine ⟨hOZ,hclosure,?_⟩
  change closure ((Subtype.val : Z → X) ⁻¹' removedLongitudinalSlice U r P t) \
    interior ((Subtype.val : Z → X) ⁻¹' removedLongitudinalSlice U r P t) = _
  rw [hclosure,hOZ.interior_eq]
  have hinter := (neighborhood_final_cut_overlap U hR he hw hr1 P F ρ hρ hρr hwρ
    hmark harms hlateral Q₁ hmap hsdis hopen₀ hopen₁).1
  have hclosedSlice := closed_neighborhood_inter_component U hR he hw hr1 P F ρ hρ hρr
    hwρ hmark harms hlateral hdistinct t ht
  rw [ProductConstruction.pieceParameter_range U P] at hclosedSlice
  have hwr : w/2 < r := by
    have h := (div_le_iff₀ (hρ false)).mp (hwρ false)
    linarith [hρr false]
  have hrim := final_panel_annulus_inter_component_eq_rim U hR he hw hr1 P F ρ hρ hρr
    hwρ hmark harms hlateral hwr hdistinct t ht
  ext x
  simp only [mem_sdiff,mem_preimage]
  rw [← hclosedSlice,← hrim,← hinter,hcut]
  change ((x.val ∈ N ∧ x.val ∈ Z) ∧ x.val ∉ removedLongitudinalSlice U r P t) ↔
    (x.val ∈ N ∧ x.val ∈ R \ O) ∧ x.val ∈ Z
  have hmem : x.val ∈ removedLongitudinalSlice U r P t ↔ x.val ∈ O :=
    ⟨fun hx => (hslice.symm.subset hx).1,fun hx => hslice.subset ⟨hx,x.property⟩⟩
  rw [hmem]
  simp only [mem_sdiff,x.property,hZR x.property,true_and,and_true]

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
