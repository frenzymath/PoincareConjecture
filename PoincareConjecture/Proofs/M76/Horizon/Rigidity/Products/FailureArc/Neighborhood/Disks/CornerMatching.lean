import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.PrescribedRectangle
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.Construction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.Rescaling

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior
open PolygonalCrossingResolution CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)
local notation "Ann" => squareAnnulus 8 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {C D : Set P2} {f₀ f₁ : P2 → X}

omit [T2Space X] in
theorem rescaled_sheet_corner_center
    (U : OriginalIntervalTube e R W Ann Ann C D f₀ f₁)
    (r : ℝ) (j b : Bool) (t : ℝ) :
    (U.map ∘ tubeTransverseContraction r) (originalStripSheet j (t,sign b)) =
      originalBandMap U r (b, if j then !b else b) (0,t) := by
  cases j <;> cases b <;>
    simp [originalStripSheet,tubeTransverseContraction_apply,
      originalBandMap,bandMap,sign]

theorem OriginalIntervalTube.exists_first_corner_matched_rectangle
    (U V : OriginalIntervalTube e R W Ann Ann C D f₀ f₁)
    {r : ℝ} (hmap : V.map = U.map ∘ tubeTransverseContraction r)
    (hR : IsCompact R) (he : PLDomain e R)
    (hf : PolyhedralPLInCharts e f₀ Ann) (hfi : InjOn f₀ Ann)
    (hfR : MapsTo f₀ Ann R)
    (hfproper : ∀ x ∈ Ann, f₀ x ∈ frontier R ↔ x ∈ frontier Ann)
    (houter : (C ∩ {p : P2 | depth 8 p = -1}).Nonempty)
    (hinner : (C ∩ {p : P2 | depth 8 p = 1}).Nonempty) :
    ∃ M : FourSidedProperComplementDisk V.first f₀ (R \ V.map '' openTube 1) C,
    ∃ k : P2 → X, PolyhedralPLInCharts e k Rect ∧
      IsEmbedding (fun p : Rect => k p) ∧ MapsTo k Rect (R \ V.map '' openTube 1) ∧
      (∀ p ∈ Rect, k p ∈ frontier (R \ V.map '' openTube 1) ↔ p ∈ frontier Rect) ∧
      k '' Rect = f₀ '' M.carrier ∧ k '' frontier Rect = f₀ '' frontier M.carrier ∧
      k '' Rect = (f₀ '' Ann) ∩ (R \ V.map '' openTube 1) ∧
      (∀ p ∈ Rect, k p ∈ frontier R ↔ p.2 = 0 ∨ p.2 = 1) ∧
      (∀ t ∈ I, k (0,t) = originalBandMap U r (true,true)
        (0,(1-t)*M.outerEnd+t*M.innerEnd)) ∧
      (∀ t ∈ I, k (1,t) = originalBandMap U r (false,false)
        (0,(1-t)*M.outerEnd+t*M.innerEnd)) := by
  obtain ⟨M⟩ := OriginalIntervalTube.nonempty_first_four_sided_complement_disk
    V hR he hfR hfproper houter hinner
  have hci : InjOn V.first source := fun _ hx _ hy h =>
    congrArg Subtype.val (V.first_embedding.injective
      (a₁ := ⟨_,hx⟩) (a₂ := ⟨_,hy⟩) h)
  have hvi : InjOn V.map tube := fun _ hx _ hy h =>
    congrArg Subtype.val (V.embedding.injective (a₁ := ⟨_,hx⟩) (a₂ := ⟨_,hy⟩) h)
  obtain ⟨k,hk,hki,hkQ,hkp,himage,hboundary,_,_,_,_,hparts,hleft,hright⟩ :=
    M.exists_prescribed_original_rectangle V.first_pl hci hf hfi hfproper false
      hvi V.first_preimage V.first_sheet
  have hex := strip_complement_exhausts_exterior false hfR hvi V.first_preimage
    V.first_sheet M.subset_annulus M.cover M.contact
  refine ⟨M,k,hk,hki,hkQ,hkp,himage,hboundary,himage.trans hex.symm,
    fun p hp => (hparts p hp).1,?_,?_⟩
  · intro t ht
    refine (hleft t ht).trans ((congrFun hmap _).trans ?_)
    simpa only [sign,if_true,Bool.false_eq_true,if_false] using
      rescaled_sheet_corner_center U r false true ((1-t)*M.outerEnd+t*M.innerEnd)
  · intro t ht
    refine (hright t ht).trans ((congrFun hmap _).trans ?_)
    simpa only [sign,if_true,Bool.false_eq_true,if_false] using
      rescaled_sheet_corner_center U r false false ((1-t)*M.outerEnd+t*M.innerEnd)

theorem OriginalIntervalTube.exists_second_corner_matched_rectangle
    (U V : OriginalIntervalTube e R W Ann Ann C D f₀ f₁)
    {r : ℝ} (hmap : V.map = U.map ∘ tubeTransverseContraction r)
    (hR : IsCompact R) (he : PLDomain e R)
    (hf : PolyhedralPLInCharts e f₁ Ann) (hfi : InjOn f₁ Ann)
    (hfR : MapsTo f₁ Ann R)
    (hfproper : ∀ x ∈ Ann, f₁ x ∈ frontier R ↔ x ∈ frontier Ann)
    (houter : (D ∩ {p : P2 | depth 8 p = -1}).Nonempty)
    (hinner : (D ∩ {p : P2 | depth 8 p = 1}).Nonempty) :
    ∃ M : FourSidedProperComplementDisk V.second f₁ (R \ V.map '' openTube 1) D,
    ∃ k : P2 → X, PolyhedralPLInCharts e k Rect ∧
      IsEmbedding (fun p : Rect => k p) ∧ MapsTo k Rect (R \ V.map '' openTube 1) ∧
      (∀ p ∈ Rect, k p ∈ frontier (R \ V.map '' openTube 1) ↔ p ∈ frontier Rect) ∧
      k '' Rect = f₁ '' M.carrier ∧ k '' frontier Rect = f₁ '' frontier M.carrier ∧
      k '' Rect = (f₁ '' Ann) ∩ (R \ V.map '' openTube 1) ∧
      (∀ p ∈ Rect, k p ∈ frontier R ↔ p.2 = 0 ∨ p.2 = 1) ∧
      (∀ t ∈ I, k (0,t) = originalBandMap U r (true,false)
        (0,(1-t)*M.outerEnd+t*M.innerEnd)) ∧
      (∀ t ∈ I, k (1,t) = originalBandMap U r (false,true)
        (0,(1-t)*M.outerEnd+t*M.innerEnd)) := by
  obtain ⟨M⟩ := OriginalIntervalTube.nonempty_second_four_sided_complement_disk
    V hR he hfR hfproper houter hinner
  have hci : InjOn V.second source := fun _ hx _ hy h =>
    congrArg Subtype.val (V.second_embedding.injective
      (a₁ := ⟨_,hx⟩) (a₂ := ⟨_,hy⟩) h)
  have hvi : InjOn V.map tube := fun _ hx _ hy h =>
    congrArg Subtype.val (V.embedding.injective (a₁ := ⟨_,hx⟩) (a₂ := ⟨_,hy⟩) h)
  obtain ⟨k,hk,hki,hkQ,hkp,himage,hboundary,_,_,_,_,hparts,hleft,hright⟩ :=
    M.exists_prescribed_original_rectangle V.second_pl hci hf hfi hfproper true
      hvi V.second_preimage V.second_sheet
  have hex := strip_complement_exhausts_exterior true hfR hvi V.second_preimage
    V.second_sheet M.subset_annulus M.cover M.contact
  refine ⟨M,k,hk,hki,hkQ,hkp,himage,hboundary,himage.trans hex.symm,
    fun p hp => (hparts p hp).1,?_,?_⟩
  · intro t ht
    refine (hleft t ht).trans ((congrFun hmap _).trans ?_)
    simpa only [sign,if_true,Bool.not_true] using
      rescaled_sheet_corner_center U r true true ((1-t)*M.outerEnd+t*M.innerEnd)
  · intro t ht
    refine (hright t ht).trans ((congrFun hmap _).trans ?_)
    simpa only [sign,Bool.false_eq_true,if_false,if_true,Bool.not_false] using
      rescaled_sheet_corner_center U r true false ((1-t)*M.outerEnd+t*M.innerEnd)

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
