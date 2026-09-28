import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.FourSideParameter
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.MarkedComplementDisks
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)
local notation "Ann" => squareAnnulus 8 1

theorem FourSidedProperComplementDisk.original_rectangle_of_parameter
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {center : Set P2}
    {c g : P2 → P2} {f : P2 → X}
    (M : FourSidedProperComplementDisk c f Q center)
    (hf : PolyhedralPLInCharts e f Ann) (hfi : InjOn f Ann)
    (hg : FinitePiecewiseAffineOn g Rect) (hgbij : BijOn g Rect M.carrier)
    (hboundary : g '' frontier Rect = frontier M.carrier) :
    PolyhedralPLInCharts e (f ∘ g) Rect ∧ IsEmbedding (fun x : Rect => f (g x)) ∧
      MapsTo (f ∘ g) Rect Q ∧
      (∀ x ∈ Rect, f (g x) ∈ frontier Q ↔ x ∈ frontier Rect) := by
  have hfrontsub : frontier Rect ⊆ Rect :=
    (isClosed_Icc.prod isClosed_Icc).frontier_subset
  have hgproper (x : P2) (hx : x ∈ Rect) :
      g x ∈ frontier M.carrier ↔ x ∈ frontier Rect := by
    rw [← hboundary]
    exact hgbij.2.1.mem_image_iff hfrontsub hx
  have hk : PolyhedralPLInCharts e (f ∘ g) Rect := by
    have hg' := hg
    obtain ⟨K,hK,hKs,_⟩ := hg'
    exact hKs ▸ hf.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hg)
      (fun x hx => M.subset_annulus (hgbij.1 (hKs.subset hx)))
  have hki : InjOn (f ∘ g) Rect := fun x hx y hy hxy =>
    hgbij.2.1 hx hy (hfi (M.subset_annulus (hgbij.1 hx))
      (M.subset_annulus (hgbij.1 hy)) hxy)
  let : CompactSpace Rect := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  refine ⟨hk,?_,fun x hx => M.mapsTo_exterior (hgbij.1 hx),?_⟩
  · exact (hk.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy => Subtype.ext (hki x.property y.property hxy))).isEmbedding
  · intro x hx
    exact (M.proper _ (hgbij.1 hx)).trans (hgproper x hx)

theorem FourSidedProperComplementDisk.exists_original_marked_rectangle
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {center : Set P2}
    {c : P2 → P2} {f : P2 → X}
    (M : FourSidedProperComplementDisk c f Q center)
    (hf : PolyhedralPLInCharts e f Ann) (hfi : InjOn f Ann) :
    ∃ (g : P2 → P2) (k : P2 → X),
      FinitePiecewiseAffineOn g Rect ∧ BijOn g Rect M.carrier ∧
      g '' frontier Rect = frontier M.carrier ∧ k = f ∘ g ∧
      PolyhedralPLInCharts e k Rect ∧ IsEmbedding (fun x : Rect => k x) ∧
      MapsTo k Rect Q ∧
      (∀ x ∈ Rect, k x ∈ frontier Q ↔ x ∈ frontier Rect) ∧
      k '' Rect = f '' M.carrier ∧ k '' frontier Rect = f '' frontier M.carrier ∧
      k '' (I ×ˢ {(0 : ℝ)}) = f '' (M.carrier ∩ frontier spanningOuterSquare) ∧
      k '' (I ×ˢ {(1 : ℝ)}) = f '' (M.carrier ∩ frontier spanningInnerSquare) ∧
      k '' ({(0 : ℝ)} ×ˢ I) = f '' (c '' arm (-1)) ∧
      k '' ({(1 : ℝ)} ×ˢ I) = f '' (c '' arm 1) ∧
      k (0,0) = f (c (M.outerEnd,-1)) ∧ k (1,0) = f (c (M.outerEnd,1)) ∧
      k (0,1) = f (c (M.innerEnd,-1)) ∧ k (1,1) = f (c (M.innerEnd,1)) := by
  obtain ⟨g,hg,hgi,himage,hboundary,houter,hinner,hnegative,hpositive,ha,hb,hc,hd⟩ :=
    exists_four_side_disk_map M.ball M.outer_interval M.inner_interval
      M.negative_interval M.positive_interval M.opposite_rims M.opposite_arms
      (M.outer_contacts (-1) (Or.inl rfl)) (M.outer_contacts 1 (Or.inr rfl))
      (M.inner_contacts (-1) (Or.inl rfl)) (M.inner_contacts 1 (Or.inr rfl)) M.frontier_eq
  have hgM : MapsTo g Rect M.carrier := fun x hx =>
    himage.subset (mem_image_of_mem g hx)
  have hgonto : SurjOn g Rect M.carrier := fun y hy =>
    himage.symm.subset hy
  let k := f ∘ g
  obtain ⟨hk,hkembed,hkQ,hkproper⟩ :=
    M.original_rectangle_of_parameter hf hfi hg ⟨hgM,hgi,hgonto⟩ hboundary
  have himages (s : Set P2) : k '' s = f '' (g '' s) := by
    rw [image_image]
    rfl
  refine ⟨g,k,hg,⟨hgM,hgi,hgonto⟩,hboundary,rfl,hk,hkembed,
    hkQ,hkproper,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [himages,himage]
  · rw [himages,hboundary]
  · rw [himages,houter]
  · rw [himages,hinner]
  · rw [himages,hnegative]
  · rw [himages,hpositive]
  · exact congrArg f ha
  · exact congrArg f hb
  · exact congrArg f hc
  · exact congrArg f hd

end PoincareConjecture.M76.Dehn.Annuli
