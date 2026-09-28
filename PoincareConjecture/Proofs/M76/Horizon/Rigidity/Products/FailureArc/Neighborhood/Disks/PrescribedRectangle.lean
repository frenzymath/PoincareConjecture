import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.BoundaryParts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.PrescribedArmParameter



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)
local notation "Ann" => squareAnnulus 8 1

theorem FourSidedProperComplementDisk.endpoint_values_of_outer_start
    {X : Type*} [TopologicalSpace X] {Q : Set X} {center : Set P2}
    {c : P2 → P2} {f : P2 → X}
    (M : FourSidedProperComplementDisk c f Q center)
    (hstart : depth 8 (c (0,0)) = -1) : M.outerEnd = 0 ∧ M.innerEnd = 1 := by
  have h0 : M.outerEnd = 0 :=
    ((M.outer_preimage (0,0) (by constructor <;> norm_num)).mp
      ((spanning_outer_frontier _).mpr hstart)).symm
  refine ⟨h0,?_⟩
  rcases M.endpoint_order with h|h
  · exact h.2
  · linarith [h.1]

theorem FourSidedProperComplementDisk.exists_prescribed_original_rectangle
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R Q : Set X} {center : Set P2}
    {c : P2 → P2} {f : P2 → X} {τ : C3 → X}
    (M : FourSidedProperComplementDisk c f Q center)
    (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hf : PolyhedralPLInCharts e f Ann) (hfi : InjOn f Ann)
    (hfproper : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (j : Bool) (hτ : InjOn τ tube)
    (hpre : Ann ∩ f ⁻¹' (τ '' tube) = c '' source)
    (hsheet : ∀ p ∈ source, f (c p) = τ (originalStripSheet j p)) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k Rect ∧
      IsEmbedding (fun x : Rect => k x) ∧ MapsTo k Rect Q ∧
      (∀ x ∈ Rect, k x ∈ frontier Q ↔ x ∈ frontier Rect) ∧
      k '' Rect = f '' M.carrier ∧ k '' frontier Rect = f '' frontier M.carrier ∧
      k '' (I ×ˢ {(0 : ℝ)}) = f '' (M.carrier ∩ frontier spanningOuterSquare) ∧
      k '' (I ×ˢ {(1 : ℝ)}) = f '' (M.carrier ∩ frontier spanningInnerSquare) ∧
      k '' ({(0 : ℝ)} ×ˢ I) = f '' (c '' arm (-1)) ∧
      k '' ({(1 : ℝ)} ×ˢ I) = f '' (c '' arm 1) ∧
      (∀ p ∈ Rect,
        (k p ∈ frontier R ↔ p.2 = 0 ∨ p.2 = 1) ∧
        (k p ∈ τ '' TubeExterior.lateral 1 ↔ p.1 = 0 ∨ p.1 = 1)) ∧
      (∀ t ∈ I, k (0,t) = τ (originalStripSheet j
        ((1-t)*M.outerEnd+t*M.innerEnd,-1))) ∧
      (∀ t ∈ I, k (1,t) = τ (originalStripSheet j
        ((1-t)*M.outerEnd+t*M.innerEnd,1))) := by
  obtain ⟨g,hg,hgi,himage,hboundary,houter,hinner,hnegative,hpositive,hleft,hright,_⟩ :=
    M.exists_prescribed_arm_map hc hci
  have hgbij : BijOn g Rect M.carrier :=
    ⟨fun x hx => himage.subset (mem_image_of_mem g hx),hgi,fun _ hx => himage.symm.subset hx⟩
  obtain ⟨hk,hkembed,hkQ,hkproper⟩ :=
    M.original_rectangle_of_parameter hf hfi hg hgbij hboundary
  have hparts := strip_rectangle_boundary_parts M j hτ hpre hsheet hfproper hgbij
    houter hinner hnegative hpositive
  have htime (t : ℝ) (ht : t ∈ I) : (1-t)*M.outerEnd+t*M.innerEnd ∈ I := by
    rcases M.endpoint_order with h|h
    · simpa only [h.1,h.2,mul_zero,mul_one,zero_add] using ht
    · simp only [h.1,h.2,mul_zero,mul_one,add_zero,mem_Icc] at *
      constructor <;> linarith [ht.1,ht.2]
  refine ⟨f ∘ g,hk,hkembed,hkQ,hkproper,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [image_comp,himage]
  · rw [image_comp,hboundary]
  · rw [image_comp,houter]
  · rw [image_comp,hinner]
  · rw [image_comp,hnegative]
  · rw [image_comp,hpositive]
  · exact fun p hp => ⟨(hparts p hp).1,(hparts p hp).2.1⟩
  · intro t ht
    change f (g (0,t)) = _
    rw [hleft t ht]
    exact hsheet _ ⟨htime t ht,by norm_num⟩
  · intro t ht
    change f (g (1,t)) = _
    rw [hright t ht]
    exact hsheet _ ⟨htime t ht,by norm_num⟩

end PoincareConjecture.M76.Dehn.Annuli
