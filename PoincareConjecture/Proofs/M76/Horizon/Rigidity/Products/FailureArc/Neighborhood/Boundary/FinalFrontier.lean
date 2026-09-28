import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CutGeometry
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskCutDomainConstruction
import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductSlices







set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1

namespace BoundaryInventory

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {j₀ j₁ : V2 → X}

theorem endDisks_eq_slice_images (P : OriginalDiskProduct e Q j₀) :
    P.endDisks = P.slice (-(1 / 2 : ℝ)) '' Disk ∪ P.slice (1 / 2 : ℝ) '' Disk := by
  rw [P.slice_image, P.slice_image]
  change P.map '' (Disk ×ˢ ({-(1 / 2 : ℝ), 1 / 2} : Set ℝ)) = _
  rw [show ({-(1 / 2 : ℝ), 1 / 2} : Set ℝ) =
    {-(1 / 2 : ℝ)} ∪ {(1 / 2 : ℝ)} by ext x; simp [or_comm]]
  rw [prod_union, image_union]

theorem successive_cut_frontier
    (P₀ : OriginalDiskProduct e Q j₀) (P₁ : OriginalDiskProduct e P₀.cutCarrier j₁)
    (hdis : Disjoint P₀.closedStrip P₁.closedStrip)
    (hfront₀ : frontier P₀.cutCarrier = (frontier Q \ P₀.openStrip) ∪ P₀.endDisks)
    (hfront₁ : frontier P₁.cutCarrier =
      (frontier P₀.cutCarrier \ P₁.openStrip) ∪ P₁.endDisks) :
    frontier P₁.cutCarrier = (frontier Q \ (P₀.openStrip ∪ P₁.openStrip)) ∪
      (P₀.slice (-(1 / 2 : ℝ)) '' Disk ∪ P₀.slice (1 / 2 : ℝ) '' Disk) ∪
      (P₁.slice (-(1 / 2 : ℝ)) '' Disk ∪ P₁.slice (1 / 2 : ℝ) '' Disk) := by
  have hend₀ : P₀.endDisks ⊆ P₀.closedStrip := by
    rw [← P₀.closedStrip_sdiff_openStrip]
    exact sdiff_subset
  have hopen₁ : P₁.openStrip ⊆ P₁.closedStrip :=
    image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
  rw [← endDisks_eq_slice_images, ← endDisks_eq_slice_images, hfront₁, hfront₀]
  ext x
  have havoid : x ∈ P₀.endDisks → x ∉ P₁.openStrip :=
    fun hx hy => Set.disjoint_left.mp hdis (hend₀ hx) (hopen₁ hy)
  simp only [mem_union, mem_sdiff]
  tauto

theorem successive_cut_cover_overlap
    (P₀ : OriginalDiskProduct e Q j₀) (P₁ : OriginalDiskProduct e P₀.cutCarrier j₁)
    (hdis : Disjoint P₀.closedStrip P₁.closedStrip)
    (hoverlap₀ : P₀.closedStrip ∩ P₀.cutCarrier = P₀.endDisks)
    (hcover₀ : P₀.closedStrip ∪ P₀.cutCarrier = Q)
    (hoverlap₁ : P₁.closedStrip ∩ P₁.cutCarrier = P₁.endDisks)
    (hcover₁ : P₁.closedStrip ∪ P₁.cutCarrier = P₀.cutCarrier) :
    (P₀.closedStrip ∪ P₁.closedStrip) ∪ P₁.cutCarrier = Q ∧
      (P₀.closedStrip ∪ P₁.closedStrip) ∩ P₁.cutCarrier =
        (P₀.slice (-(1 / 2 : ℝ)) '' Disk ∪ P₀.slice (1 / 2 : ℝ) '' Disk) ∪
        (P₁.slice (-(1 / 2 : ℝ)) '' Disk ∪ P₁.slice (1 / 2 : ℝ) '' Disk) := by
  constructor
  · rw [union_assoc, hcover₁, hcover₀]
  · rw [← endDisks_eq_slice_images, ← endDisks_eq_slice_images,
      ← hoverlap₀, ← hoverlap₁]
    ext x
    have havoid : x ∈ P₀.closedStrip → x ∉ P₁.closedStrip :=
      fun hx hy => Set.disjoint_left.mp hdis hx hy
    have hcover := Set.ext_iff.mp hcover₁ x
    simp only [mem_union, mem_inter_iff] at hcover ⊢
    tauto

end BoundaryInventory

namespace TubeExterior

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X} {j₀ j₁ : V2 → X}

theorem OriginalIntervalTube.final_frontier_inventory
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (P₀ : OriginalDiskProduct e (R \ U.map '' openTube r) j₀)
    (P₁ : OriginalDiskProduct e P₀.cutCarrier j₁)
    (hdis : Disjoint P₀.closedStrip P₁.closedStrip)
    (hfront₀ : frontier P₀.cutCarrier =
      (frontier (R \ U.map '' openTube r) \ P₀.openStrip) ∪ P₀.endDisks)
    (hfront₁ : frontier P₁.cutCarrier =
      (frontier P₀.cutCarrier \ P₁.openStrip) ∪ P₁.endDisks)
    (hoverlap₀ : P₀.closedStrip ∩ P₀.cutCarrier = P₀.endDisks)
    (hcover₀ : P₀.closedStrip ∪ P₀.cutCarrier = R \ U.map '' openTube r)
    (hoverlap₁ : P₁.closedStrip ∩ P₁.cutCarrier = P₁.endDisks)
    (hcover₁ : P₁.closedStrip ∪ P₁.cutCarrier = P₀.cutCarrier) :
    frontier P₁.cutCarrier =
        (frontier R \ (U.map '' openTube r ∪ P₀.openStrip ∪ P₁.openStrip)) ∪
        (U.map '' lateral r \ (P₀.openStrip ∪ P₁.openStrip)) ∪
        (P₀.slice (-(1 / 2 : ℝ)) '' Disk ∪ P₀.slice (1 / 2 : ℝ) '' Disk) ∪
        (P₁.slice (-(1 / 2 : ℝ)) '' Disk ∪ P₁.slice (1 / 2 : ℝ) '' Disk) ∧
      P₁.cutCarrier = R \ (U.map '' openTube r ∪ P₀.openStrip ∪ P₁.openStrip) ∧
      (U.map '' closedTube r) ∩ P₁.cutCarrier =
        U.map '' lateral r \ (P₀.openStrip ∪ P₁.openStrip) ∧
      (P₀.closedStrip ∪ P₁.closedStrip) ∩ P₁.cutCarrier =
        (P₀.slice (-(1 / 2 : ℝ)) '' Disk ∪ P₀.slice (1 / 2 : ℝ) '' Disk) ∪
        (P₁.slice (-(1 / 2 : ℝ)) '' Disk ∪ P₁.slice (1 / 2 : ℝ) '' Disk) ∧
      U.map '' closedTube r ∪ (P₀.closedStrip ∪ P₁.closedStrip) ∪ P₁.cutCarrier = R := by
  obtain ⟨hcover, hoverlap⟩ := BoundaryInventory.successive_cut_cover_overlap
    P₀ P₁ hdis hoverlap₀ hcover₀ hoverlap₁ hcover₁
  refine ⟨?_, ?_, ?_, hoverlap, ?_⟩
  · rw [BoundaryInventory.successive_cut_frontier P₀ P₁ hdis hfront₀ hfront₁,
      OriginalIntervalTube.frontier_exterior U hR he hr hr1]
    ext x
    simp only [mem_union, mem_sdiff]
    tauto
  · ext x
    simp only [OriginalDiskProduct.cutCarrier, mem_sdiff, mem_union]
    tauto
  · have h := OriginalIntervalTube.closedTube_inter_exterior U hr hr1
    ext x
    have hx := Set.ext_iff.mp h x
    simp only [OriginalDiskProduct.cutCarrier, mem_sdiff, mem_inter_iff,
      mem_union] at hx ⊢
    tauto
  · rw [union_assoc, hcover, OriginalIntervalTube.closedTube_union_exterior U hr1]

end TubeExterior
end PoincareConjecture.M76.Dehn.Annuli
