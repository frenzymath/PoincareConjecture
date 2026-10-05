import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.OriginalProductNeighborhood
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.OriginalProductThinStrips
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.OriginalProductRescaling
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.OriginalProductLateralOpenness
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# A small original disk product with complete relative-open strips

The actual derived-neighborhood image supplies openness. Compactness
then restricts the whole closed product inside any prescribed original
open neighborhood. See Hudson1969, pp.58--63 and rigidity035.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

/-- The same original retained disk model constructs a uniformly
small product with every whole open strip relatively open, including
its entire old-frontier cylinder. See rigidity035, sections1--4. -/
theorem OriginalProperDiskTriangulation.exists_small_disk_product
    (T : OriginalProperDiskTriangulation e R j) {U : Set X}
    (hU : IsOpen U) (hDU : j '' D ⊆ U) :
    ∃ P : OriginalDiskProduct e R j, MapsTo P.map (D ×ˢ I) U ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-ε) ε))) ∧
        IsOpen ((Subtype.val : frontier R → X) ⁻¹' (P.map '' (Q ×ˢ Ioo (-ε) ε))) := by
  obtain ⟨P, W, hW, hcenter, hWimage⟩ := T.exists_disk_product_with_neighborhood
  let V : Set R := W ∩ (Subtype.val : R → X) ⁻¹' U
  have hV : IsOpen V := hW.inter (hU.preimage continuous_subtype_val)
  have hzero (z : D) :
      (⟨P.map ((z : V2), 0), P.inside ⟨z.property, by norm_num⟩⟩ : R) ∈ V := by
    have heq : (⟨P.map ((z : V2), 0), P.inside ⟨z.property, by norm_num⟩⟩ : R) =
        ⟨j z, T.disk_in_region z.property⟩ := Subtype.ext (P.central z z.property)
    rw [heq]
    exact ⟨hcenter z z.property, hDU ⟨z, z.property, rfl⟩⟩
  have hVimage : (Subtype.val : R → X) '' V ⊆ P.map '' (D ×ˢ I) :=
    (image_mono inter_subset_left).trans hWimage
  obtain ⟨δ, hδ, hδsmall, hthin, hopen⟩ := P.exists_thin_open_strips hV hzero hVimage
  obtain ⟨P', hP'⟩ := P.exists_rescaled_product hδ (by linarith)
  have hclosed : P'.map '' (D ×ˢ I) = P.map '' (D ×ˢ Icc (-δ) δ) := by
    calc
      P'.map '' (D ×ˢ I) = (P.map ∘ Prod.map id (fun t : ℝ => δ * t)) '' (D ×ˢ I) :=
        image_congr (fun x _ => hP' x)
      _ = P.map '' (D ×ˢ Icc (-δ) δ) := by
        rw [Set.image_comp, prodMap_image_prod, image_id, image_mul_left_Icc' hδ]
        simp only [mul_neg, mul_one]
  have hVinside : (Subtype.val : R → X) '' V ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy.2
  have hinside : MapsTo P'.map (D ×ˢ I) U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hclosed.subset ⟨x, hx, rfl⟩
    rw [← hxy]
    exact hVinside (hthin hy)
  refine ⟨P', hinside, ?_⟩
  intro ε hε hεsmall
  have hopen' : IsOpen ((Subtype.val : R → X) ⁻¹' (P'.map '' (D ×ˢ Ioo (-ε) ε))) := by
    have heq : P'.map '' (D ×ˢ Ioo (-ε) ε) =
        P.map '' (D ×ˢ Ioo (-(δ * ε)) (δ * ε)) := by
      calc
        P'.map '' (D ×ˢ Ioo (-ε) ε) =
            (P.map ∘ Prod.map id (fun t : ℝ => δ * t)) '' (D ×ˢ Ioo (-ε) ε) :=
          image_congr (fun x _ => hP' x)
        _ = P.map '' (D ×ˢ Ioo (-(δ * ε)) (δ * ε)) := by
          rw [Set.image_comp, prodMap_image_prod, image_id, image_mul_left_Ioo hδ, mul_neg]
    rw [heq]
    exact hopen (δ * ε) (mul_pos hδ hε) (by nlinarith)
  exact ⟨hopen', P'.isOpen_lateral_image T.isClosed_region hεsmall hopen'⟩

/-- An actual original proper PL disk has a whole small product in
its given atlas. All model and openness data are produced internally;
the complete given disk parameter is retained. See rigidity035. -/
theorem exists_small_original_disk_product
    (hR : IsCompact R) (he : PLDomain e R)
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    {U : Set X} (hU : IsOpen U) (hDU : j '' D ⊆ U) :
    ∃ P : OriginalDiskProduct e R j, MapsTo P.map (D ×ˢ I) U ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-ε) ε))) ∧
        IsOpen ((Subtype.val : frontier R → X) ⁻¹' (P.map '' (Q ×ˢ Ioo (-ε) ε))) := by
  obtain ⟨T⟩ := exists_original_proper_disk_triangulation hR he hj hemb hDR hproper
  exact T.exists_small_disk_product hU hDU

end PoincareMT.M76
