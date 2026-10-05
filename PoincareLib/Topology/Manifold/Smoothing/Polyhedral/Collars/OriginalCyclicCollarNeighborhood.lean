import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.OriginalLateralBoxInterior
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonInteriorCutArcs
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.CompactZeroFiberBand

/-!
# The actual cyclic collar contains the complete surface band

Every point of the unchanged polygon core is interior to the
literal cyclic box union. Compactness of the full surface
then supplies a whole closed height band inside this collar.
See Alexander 1924, pp. 6--8, Hudson 1969, pp. 12--19,
60--61 and M76 derivation 286av.
-/

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

/-- The whole original polygon core lies in the ambient
interior of the actual cyclic box union. Strict core points
use PL openness; original endpoints use their exact adjacent
two-box union. See Alexander pp. 6--8 and derivation 286av. -/
theorem boundary_subset_interior_original_cyclic_boxes
    (P : Polygon E (n + 3)) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1)
    (F : Fin (n + 3) → ((ℝ × ℝ) × ℝ) → E)
    (f : Fin (n + 3) → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    {r : ℝ} (hr : 0 < r)
    (hF : ∀ i, FinitePiecewiseAffineOn (F i) (box r))
    (hinj : ∀ i, InjOn (F i) (box r))
    (hcore : ∀ i, F i '' (({0} ×ˢ Icc (-r) r) ×ˢ {0}) = P.cutArc t i)
    (hlateral : ∀ i (j : Bool) u z, u ∈ Icc (-r) r → z ∈ Icc (-r) r →
      F i ((u, if j then r else -r), z) =
        f (if j then finRotate (n + 3) i else i) ((u, 0), z))
    (hcontact : ∀ i, (F i '' box r) ∩ (F (finRotate (n + 3) i) '' box r) =
      f (finRotate (n + 3) i) '' ((Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r)) :
    P.boundary ℝ ⊆ interior (⋃ i, F i '' box r) := by
  have hzero : (0 : ℝ) ∈ Icc (-r) r := ⟨neg_nonpos.mpr hr.le, hr.le⟩
  have hshared (i : Fin (n + 3)) :
      f (finRotate (n + 3) i) 0 ∈ interior (⋃ j, F j '' box r) := by
    apply interior_mono (union_subset (subset_iUnion _ i)
      (subset_iUnion _ (finRotate (n + 3) i)))
    exact original_cut_mem_interior_box_union (F i) (F (finRotate (n + 3) i))
      (f (finRotate (n + 3) i)) hr (hF i) (hF (finRotate (n + 3) i))
      (hinj i) (hinj (finRotate (n + 3) i)) (hlateral i true)
      (hlateral (finRotate (n + 3) i) false) (hcontact i)
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp ((P.iUnion_cutArc t ht).symm.subset hy)
  rw [← hcore i] at hi
  obtain ⟨⟨⟨u, s⟩, z⟩, ⟨⟨hu, hs⟩, hz⟩, rfl⟩ := hi
  have hu0 : u = 0 := hu
  have hz0 : z = 0 := hz
  subst u
  subst z
  by_cases hneg : s = -r
  · subst s
    have hendpoint : F i ((0, -r), 0) = f i 0 := hlateral i false 0 0 hzero hzero
    rw [hendpoint]
    simpa only [Equiv.apply_symm_apply] using hshared ((finRotate (n + 3)).symm i)
  by_cases hpos : s = r
  · subst s
    have hendpoint : F i ((0, r), 0) = f (finRotate (n + 3) i) 0 :=
      hlateral i true 0 0 hzero hzero
    rw [hendpoint]
    exact hshared i
  have hsource : ((0, s), 0) ∈ interior (box r) := by
    simp only [box, base, interior_prod_eq, interior_Icc, mem_prod, mem_Ioo]
    exact ⟨⟨⟨by linarith, hr⟩, lt_of_le_of_ne hs.1 (Ne.symm hneg),
      lt_of_le_of_ne hs.2 hpos⟩, by linarith, hr⟩
  exact interior_mono (subset_iUnion _ i)
    ((hF i).mem_interior_image (f i).linear.finrank_eq (hinj i) hsource)

omit [FiniteDimensional ℝ E] in
/-- A compact surface whose complete numerical height
section is the original polygon has a whole positive closed
band inside any actual open neighborhood of that polygon.
The width can be arbitrarily small. See derivation 286av. -/
theorem exists_surface_band_subset_original_neighborhood
    (P : Polygon E (n + 3)) {S U : Set E} (hS : IsCompact S) (hU : IsOpen U)
    (hPU : P.boundary ℝ ⊆ U) (A : E → ℝ) (c : ℝ)
    (hA : ContinuousOn A S) (hsection : S ∩ {x | A x = c} = P.boundary ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, δ ∈ Ioo 0 ε ∧ S ∩ {x | |A x - c| ≤ δ} ⊆ U := by
  have hzero : S ∩ {x | A x - c = 0} ⊆ U := by
    intro x hx
    apply hPU
    rw [← hsection]
    exact ⟨hx.1, sub_eq_zero.mp hx.2⟩
  obtain ⟨ρ, hρ, hband⟩ := hS.exists_pos_abs_le_subset_of_zero_fiber
    hU (hA.sub continuousOn_const) hzero
  let δ := min ρ ε / 2
  have hδ : 0 < δ := half_pos (lt_min hρ hε)
  have hδρ : δ ≤ ρ := (half_le_self (le_of_lt (lt_min hρ hε))).trans (min_le_left _ _)
  have hδε : δ < ε := (half_lt_self (lt_min hρ hε)).trans_le (min_le_right _ _)
  exact ⟨δ, ⟨hδ, hδε⟩, fun x hx => hband x hx.1 (hx.2.trans hδρ)⟩

end Polygon
