import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Exact edge contacts in the common planar face coordinates

The supporting-axis equation transfers the finite original frontier
contacts. Injectivity on the original face transfers the selected
two-contact interval without a planar contact-set supplier.
-/

set_option autoImplicit false
open Set

namespace PoincareMT.M76

local notation "V" => (ℝ × ℝ)
local notation "Z" => (Prod.snd : V → ℝ) ⁻¹' ({0} : Set ℝ)

/-- The full projected graph meets the supporting axis in exactly the
projection of its original base contacts, which are finite whenever
its original frontier contacts are finite. -/
theorem projected_face_axis_contacts
    {E : Type*} {G triangle base boundary : Set E}
    (R : E → V) (hG : G ⊆ triangle)
    (haxis : ∀ x ∈ triangle, (R x).2 = 0 ↔ x ∈ base)
    (hbase : base ⊆ boundary) (hfinite : (G ∩ boundary).Finite) :
    (R '' G) ∩ Z = R '' (G ∩ base) ∧ ((R '' G) ∩ Z).Finite := by
  have heq : (R '' G) ∩ Z = R '' (G ∩ base) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, (haxis x (hG hx)).mp hy⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxbase⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, (haxis x (hG hx)).mpr hxbase⟩
  refine ⟨heq, ?_⟩
  rw [heq]
  exact (hfinite.subset (inter_subset_inter_right G hbase)).image R

/-- The original contact identity transfers through the affine face
projection. Injectivity is needed only on that face. -/
theorem projected_face_segment_contacts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {triangle G : Set E} (htriangle : Convex ℝ triangle) (hG : G ⊆ triangle)
    (R : E →ᴬ[ℝ] V) (hR : InjOn R triangle)
    {u v : E} (hu : u ∈ triangle) (hv : v ∈ triangle)
    (hcontact : segment ℝ u v ∩ G = {u, v}) :
    segment ℝ (R u) (R v) ∩ (R '' G) = {R u, R v} := by
  have heq : segment ℝ (R u) (R v) ∩ (R '' G) = R '' (segment ℝ u v ∩ G) := by
    have himage : R '' segment ℝ u v = segment ℝ (R u) (R v) :=
      image_segment ℝ R.toAffineMap u v
    rw [← himage]
    ext y
    constructor
    · rintro ⟨⟨x, hx, hxy⟩, z, hz, hzy⟩
      have hxz : x = z := hR (htriangle.segment_subset hu hv hx) (hG hz)
        (hxy.trans hzy.symm)
      exact ⟨x, ⟨hx, hxz.symm ▸ hz⟩, hxy⟩
    · rintro ⟨x, ⟨hx, hxG⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, x, hxG, rfl⟩
  rw [heq, hcontact, image_pair]

end PoincareMT.M76
