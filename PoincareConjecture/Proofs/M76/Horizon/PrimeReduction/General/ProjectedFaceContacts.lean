import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.ContinuousAffineMap









set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "V" => (ℝ × ℝ)
local notation "Z" => (Prod.snd : V → ℝ) ⁻¹' ({0} : Set ℝ)




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

end PoincareConjecture.M76
