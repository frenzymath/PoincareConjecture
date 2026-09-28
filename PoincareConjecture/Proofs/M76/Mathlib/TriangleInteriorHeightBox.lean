import PoincareConjecture.Proofs.M76.Mathlib.MaximalFaceAffineGerm
import PoincareConjecture.Proofs.M76.Mathlib.HeightPlaneAffineCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension

set_option autoImplicit false

open Set CoordinateHalfBoxes

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_triangle_interior_affine_height_box
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (hdim : Module.finrank ℝ E = 3)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices)
    {p : E} (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    {W : Set E} (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (r : ℝ),
      0 < r ∧ f 0 = p ∧ f '' box r ⊆ W ∧
      p ∈ interior (f '' box r) ∧
      (∀ x, A (f x) = A p + x.1.1) ∧
      ∀ x ∈ box r, f x ∈ K.space ↔ x.2 = 0 := by
  classical
  let P := affineSpan ℝ (s : Set E)
  have hPdim : Module.finrank ℝ P.direction = 2 := K.finrank_faceDirection_of_card hs hcard
  have hpP : p ∈ P := convexHull_subset_affineSpan _ (intrinsicInterior_subset hp)
  have hAP : ∃ u ∈ P, ∃ v ∈ P, A u ≠ A v := by
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < s.card by omega)
    have huK : u ∈ K.vertices := K.down_closed hs
      (Finset.singleton_subset_iff.mpr hu) (Finset.singleton_nonempty u)
    have hvK : v ∈ K.vertices := K.down_closed hs
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    exact ⟨u, mem_affineSpan ℝ hu, v, mem_affineSpan ℝ hv,
      fun h => huv (hA huK hvK h)⟩
  obtain ⟨f, hf0, hfA, hfP⟩ :=
    P.exists_centered_height_plane_coordinates hdim hPdim A hAP hpP
  obtain ⟨U, hU, hpU, hKU⟩ :=
    K.exists_open_eq_affineSpan_of_triangle_interior hK hbound hs hcard hp
  have hpre : IsOpen (f ⁻¹' (U ∩ W)) := (hU.inter hW).preimage f.continuous
  have hzero : (0 : (ℝ × ℝ) × ℝ) ∈ f ⁻¹' (U ∩ W) := by
    change f 0 ∈ U ∩ W
    rw [hf0]
    exact ⟨hpU, hpW⟩
  obtain ⟨r, hr, hrbox⟩ := exists_box_subset hpre hzero
  have hpbox : p ∈ interior (f '' box r) := by
    change p ∈ interior (f.toHomeomorph '' box r)
    rw [← f.toHomeomorph.image_interior]
    exact ⟨0, zero_mem_interior_box hr, hf0⟩
  refine ⟨f, r, hr, hf0, ?_, hpbox, hfA, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hrbox hx).2
  · intro x hx
    have hxU := (hrbox hx).1
    have hlocal : f x ∈ K.space ↔ f x ∈ P :=
      ⟨fun h => (hKU.subset ⟨h, hxU⟩).1,
        fun h => (hKU.symm.subset ⟨h, hxU⟩).1⟩
    exact hlocal.trans (hfP x)

end Geometry.SimplicialComplex
