import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.FaceData
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartFaceImage
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FreeFaceCarrierBounds

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem MarkedSurfaceMotionData.exists_active_face_bound
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V} (hK : K.faces.Finite)
    {face : Finset V} (hface : face ∈ K.faces)
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V))
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    {Q : OpenPartialHomeomorph t.Carrier E}
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid E)
    {B : OpenPartialHomeomorph s.Carrier E} {J : SimplicialComplex ℝ E}
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}
    (motion : MarkedSurfaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary) :
    ∃ L : SimplicialComplex ℝ E,
      L.faces.Finite ∧
      L.space = Q '' (j '' convexHull ℝ (face : Set V) ∩ Q.source) ∩
        motion.support.space ∧
      (∀ a ∈ L.faces, a.card ≤ face.card) ∧
      ∀ a ∈ motion.freeComplex.faces, a ∉ motion.fixedComplex.faces →
        convexHull ℝ (a : Set E) ⊆ L.space ∧ a.card ≤ face.card := by
  obtain ⟨L, hL, hLs, hbound⟩ := hj.exists_finite_face_chart_image K hK hface Q hQ
    motion.support motion.support_finite motion.support_upper
  have hcover : motion.freeComplex.space ⊆ motion.fixedComplex.space ∪ L.space := by
    intro z hz
    have hzsource : z ∈ Q '' (j '' K₁.space ∩ Q.source) ∩ motion.support.space := by
      rw [← motion.source_space, ← motion.free_space]
      exact hz
    obtain ⟨⟨y, ⟨⟨x, hx, rfl⟩, hjxQ⟩, hvalue⟩, hzsupport⟩ := hzsource
    rcases hsucc.subset hx with hxold | hxactive
    · left
      rw [motion.fixed_space, motion.protected_space]
      exact ⟨⟨j x, ⟨mem_image_of_mem j hxold, hjxQ⟩, hvalue⟩, hzsupport⟩
    · right
      rw [hLs]
      exact ⟨⟨j x, ⟨mem_image_of_mem j hxactive, hjxQ⟩, hvalue⟩, hzsupport⟩
  refine ⟨L, hL, hLs, hbound, ?_⟩
  intro a ha hnot
  have hsub := motion.freeComplex.free_face_hull_subset_closed_active
    motion.fixedComplex motion.fixed_le (L.isCompact_space_of_finite hL).isClosed
    hcover ha hnot
  exact ⟨hsub, motion.freeComplex.face_card_le_of_hull_subset_finite_carrier
    L hL ha hsub hbound⟩

end Geometry.OriginalPLTower
