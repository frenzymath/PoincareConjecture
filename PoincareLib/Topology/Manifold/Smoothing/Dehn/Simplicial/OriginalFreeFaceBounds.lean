import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.OriginalFaceMotionData
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.FiniteChartFaceImage
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.FreeFaceCarrierBounds

/-!
# Bound every produced free face by the original active source face

Construct the exact finite clipped image of the actual active face.
The recorded successor is the whole prefix union that face, so every
produced free face lies in this closed image. Its cardinality is bounded
by the original source face using the finite affine cover theorem.
The actual produced faces and their position alternatives are unchanged.
See Hudson1969, Lemma4.6, and Dehn032, section6.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

/-- The actual motion data and original current disk construct a
finite active image containing every whole free face. Each such face
has at most the original active face's number of vertices, without
changing the produced subdivision or its position alternatives.
See Dehn032, section6. -/
theorem FaceMotionData.exists_active_face_bound
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V2} (hK : K.faces.Finite)
    {face : Finset V2} (hface : face ∈ K.faces)
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V2))
    {j : V2 → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    {Q : OpenPartialHomeomorph t.Carrier V3}
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}
    (motion : FaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary) :
    ∃ L : SimplicialComplex ℝ V3,
      L.faces.Finite ∧
      L.space = Q '' (j '' convexHull ℝ (face : Set V2) ∩ Q.source) ∩
        motion.support.space ∧
      (∀ a ∈ L.faces, a.card ≤ face.card) ∧
      ∀ a ∈ motion.freeComplex.faces, a ∉ motion.fixedComplex.faces →
        convexHull ℝ (a : Set V3) ⊆ L.space ∧ a.card ≤ face.card := by
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
