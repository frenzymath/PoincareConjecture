import PoincareConjecture.Proofs.M76.Mathlib.CenteredDerivedSurface
import PoincareConjecture.Proofs.M76.Mathlib.MinimalFaceRadialTransport
import PoincareConjecture.Proofs.M76.Mathlib.SmallClosedStarNeighborhood

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_centered_original_event_body
    {ι : Type*} [Finite ι] [Nonempty ι]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (hzeroK : (0 : E) ∈ K.space) {U : Set E} (hU : IsOpen U)
    (hzeroU : (0 : E) ∈ U) (c : E ≃L[ℝ] (ι → ℝ)) :
    ∃ (M : SimplicialComplex ℝ E) (C : Set E)
      (L : (ι ⊕ ι) → E →ₗ[ℝ] ℝ) (J : SimplicialComplex ℝ E),
      M.faces.Finite ∧ M.space = K.space ∧ (0 : E) ∈ M.vertices ∧
      (∀ s ∈ M.faces, ∃ t ∈ M.faces, t.card = 3 ∧ s ⊆ t) ∧
      (∀ s ∈ M.faces, s.card = 2 →
        {t : Finset E | t ∈ M.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2) ∧
      (M.link 0).vertexAbstractComplex.edgeGraph.Connected ∧
      IsCompact C ∧ Convex ℝ C ∧ (0 : E) ∈ interior C ∧ C ⊆ U ∧
      Disjoint C (M.link 0).space ∧
      M.space ∩ C = (M.closedStar 0).space ∩ C ∧
      (∀ s ∈ K.faces, (convexHull ℝ (s : Set E) ∩ C).Nonempty →
        (0 : E) ∈ convexHull ℝ (s : Set E)) ∧
      (∀ i, L i ≠ 0) ∧ C = {x | ∀ i, L i x ≤ 1} ∧
      J.faces.Finite ∧ J.space = frontier C := by
  obtain ⟨M, hM, hMK, hzeroM, hpureM, hcofacesM, hlinkM⟩ :=
    K.exists_centered_derived_surface_at_carrier_point hK hpure hcofaces hlinks hzeroK
  obtain ⟨V, hV, hzeroV, hfaceV⟩ := K.exists_open_face_hulls_contain_point hK 0
  obtain ⟨C, L, J, hC, hconv, hzeroC, hCUV, hlinkC, hstarC, hL, hrep, hJ, hJC⟩ :=
    M.exists_small_closedStar_halfspace_neighborhood hM hzeroM
      (hU.inter hV) ⟨hzeroU, hzeroV⟩ c
  refine ⟨M, C, L, J, hM, hMK, hzeroM, hpureM, hcofacesM, hlinkM,
    hC, hconv, hzeroC, fun _ hx => (hCUV hx).1, hlinkC, hstarC, ?_,
    hL, hrep, hJ, hJC⟩
  intro s hs hmeet
  obtain ⟨x, hxs, hxC⟩ := hmeet
  exact hfaceV s hs ⟨x, hxs, (hCUV hxC).2⟩

end Geometry.SimplicialComplex
