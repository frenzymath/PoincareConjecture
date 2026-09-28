import PoincareConjecture.Proofs.M76.Wall.Mathlib.PairedFacetOrientation
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid

set_option autoImplicit false

open Set

namespace Geometry

theorem exists_finite_paired_facet_orientation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : OpenPartialHomeomorph E E) (hh : h ∈ piecewiseAffineGroupoid E)
    {x : E} (hx : x ∈ h.source) :
    ∃ K : SimplicialComplex ℝ E,
      K.faces.Finite ∧ x ∈ interior K.space ∧ K.space ⊆ h.source ∧
      K.AffineOnFaces h ∧ InjOn h K.space ∧
      ∀ (s t u : Finset E), s ∈ K.faces → t ∈ K.faces → u ∈ K.faces →
        s.card = Module.finrank ℝ E → t.card = Module.finrank ℝ E + 1 →
        u.card = Module.finrank ℝ E + 1 → s ⊆ t → s ⊆ u → t ≠ u →
        ∀ A B : E →ᴬ[ℝ] E,
          EqOn h A (convexHull ℝ (t : Set E)) →
          EqOn h B (convexHull ℝ (u : Set E)) →
          LinearMap.det A.toAffineMap.linear ≠ 0 ∧
            LinearMap.det B.toAffineMap.linear ≠ 0 ∧
            0 < LinearMap.det A.toAffineMap.linear *
              LinearMap.det B.toAffineMap.linear := by
  obtain ⟨K, hK, hxK, hsource, hformula⟩ :=
    ((mem_piecewiseAffineGroupoid_iff E h).mp hh).1 x hx
  have hinj : InjOn h K.space := h.injOn.mono hsource
  refine ⟨K, hK, hxK, hsource, hformula, hinj, ?_⟩
  intro s t u hs ht hu hsc htc huc hst hsu htu A B hA hB
  exact hformula.det_mul_pos_of_paired_facet hinj
    hs ht hu hsc htc huc hst hsu htu A B hA hB

end Geometry
