import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicRegularSection
import PoincareConjecture.Proofs.M76.Triangulation.RegularSliceCircles

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in

theorem hasDisjointPolygonPresentation_regular_level
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (A : E →ᵃ[ℝ] ℝ) {c : ℝ} (hreg : ∀ z ∈ K.vertices, A z ≠ c) :
    HasDisjointPolygonPresentation (K.space ∩ {x | A x = c}) := by
  classical
  let B : E →ᵃ[ℝ] ℝ := A - AffineMap.const ℝ E c
  have hBc (x : E) : B x = 0 ↔ A x = c := sub_eq_zero
  have hregB : ∀ z ∈ K.vertices, B z ≠ 0 :=
    fun z hz h => hreg z hz ((hBc z).mp h)
  obtain ⟨n, P, hP, hcover, hpair⟩ :=
    K.exists_regularSlice_polygons B hK hregB hpure hcofaces
  let : Finite (K.regularSliceGraph B).ConnectedComponent :=
    K.finite_regularSliceGraph_components B hK
  apply hasDisjointPolygonPresentation_of_family n P hP _ hpair
  simpa only [hBc] using hcover

end Geometry.SimplicialComplex
