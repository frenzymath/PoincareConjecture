import PoincareConjecture.Proofs.M76.Mathlib.SupportedPLGraphCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLTransport
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffine
import Mathlib.Topology.Algebra.Indicator

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_locallyPL_supported_graph_extension {Q U : Set E}
    (hQ : IsCompact Q) (hU : IsOpen U) (hQU : Q ⊆ U) :
    ∃ (g : E → ℝ × E) (K : SimplicialComplex ℝ E),
      K.faces.Finite ∧ K.space ⊆ U ∧ FinitePiecewiseAffineOn g K.space ∧
      EqOn g (fun x => (1, x)) Q ∧ (∀ x, x ∉ K.space → g x = 0) ∧
      Continuous g ∧ LocallyPiecewiseAffineOn g univ ∧
      (∀ x, 0 ≤ (g x).1 ∧ (g x).1 ≤ 1) ∧
      (∀ x, (g x).1 = 1 → (g x).2 = x) := by
  classical
  obtain ⟨J, hJ, hQJ, hJU⟩ := exists_finite_neighborhood_subset_normed hQ hU hQU
  obtain ⟨K, hK, hJK, hKU⟩ := exists_finite_neighborhood_subset_normed
    (J.isCompact_space_of_finite hJ) hU hJU
  obtain ⟨g, hg, heq, hzero, hoff, hbound, hrecover⟩ :=
    exists_supported_graph_extension J K hJ hK
      (hJK.trans interior_subset) isOpen_interior hJK
  have hclosed : IsClosed K.space := (K.isCompact_space_of_finite hK).isClosed
  have hcont : Continuous g := by
    have hind : Continuous (K.space.indicator g) := continuous_indicator
      (fun x hx => hzero x hx.2) (by
        rw [hclosed.closure_eq]
        exact hg.continuousOn)
    apply hind.congr
    intro x
    by_cases hx : x ∈ K.space
    · exact indicator_of_mem hx g
    · exact (indicator_of_notMem hx g).trans (hoff x hx).symm
  refine ⟨g, K, hK, hKU, hg, heq.mono (hQJ.trans interior_subset),
    hoff, hcont, ?_, hbound, hrecover⟩
  intro x _
  obtain ⟨L, hL, hxL, _⟩ := exists_finite_neighborhood_subset_normed
    (isCompact_singleton (x := x)) isOpen_univ (subset_univ _)
  obtain ⟨R, hR, hRL, hgR⟩ := hg.on_finite_polyhedron_of_eq_affine_off hcont
    (ContinuousAffineMap.const ℝ E (0 : ℝ × E)) hoff L hL
  refine ⟨R, hR, ?_, subset_univ _, hgR⟩
  rw [hRL]
  exact hxL (mem_singleton x)

end Geometry.SimplicialComplex
