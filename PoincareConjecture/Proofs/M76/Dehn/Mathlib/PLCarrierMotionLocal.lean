import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierMotionRegularity
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse










set_option autoImplicit false

open Set unitInterval

namespace Geometry.PLCarrierMotion





theorem slice_mem_piecewiseAffineGroupoid {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C P : Set E} {ε : ℝ} (H : PLCarrierMotion C P ε) (t : I) :
    (H.map t).toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E := by
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  intro x _
  obtain ⟨K, hK, hxK, _⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed
      (E := E) isCompact_singleton isOpen_univ (subset_univ {x})
  obtain ⟨L, hL, hLs, hLaff⟩ :=
    (H.finitePiecewiseAffineOn_finite_polyhedron t K hK).1
  refine ⟨L, hL, ?_, subset_univ _, hLaff⟩
  rw [hLs]
  exact hxK (mem_singleton x)

end Geometry.PLCarrierMotion
