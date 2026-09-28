import PoincareConjecture.Definitions.Ch06.ReducedLength

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax τ : ℝ} {p q : M}

theorem regular_upperBarrier_exists (r : ReducedLengthRegularPoint F T τmax p q τ) :
    ∃ B : ReducedLengthUpperBarrier F T p q τ,
      B.representative = r.representative ∧ B.neighborhood = r.neighborhood := by
  refine ⟨{
    neighborhood := r.neighborhood
    neighborhood_open := r.neighborhood_open
    center_mem := r.center_mem
    representative := r.representative
    touches := r.representative_eq (q, τ) r.center_mem
    dominates := fun z hz ↦ (r.representative_eq z hz).symm.le
    representative_spacetime_smooth := r.representative_spacetime_smooth
    representative_space_smooth_on := r.representative_space_smooth_on
    representative_space_smooth := r.representative_space_smooth
    representative_time_derivative := r.representative_time_derivative }, rfl, rfl⟩

end PoincareConjecture.Proofs.M09
