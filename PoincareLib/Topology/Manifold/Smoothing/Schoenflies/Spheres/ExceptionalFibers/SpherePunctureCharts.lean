import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Actual full three-dimensional charts at every puncture

Use Mathlib's stereographic projection on the actual standard sphere,
then change its Euclidean coordinates to the frozen supremum-norm
three-space. Transport through the displayed sphere homeomorphism.
See Brown1960 Theorem4 and Brown derivation017, section2.
-/

set_option autoImplicit false

open Set Metric

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X]

/-- An actual homeomorphism to the standard three-sphere produces
the entire punctured chart with target the frozen three-space.
See Brown derivation017, section2, and Mathlib stereographic'. -/
theorem exists_punctured_three_space_chart
    (e : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (p : X) :
    ∃ C : OpenPartialHomeomorph X (Fin 3 → ℝ),
      C.source = {p}ᶜ ∧ C.target = univ := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  obtain ⟨L⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) (F := Fin 3 → ℝ) (by simp)
  let S := stereographic' 3 (e p)
  let C := e.transOpenPartialHomeomorph (S.transHomeomorph L.toHomeomorph)
  refine ⟨C, ?_, ?_⟩
  · change e ⁻¹' S.source = {p}ᶜ
    rw [stereographic'_source]
    ext x
    change (e x ≠ e p) ↔ x ≠ p
    exact not_congr e.injective.eq_iff
  · change L.toHomeomorph.symm ⁻¹' S.target = univ
    rw [stereographic'_target, preimage_univ]

end Homeomorph
