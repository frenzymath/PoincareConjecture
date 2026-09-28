import PoincareConjecture.Proofs.M14.Sec6_2_SquareEulerInterior
import PoincareConjecture.Proofs.M14.Sec6_2_EulerContinuity
import PoincareConjecture.Proofs.M14.Mathlib.SectionThroughVector











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}




theorem squareRootEulerResidual_eq_zero_of_minimizing
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hmin : M14IsMinimizing p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity) {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (W : G.Horizontal (R.curve s)) : M14SquareRootEulerResidual G R E s W = 0 := by
  obtain ⟨Z, hZ, hZs⟩ := FiberBundle.exists_contMDiff_section_through
    (I := spacetimeModel n) (F := EuclideanSpace ℝ (Fin n)) W
  have hcont := squareRootEulerResidual_stationary_continuousOn hM12 E Z hZ
  have hzero : EqOn (fun r => M14SquareRootEulerResidual G R E r (Z (R.curve r)))
      (fun _ => 0) (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) := by
    intro r hr
    exact squareRootEulerResidual_eq_zero_of_minimizing_interior hCoordinates hM12 hmin E hr _
  have hclosed := hzero.of_subset_closure hcont continuousOn_const Ioo_subset_Icc_self
    (show M14SqrtParameterInterval τ₁ τ₂ ⊆ closure (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) by
      rw [closure_Ioo (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt).ne]
      exact Subset.rfl)
  simpa only [hZs] using hclosed hs




theorem squareRootEulerStatement (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) : M14SquareRootEulerStatement G := by
  intro T τ₁ τ₂ x y p R hmin
  obtain ⟨E⟩ := exists_squareRoot_velocity_extension R
  exact ⟨E, fun _ hs W =>
    squareRootEulerResidual_eq_zero_of_minimizing hCoordinates hM12 hmin E hs W⟩

end PoincareConjecture.M14
