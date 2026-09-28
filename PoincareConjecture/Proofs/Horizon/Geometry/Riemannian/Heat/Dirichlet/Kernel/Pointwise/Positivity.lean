import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.TestOrder
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.Order

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

theorem heatKernelContinuous_nonneg (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω)
    (t : ℝ) (ht : 0 < t) (x y : M) :
    0 ≤ heatKernelContinuous D S t ht x y := by
  by_cases hy : y ∈ Ω
  · have hcont : Continuous (heatKernelContinuous D S t ht x) := by
      simpa only [Function.comp_def, id_eq] using
        (continuous_heatKernelContinuous D S t ht).comp
          (continuous_const.prodMk (continuous_id : Continuous (id : M → M)))
    apply nonneg_of_integral_mul_test_nonneg (D := D) S.isOpen hcont _ y hy
    intro φ hφ
    rw [integral_heatKernelContinuous_test D S t ht x φ]
    exact Boundary.heatPowerContinuous_test_nonneg D S φ hφ t ht x
  · rw [heatKernelContinuous_zero D S t ht x y (Or.inr hy)]

end PoincareConjecture.LeviCivitaData.Dirichlet
