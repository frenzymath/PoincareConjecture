import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Approximation.Cutoffs
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Integral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Positivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

theorem heatKernelContinuous_mass_le_one (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω)
    (t : ℝ) (ht : 0 < t) (x : M) :
    (∫ y in Ω, heatKernelContinuous D S t ht x y ∂g.volumeMeasure) ≤ 1 := by
  obtain ⟨φ, hφ, hφlim⟩ := exists_energyTest_cutoffs D S.isOpen S.isCompact_closure
  let K : M → ℝ := heatKernelContinuous D S t ht x
  have hK : Continuous K := continuous_heatKernelContinuous_row D S t ht x
  have hKnonneg : ∀ y : M, 0 ≤ K y := heatKernelContinuous_nonneg D S t ht x
  have hlim : Tendsto (fun j : ℕ => ∫ y in Ω, K y * φ j y ∂g.volumeMeasure)
      atTop (𝓝 (∫ y in Ω, K y ∂g.volumeMeasure)) := by
    apply tendsto_integral_of_dominated_convergence K
    · intro j
      exact (hK.mul (φ j).smooth.continuous).aestronglyMeasurable
    · exact integrable_heatKernelContinuous D S t ht x
    · intro j
      exact Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (mul_nonneg (hKnonneg y) (hφ j y).1)]
        exact mul_le_of_le_one_right (hKnonneg y) (hφ j y).2
    · filter_upwards [ae_restrict_mem S.isOpen.measurableSet] with y hy
      simpa only [mul_one] using tendsto_const_nhds.mul (hφlim y hy)
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun j => by
    rw [show (∫ y in Ω, K y * φ j y ∂g.volumeMeasure) =
        Boundary.heatPowerContinuous D S 0 t ht
          (toDomainL2 D Ω (φ j : H1Zero D Ω)) x from
      integral_heatKernelContinuous_test D S t ht x (φ j)]
    exact Boundary.heatPowerContinuous_test_le D S (φ j) 1 zero_le_one
      (fun y => (hφ j y).2) t ht x

end PoincareConjecture.LeviCivitaData.Dirichlet
