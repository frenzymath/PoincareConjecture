import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Gaussian

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture.LeviCivitaData

theorem exists_dirichletExhaustionKernel_first_moment_bound
    (m : ℕ) (κ : ℝ) (hm : 0 < m) (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M] [PreconnectedSpace M]
        (g : RiemannianMetric (m + 1) M), MetricComplete g →
        ∀ D : LeviCivitaData g,
          (∀ x (v : TangentSpace (𝓡 (m + 1)) x),
            -(m : ℝ) * κ * g.inner x v v ≤ D.ricci x v v) →
          ∀ (Ω : ℕ → Set M)
            (S : ∀ j, Poincare.Manifold.SmoothDomain (m + 1) (Ω j)),
            Monotone Ω → (⋃ j, Ω j) = univ →
            (∀ x t, 0 < t → t ≤ 1 →
              Integrable
                  (fun y => (g.edist x y).toReal *
                    dirichletExhaustionKernel
                      (fun j => Dirichlet.heatKernelContinuousTime D (S j)) t x y)
                  g.volumeMeasure ∧
                (∫ y, (g.edist x y).toReal *
                    dirichletExhaustionKernel
                      (fun j => Dirichlet.heatKernelContinuousTime D (S j)) t x y
                    ∂g.volumeMeasure) ≤ C) ∧
            Tendsto
              (fun t => ⨆ x,
                ∫ y, (g.edist x y).toReal *
                  dirichletExhaustionKernel
                    (fun j => Dirichlet.heatKernelContinuousTime D (S j)) t x y
                  ∂g.volumeMeasure)
              (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨A, hA, hgauss⟩ :=
    exists_dirichletExhaustionKernel_gaussian_bound m κ hm hκ
  obtain ⟨C, hC, hmoment⟩ :=
    PoincareConjecture.RiemannianMetric.exists_first_moment_bound_of_ricci_gaussian
      (m + 1) κ A 192 (by omega) hκ hA (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ g hc D hRic Ω S hΩmono hcover
  let K := fun j => Dirichlet.heatKernelContinuousTime D (S j)
  let H := dirichletExhaustionKernel K
  have hK : ∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j) :=
    fun j => Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S j)
  have hbdd : ∀ t, 0 < t → ∀ x y,
      BddAbove (range (fun j => K j t x y)) := by
    intro t ht x y
    exact D.bddAbove_heatKernelContinuousTime_exhaustion (by omega) hc
      (k := (m : ℝ) * κ) (by positivity)
      (fun z v => by simpa [mul_assoc] using hRic z v) S hΩmono hcover ht x y
  have hmeas : ∀ t, 0 < t →
      Measurable (fun p : M × M => H t p.1 p.2) := by
    intro t ht
    let : SecondCountableTopology M := g.secondCountableTopology
    exact measurable_dirichletExhaustionKernel hK hbdd ht
  have hnonneg : ∀ t, 0 < t → ∀ x y, 0 ≤ H t x y := by
    intro t ht x y
    exact DirichletExhaustion.nonneg hK hbdd ht x y
  have hH : ∀ t, 0 < t → t ≤ 1 → ∀ x,
      Measurable (fun y => H t x y) ∧ (∀ y, 0 ≤ H t x y) ∧
        (∀ y, H t x y ≤ A / g.volumeMeasure.real (g.ball x (Real.sqrt t)) *
          Real.exp (-(g.edist x y).toReal ^ 2 / (192 * t))) := by
    intro t ht ht1 x
    refine ⟨?_, hnonneg t ht x, ?_⟩
    · change Measurable ((fun p : M × M => H t p.1 p.2) ∘ fun y => (x, y))
      exact (hmeas t ht).comp measurable_prodMk_left
    · intro y
      exact hgauss M g hc D hRic Ω S hΩmono hcover t ht ht1 x y
  have hRic' : ∀ z (v : TangentSpace (𝓡 (m + 1)) z),
      -((((m + 1 : ℕ) : ℝ) - 1) * κ) * g.inner z v v ≤ D.ricci z v v := by
    intro z v
    simpa [Nat.cast_add] using hRic z v
  exact hmoment M g hc D hRic' (fun x y t => H t x y) hH

end PoincareConjecture.LeviCivitaData
