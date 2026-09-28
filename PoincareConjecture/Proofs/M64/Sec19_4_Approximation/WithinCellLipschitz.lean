import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge














set_option autoImplicit false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]




theorem m64_lipschitzOn_nhdsWithin_of_extension
    (g : RiemannianMetric n M) {f F : LoopPlane → M} {S : Set LoopPlane}
    {x : LoopPlane}
    (hF : ContMDiffAt (𝓡 2) (𝓡 n) 1 F x)
    (hEq : EqOn f F S) :
    ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, ∀ y ∈ U ∩ S, ∀ z ∈ U ∩ S,
      g.edist (f y) (f z) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖ := by
  obtain ⟨K, U, hU, hK⟩ :=
    m64_lipschitzOn_nhds_of_contMDiffAt g hF
  refine ⟨K, U, hU, ?_⟩
  intro y hy z hz
  rw [hEq hy.2, hEq hz.2]
  exact hK y hy.1 z hz.1

end PoincareConjecture
