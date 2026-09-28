import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.RelativeScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.Shrink
import Mathlib.Data.Real.Pointwise

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture

section Homothety

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]

theorem Homothety.metricDiameter_univ
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (he : MetricHomothety g h e Q) :
    metricDiameter h Set.univ = Real.sqrt Q * metricDiameter g Set.univ := by
  have hdist (x y : M) :
      (h.edist (e x) (e y)).toReal = Real.sqrt Q * (g.edist x y).toReal := by
    rw [Homothety.homothety_edist g h e Q hQ he,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hrange :
      Set.range (fun p : ↥(Set.univ : Set N) × ↥(Set.univ : Set N) =>
        (h.edist p.1 p.2).toReal) =
      Set.range (fun p : ↥(Set.univ : Set M) × ↥(Set.univ : Set M) =>
        Real.sqrt Q * (g.edist p.1 p.2).toReal) := by
    ext r
    constructor
    · rintro ⟨⟨x, y⟩, rfl⟩
      refine ⟨(⟨e.symm x, Set.mem_univ _⟩, ⟨e.symm y, Set.mem_univ _⟩), ?_⟩
      simpa only [e.apply_symm_apply] using (hdist (e.symm x) (e.symm y)).symm
    · rintro ⟨⟨x, y⟩, rfl⟩
      exact ⟨(⟨e x, Set.mem_univ _⟩, ⟨e y, Set.mem_univ _⟩), hdist x y⟩
  unfold metricDiameter
  rw [hrange]
  exact (Real.mul_iSup_of_nonneg (Real.sqrt_nonneg Q) _).symm

end Homothety

section Normalization

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {p : M}

theorem AncientKappaNormalization.metricDiameter_zero
    (A : AncientKappaNormalization K p 0) :
    metricDiameter (A.target.flow.metric 0) Set.univ =
      Real.sqrt A.scale * metricDiameter (K.flow.metric 0) Set.univ := by
  unfold metricDiameter
  simp_rw [A.toReal_edist_zero]
  exact (Real.mul_iSup_of_nonneg (Real.sqrt_nonneg A.scale) _).symm

end Normalization

namespace RicciFlow

attribute [local instance] smallCarrier smallChartedSpace smallIsManifold smallT3Space

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [SecondCountableTopology M]
  {J : Set ℝ}

@[simp] theorem metricDiameter_shrink (F : RicciFlow 3 M J) (t : ℝ) :
    metricDiameter (F.shrink.metric t) Set.univ =
      metricDiameter (F.metric t) Set.univ := by
  simpa only [Real.sqrt_one, one_mul] using
    Homothety.metricDiameter_univ (F.metric t) (F.shrink.metric t)
      (Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M) 1 zero_lt_one
      (F.metricHomothety_shrink t)

end RicciFlow

end PoincareConjecture
