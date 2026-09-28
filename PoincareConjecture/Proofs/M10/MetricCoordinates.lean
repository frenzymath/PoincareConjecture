import PoincareConjecture.Definitions.Ch01.Curvature

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

noncomputable def metricCoordinates (g : RiemannianMetric n M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] TangentSpace (𝓡 n) p := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  exact ((g.orthonormalBasis p).reindex (finCongr hdim)).repr.symm

set_option backward.isDefEq.respectTransparency false in

theorem metricCoordinates_tangentNorm (g : RiemannianMetric n M) (p : M)
    (v : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm p (metricCoordinates g p v) = ‖v‖ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm : ‖metricCoordinates g p v‖ = g.tangentNorm p (metricCoordinates g p v) :=
    norm_eq_sqrt_real_inner _
  exact hnorm.symm.trans ((metricCoordinates g p).norm_map v)

end PoincareConjecture.M10
