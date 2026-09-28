import PoincareConjecture.Proofs.M10.MetricCoordinates
import PoincareConjecture.Definitions.Ch06.ReducedLength

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem exists_exponential_source_normalization
    (G : LExponentialGeometry F T τmax p) (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (hreg : (metricCoordinates (F.metric T) p x, τ) ∈ G.toLExponentialFamily.regularDomain) :
    ∃ C : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ v : EuclideanSpace ℝ (Fin n),
        G.toLExponentialFamily.sliceDifferential (metricCoordinates (F.metric T) p x) τ
          (metricCoordinates (F.metric T) p (C v)) =
        metricCoordinates (F.metric (T - τ))
          (G.gamma (metricCoordinates (F.metric T) p x) τ) v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let β := (metricCoordinates (F.metric T) p).toContinuousLinearEquiv
  let q := G.gamma (β x) τ
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) q) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) q
  let D : TangentSpace (𝓡 n) p ≃L[ℝ] TangentSpace (𝓡 n) q :=
    LinearEquiv.toContinuousLinearEquiv
      (LinearEquiv.ofBijective
        (G.toLExponentialFamily.sliceDifferential (β x) τ).toLinearMap hreg.2)
  let δ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) q := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - τ)).toRiemannianMetric⟩
    exact (metricCoordinates (F.metric (T - τ)) q).toContinuousLinearEquiv
  let C := δ.trans (D.symm.trans β.symm)
  refine ⟨C, ?_⟩
  intro v
  change D (β (C v)) = δ v
  simp only [C, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]

end PoincareConjecture.M10
