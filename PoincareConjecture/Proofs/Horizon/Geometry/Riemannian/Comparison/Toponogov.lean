import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Hinge
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Triangle

noncomputable section
open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem toponogov_comparison
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {γ σ : ℝ → M} {p : M} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hγ : g.IsGeodesicOn γ (Icc 0 a)) (hσ : g.IsGeodesicOn σ (Icc 0 b))
    (hγ0 : γ 0 = p) (hσ0 : σ 0 = p)
    (hγspeed : ∀ s ∈ Icc 0 a,
      g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = 1)
    (hσspeed : ∀ t ∈ Icc 0 b,
      g.tangentNorm (σ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ t 1) = 1)
    (hγmin : ∀ s ∈ Icc 0 a, ∀ t ∈ Icc 0 a,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hσmin : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b,
      g.edist (σ s) (σ t) = ENNReal.ofReal |s - t|) :
    (g.edist (γ a) (σ b)).toReal ^ 2 ≤ a ^ 2 + b ^ 2 - 2 * a * b *
      g.inner p (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1) ∧
    ∀ s ∈ Icc 0 a, ∀ t ∈ Icc 0 b,
      (g.edist (γ s) (σ t)).toReal ^ 2 ≥ s ^ 2 + t ^ 2 -
        2 * s * t * ((a ^ 2 + b ^ 2 - (g.edist (γ a) (σ b)).toReal ^ 2) /
          (2 * a * b)) := by
  exact ⟨g.toponogov_hinge D hcomplete hsec ha hb hγ hσ hγ0 hσ0 hσspeed hγmin hσmin,
    g.toponogov_corresponding_side D hcomplete hsec ha hb hγ hσ hγ0 hσ0
      hγspeed hσspeed hγmin hσmin⟩

end PoincareConjecture.RiemannianMetric
