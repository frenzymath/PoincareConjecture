import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Semiconcavity







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]


theorem toponogov_corresponding_side
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
    ∀ s ∈ Icc 0 a, ∀ t ∈ Icc 0 b,
      (g.edist (γ s) (σ t)).toReal ^ 2 ≥ s ^ 2 + t ^ 2 -
        2 * s * t * ((a ^ 2 + b ^ 2 - (g.edist (γ a) (σ b)).toReal ^ 2) /
          (2 * a * b)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcomm (x y : M) : g.edist x y = g.edist y x := Manifold.riemannianEDist_comm
  apply corresponding_side_lower_of_squared_distance_semiconcavity ha hb
  · intro t ht
    simpa only [hcomm (σ t)] using
      g.squared_distance_sub_sq_concave D hcomplete hsec (σ t) hγ hγspeed hγmin
  · intro s hs
    exact g.squared_distance_sub_sq_concave D hcomplete hsec (γ s) hσ hσspeed hσmin
  · intro s hs
    have hzero : σ 0 = γ 0 := hσ0.trans hγ0.symm
    rw [hzero, hγmin s hs 0 ⟨le_rfl, ha.le⟩, sub_zero,
      ENNReal.toReal_ofReal (abs_nonneg _), sq_abs]
  · intro t ht
    have hzero : γ 0 = σ 0 := hγ0.trans hσ0.symm
    rw [hzero, hσmin 0 ⟨le_rfl, hb.le⟩ t ht, zero_sub,
      ENNReal.toReal_ofReal (abs_nonneg _), sq_abs]
    ring

end PoincareConjecture.RiemannianMetric
