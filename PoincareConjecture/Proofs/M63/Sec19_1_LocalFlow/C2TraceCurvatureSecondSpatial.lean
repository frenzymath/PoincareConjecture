import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.EmbeddedCurvatureJetSpatial










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι




theorem embeddedCurvature_second_spatial_derivative_bound
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    {E1 E2 E3 : ℝ} (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (hE3 : 0 ≤ E3)
    (hde : ∀ V : TangentSpace (𝓡 n) (c x t),
      Norm.norm (E := W) (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) V) ≤
        E1 * (F.metric t).tangentNorm (c x t) V)
    (hE : ∀ V Z : TangentSpace (𝓡 n) (c x t),
      ‖coordinateHessian (F.connection t) e (c x t) V Z‖ ≤
        E2 * (F.metric t).tangentNorm (c x t) V * (F.metric t).tangentNorm (c x t) Z)
    (hT : ∀ V Y Z : TangentSpace (𝓡 n) (c x t),
      ‖WithLp.toLp 2 (fun k : ι => (F.connection t).covariantTensorDerivative
          (fun q w => (F.connection t).hessian (fun z => e z k) q (w 0) (w 1))
          (c x t) ![V, Y, Z])‖ ≤
        E3 * (F.metric t).tangentNorm (c x t) V * (F.metric t).tangentNorm (c x t) Y *
          (F.metric t).tangentNorm (c x t) Z) :
    let eta : ℝ → W := fun y =>
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y t) (m62CurvatureVector F c t y)
    let v := curveSpeed F c t x
    let k := m62Curvature F c t x
    let h1 := (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x)
    let h2 := (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 2 t x)
    ‖deriv (deriv eta) x‖ ≤
      |deriv (curveSpeed F c t) x| * (E2 * k + E1 * h1) +
        v ^ 2 * (E3 * k + E2 * k ^ 2 + 2 * E2 * h1 + E1 * h2) := by
  have hb := embeddedCurvatureJet_second_spatial_derivative_bound F c hc he 0 ht x
    hE1 hE2 hE3 hde hE hT
  dsimp only at hb ⊢
  simpa only [m63CurvatureJet, m62Curvature, RiemannianMetric.tangentNorm,
    m62CurvatureSquared, pow_two, mul_assoc] using hb

end PoincareConjecture.M63
