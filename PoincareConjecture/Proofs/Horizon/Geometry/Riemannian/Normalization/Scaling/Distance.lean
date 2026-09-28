import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Metric.Construction










set_option autoImplicit false

open Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem rescaledMetric_tangentNorm (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (rescaledMetric g c hc).tangentNorm x v = Real.sqrt c * g.tangentNorm x v := by
  unfold RiemannianMetric.tangentNorm
  rw [rescaledMetric_inner, Real.sqrt_mul hc.le]

theorem normalization_tangentEnorm_eq (g : RiemannianMetric n M) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    (letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ‖v‖ₑ) = ENNReal.ofReal (g.tangentNorm x v) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

theorem rescaledMetric_pathELength (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (γ : ℝ → M) (a b : ℝ) :
    (rescaledMetric g c hc).pathELength γ a b =
      ENNReal.ofReal (Real.sqrt c) * g.pathELength γ a b := by
  unfold RiemannianMetric.pathELength
  simp only [pathELength_eq_lintegral_mfderiv_Icc, normalization_tangentEnorm_eq,
    rescaledMetric_tangentNorm, ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem rescaledMetric_edist (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x y : M) :
    (rescaledMetric g c hc).edist x y =
      ENNReal.ofReal (Real.sqrt c) * g.edist x y := by
  have hpos : ENNReal.ofReal (Real.sqrt c) ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne'
  unfold RiemannianMetric.edist
  simp only [riemannianEDist, normalization_tangentEnorm_eq, rescaledMetric_tangentNorm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg c),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]

end PoincareConjecture
