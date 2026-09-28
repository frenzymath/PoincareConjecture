import PoincareConjecture.Proofs.M01.NormalizationMetric











set_option autoImplicit false

open Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m01RescaledMetric_tangentNorm (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (m01RescaledMetric g c hc).tangentNorm x v = Real.sqrt c * g.tangentNorm x v := by
  unfold RiemannianMetric.tangentNorm
  rw [m01RescaledMetric_inner, Real.sqrt_mul hc.le]

theorem m01_tangentEnorm_eq (g : RiemannianMetric n M) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    (letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ‖v‖ₑ) = ENNReal.ofReal (g.tangentNorm x v) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

theorem m01RescaledMetric_pathELength (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (γ : ℝ → M) (a b : ℝ) :
    (m01RescaledMetric g c hc).pathELength γ a b =
      ENNReal.ofReal (Real.sqrt c) * g.pathELength γ a b := by
  unfold RiemannianMetric.pathELength
  simp only [pathELength_eq_lintegral_mfderiv_Icc, m01_tangentEnorm_eq,
    m01RescaledMetric_tangentNorm, ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem m01RescaledMetric_edist (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x y : M) :
    (m01RescaledMetric g c hc).edist x y =
      ENNReal.ofReal (Real.sqrt c) * g.edist x y := by
  have hpos : ENNReal.ofReal (Real.sqrt c) ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne'
  unfold RiemannianMetric.edist
  simp only [riemannianEDist, m01_tangentEnorm_eq, m01RescaledMetric_tangentNorm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg c),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]

end PoincareConjecture
