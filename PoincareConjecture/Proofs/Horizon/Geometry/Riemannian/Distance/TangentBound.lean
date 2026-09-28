import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {m n : ℕ} {M N : Type*}
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 m) ∞ M] [IsManifold (𝓡 n) ∞ N]

theorem edist_le_mul_of_tangentNorm_mfderiv_le
    (g : RiemannianMetric m M) (h : RiemannianMetric n N)
    {F : M → N} (hF : ContMDiff (𝓡 m) (𝓡 n) 1 F)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x v, h.tangentNorm (F x) (mfderiv (𝓡 m) (𝓡 n) F x v) ≤
      C * g.tangentNorm x v) (x y : M) :
    h.edist (F x) (F y) ≤ ENNReal.ofReal C * g.edist x y := by
  let : RiemannianBundle (TangentSpace (𝓡 m) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) := ⟨h.toRiemannianMetric⟩
  change riemannianEDist (𝓡 n) (F x) (F y) ≤
    ENNReal.ofReal C * riemannianEDist (𝓡 m) x y
  simp only [riemannianEDist, ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hC).ne'
    ENNReal.ofReal_ne_top, le_iInf_iff]
  intro γ hγ
  let η : Path (F x) (F y) := γ.map hF.continuous
  have hη : ContMDiff (𝓡∂ 1) (𝓡 n) 1 η := hF.comp hγ
  refine (biInf_le _ hη).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro t
  change ‖mfderiv (𝓡∂ 1) (𝓡 n) (F ∘ γ) t 1‖ₑ ≤ _
  rw [mfderiv_comp t (hF.mdifferentiable one_ne_zero (γ t))
    (hγ.mdifferentiable one_ne_zero t)]
  dsimp only
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC.le]
  exact ENNReal.ofReal_le_ofReal (hbound (γ t) _)

theorem edist_le_mul_of_inner_mfderiv_le
    (g : RiemannianMetric m M) (h : RiemannianMetric n N)
    {F : M → N} (hF : ContMDiff (𝓡 m) (𝓡 n) 1 F)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x v, h.inner (F x) (mfderiv (𝓡 m) (𝓡 n) F x v)
      (mfderiv (𝓡 m) (𝓡 n) F x v) ≤ C ^ 2 * g.inner x v v) (x y : M) :
    h.edist (F x) (F y) ≤ ENNReal.ofReal C * g.edist x y := by
  apply edist_le_mul_of_tangentNorm_mfderiv_le g h hF hC _ x y
  intro z v
  have hb := Real.sqrt_le_sqrt (hbound z v)
  rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le] at hb
  exact hb

end PoincareConjecture.RiemannianMetric
