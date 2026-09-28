import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.C2Continuity
import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductIdentities










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b T : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem c2_slope_continuousOn (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T))
    (hT : a < T) :
    ContinuousOn (fun z : ℝ × ℝ => m62Slope P c z.2 z.1) (univ ×ˢ Icc a T) := by
  let := P.charts.chartedSpace
  have hB := (M62.circleProduct_identities P).circle_unit_smooth.continuous.continuousOn.comp
    hc.continuous (fun _ _ => mem_univ _)
  have hpair := c2_metric_pairing_continuousOn P.flow c hc hT _ _
    hc.velocity_continuous hB
  have hinv := (c2_speed_continuousOn P.flow c hc hT).inv₀
    (fun z hz => (c2_speed_pos P.flow c hc hz.2 z.1).ne')
  simpa only [Pi.mul_def, Pi.inv_def, m62Slope, spatialUnitTangent,
    map_smul, smul_apply, smul_eq_mul] using hinv.mul hpair



theorem c2_abs_slope_le_one (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T))
    {t : ℝ} (ht : t ∈ Icc a T) (x : ℝ) : |m62Slope P c t x| ≤ 1 := by
  let := P.charts.chartedSpace
  let g := P.flow.metric t
  let p := c x t
  let S := spatialUnitTangent P.flow c t x
  let B := P.charts.circleUnit p
  let : RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.charts.Point → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hS : ‖S‖ = 1 := by
    rw [norm_eq_sqrt_real_inner]
    exact c2_unitTangent_norm P.flow c hc ht x
  have hB : ‖B‖ = 1 := by
    rw [norm_eq_sqrt_real_inner]
    change Real.sqrt (g.inner p B B) = 1
    rw [(M62.circleProduct_identities P).circle_unit]
    norm_num
  change |inner ℝ S B| ≤ 1
  calc
    _ ≤ ‖S‖ * ‖B‖ := abs_real_inner_le_norm S B
    _ = 1 := by rw [hS, hB, mul_one]



theorem c2_rampRatio_continuousOn (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T))
    (hT : a < T) (hu : ∀ t ∈ Icc a T, ∀ x, 0 < m62Slope P c t x) (epsilon : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => m63RampRatio P c epsilon z.2 z.1)
      (univ ×ˢ Icc a T) :=
  (c2_regularized_continuousOn P.flow c hc hT epsilon).div
    (c2_slope_continuousOn P c hc hT) (fun z hz => (hu z.2 hz.2 z.1).ne')

end PoincareConjecture.M63
