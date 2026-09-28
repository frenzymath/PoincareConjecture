import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingDifferential

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
  (P : M62.CircleProductData F circumference) {c d : ℝ → ℝ → P.charts.Point}
  {phi : ℝ → ℝ} {t x : ℝ}

theorem slope_eq_of_relabeling (hd : M62ShrinkingCurve P.flow d)
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (ht : t ∈ Icc a b) (hcd : ∀ y, c y t = d (phi y) t) :
    m62Slope P c t x = m62Slope P d t (phi x) := by
  let := P.charts.chartedSpace
  exact (slope_congr_slice P hcd).trans (slope_comp P d
    ((hd.spatial_regular t ht (phi x)).mdifferentiableAt (by norm_num))
    (hphi x) (hpos x))

theorem slope_evolution_of_relabeling (hd : M62ShrinkingCurve P.flow d)
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hcd : ∀ s ∈ Icc a b, ∀ y, c y s = d (phi y) s) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => m62Slope P c s x)
      (m62ArcSecondDerivative P.flow c t (m62Slope P c t) x +
        (m62CurvatureSquared P.flow c t x + m62TangentRicci P.flow c t x) *
          m62Slope P c t x) t := by
  let := P.charts.chartedSpace
  have ht' := Ioo_subset_Icc_self ht
  have hdiff := (hd.spatial_regular t ht').mdifferentiable (by norm_num)
  have hscalar : m62Slope P c t = fun y => m62Slope P d t (phi y) :=
    funext fun _ => slope_eq_of_relabeling P hd hphi hpos ht' (hcd t ht')
  have hf : ContDiff ℝ 2 (m62Slope P d t) :=
    ((m63Slope_contDiffOn P d hd).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)).of_le (by decide)
  have hsecond : m62ArcSecondDerivative P.flow c t (m62Slope P c t) x =
      m62ArcSecondDerivative P.flow d t (m62Slope P d t) (phi x) := by
    rw [arcSecondDerivative_congr_slice P.flow (hcd t ht'), hscalar]
    exact smooth_arcSecondDerivative_comp P.flow hd hphi hpos ht' hf
  have hk : m62CurvatureSquared P.flow c t x = m62CurvatureSquared P.flow d t (phi x) :=
    (curvatureSquared_congr_slice P.flow (hcd t ht')).trans
      (curvatureSquared_comp P.flow d hdiff hphi hpos
        ((M62.unitTangent_contMDiff P.flow d hd ht' (phi x)).mdifferentiableAt (by simp)))
  have hRic : m62TangentRicci P.flow c t x = m62TangentRicci P.flow d t (phi x) :=
    (tangentRicci_congr_slice P.flow (hcd t ht')).trans
      (tangentRicci_comp P.flow d (hdiff (phi x)) (hphi x) (hpos x))
  have heq : (fun s => m62Slope P c s x) =ᶠ[𝓝 t] (fun s => m62Slope P d s (phi x)) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact slope_eq_of_relabeling P hd hphi hpos hs (hcd s hs)
  rw [hsecond, hk, hRic, slope_eq_of_relabeling P hd hphi hpos ht' (hcd t ht')]
  exact (M62.hasDerivAt_slope P d hd ht (phi x)).congr_of_eventuallyEq heq

theorem slope_lower_bound_of_relabeling (hd : M62ShrinkingCurve P.flow d)
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hcd : ∀ s ∈ Icc a b, ∀ y, c y s = d (phi y) s)
    {K0 K1 K2 : ℝ} (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (ht : t ∈ Ioo a b) (hu : 0 ≤ m62Slope P c t x) :
    m62ArcSecondDerivative P.flow c t (m62Slope P c t) x - K2 * m62Slope P c t x ≤
      deriv (fun s => m62Slope P c s x) t := by
  let := P.charts.chartedSpace
  have ht' := Ioo_subset_Icc_self ht
  have hRicEq : m62TangentRicci P.flow c t x = m62TangentRicci P.flow d t (phi x) :=
    (tangentRicci_congr_slice P.flow (hcd t ht')).trans
      (tangentRicci_comp P.flow d
        ((hd.spatial_regular t ht' (phi x)).mdifferentiableAt (by norm_num))
        (hphi x) (hpos x))
  have hS := (M62.unitTangent_norm P.flow d hd ht' (phi x)).le
  have hRic : -K2 ≤ m62TangentRicci P.flow c t x := by
    rw [hRicEq]
    exact (abs_le.mp (hBounds.ricci t ht' (d (phi x) t) _ _ hS hS)).1
  have hk := M62.curvatureSquared_nonneg P.flow c t x
  have hcoef : 0 ≤ m62CurvatureSquared P.flow c t x + m62TangentRicci P.flow c t x + K2 :=
    by linarith
  rw [(slope_evolution_of_relabeling P hd hphi hpos hcd ht).deriv]
  nlinarith only [mul_nonneg hcoef hu]

end PoincareConjecture.M63
