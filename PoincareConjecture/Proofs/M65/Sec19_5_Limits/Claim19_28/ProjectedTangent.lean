import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.SlopeDerivative
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Bundle Manifold Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m65Projection_inner_self (P : M62.CircleProductData F circumference)
    (t : ℝ) (q : P.charts.Point) (V : TangentSpace (𝓡 (n + 1)) q) :
    (F.metric t).inner q.1 (P.charts.split q V).1 (P.charts.split q V).1 =
      (P.flow.metric t).inner q V V -
        ((P.flow.metric t).inner q V (P.charts.circleUnit q)) ^ 2 := by
  let := P.charts.chartedSpace
  have hframe := (M62.circleProduct_identities P).circle_identities.frame_unit q.2
  have hnonzero : P.circle.frame q.2 ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hframe
    norm_num at hframe
  obtain ⟨r, hr⟩ := exists_smul_eq_of_finrank_eq_one
    (by simpa +instances only [TangentSpace] using!
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 1)) :
      Module.finrank ℝ (TangentSpace (𝓡 1) q.2) = 1)
    hnonzero (P.charts.split q V).2
  have hvertical : P.circle.metricOnPoints.inner q.2
      (P.charts.split q V).2 (P.charts.split q V).2 = r ^ 2 := by
    rw [← hr]
    simp only [map_smul, smul_apply, smul_eq_mul, hframe]
    ring
  have hpair : (P.flow.metric t).inner q V (P.charts.circleUnit q) = r := by
    rw [P.metric_eq]
    simp only [M62.CircleProductCharts.circleUnit,
      ContinuousLinearEquiv.apply_symm_apply, map_zero, zero_add]
    rw [← hr]
    simp only [map_smul, smul_apply, smul_eq_mul, hframe, mul_one]
  rw [hpair, P.metric_eq, hvertical]
  ring

theorem m65Projection_immersed_of_slope_lt_one (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) (hslope : |m62Slope P c t x| < 1) :
    curveVelocity (n := n) (fun y => (c y t).1) x ≠ 0 := by
  let := P.charts.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hchain := mfderiv_comp_apply (f := fun y => c y t)
    (g := (Prod.fst : P.charts.Point → M)) x
    (hfst.mdifferentiableAt (by simp))
    ((hc.spatial_regular t ht x).mdifferentiableAt (by norm_num)) (1 : ℝ)
  change curveVelocity (n := n) (fun y => (c y t).1) x = _ at hchain
  rw [← P.charts.split_space] at hchain
  intro hzero
  have hhorizontal :
      (P.charts.split (c x t) (spatialUnitTangent P.flow c t x)).1 = 0 := by
    unfold spatialUnitTangent
    rw [map_smul, Prod.smul_fst]
    erw [← hchain, hzero]
    exact smul_zero _
  have heq := m65Projection_inner_self P t (c x t) (spatialUnitTangent P.flow c t x)
  rw [hhorizontal, map_zero, M62.unitTangent_inner_self P.flow c hc ht x] at heq
  change 0 = 1 - m62Slope P c t x ^ 2 at heq
  have hsquare : m62Slope P c t x ^ 2 < 1 := by
    exact (sq_lt_sq.mpr (by simpa only [abs_one] using hslope)).trans_eq (one_pow 2)
  linarith

end PoincareConjecture
