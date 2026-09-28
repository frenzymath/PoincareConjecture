import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ProjectedTangent








set_option autoImplicit false

open Bundle Manifold Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem m65Projection_tangentNorm_le (P : M62.CircleProductData F circumference)
    (t : ℝ) (q : P.charts.Point) (V : TangentSpace (𝓡 (n + 1)) q) :
    (F.metric t).tangentNorm q.1 (P.charts.split q V).1 ≤
      (P.flow.metric t).tangentNorm q V := by
  unfold RiemannianMetric.tangentNorm
  apply Real.sqrt_le_sqrt
  rw [m65Projection_inner_self]
  exact sub_le_self _ (sq_nonneg _)



theorem m65Projection_speed_sq (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) :
    curveSpeed F (fun y r => (c y r).1) t x ^ 2 =
      curveSpeed P.flow c t x ^ 2 * (1 - m62Slope P c t x ^ 2) := by
  let := P.charts.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hchain := mfderiv_comp_apply (f := fun y => c y t)
    (g := (Prod.fst : P.charts.Point → M)) x
    (hfst.mdifferentiableAt (by simp))
    ((hc.spatial_regular t ht x).mdifferentiableAt (by norm_num)) (1 : ℝ)
  change curveVelocity (n := n) (fun y => (c y t).1) x = _ at hchain
  rw [← P.charts.split_space] at hchain
  change curveVelocity (n := n) (fun y => (c y t).1) x =
    (P.charts.split (c x t) (curveVelocity (n := n + 1) (fun y => c y t) x)).1 at hchain
  have hpair : (P.flow.metric t).inner (c x t)
      (curveVelocity (n := n + 1) (fun y => c y t) x) (P.charts.circleUnit (c x t)) =
      curveSpeed P.flow c t x * m62Slope P c t x := by
    have hv := (M62.speed_pos P.flow c hc ht x).ne'
    simp only [m62Slope, spatialUnitTangent, map_smul, smul_apply, smul_eq_mul]
    field_simp
  rw [M62.speed_sq, hchain, m65Projection_inner_self, hpair, ← M62.speed_sq]
  ring



theorem m65Projection_speed_bounds (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) (hslope : |m62Slope P c t x| ≤ 1 / 2) :
    curveSpeed P.flow c t x / 2 ≤ curveSpeed F (fun y r => (c y r).1) t x ∧
      curveSpeed F (fun y r => (c y r).1) t x ≤ curveSpeed P.flow c t x := by
  have heq := m65Projection_speed_sq P c hc ht x
  have hv := M62.speed_nonneg P.flow c t x
  have hw := M62.speed_nonneg F (fun y r => (c y r).1) t x
  have hu : m62Slope P c t x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    exact sq_le_sq.mpr (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      using hslope)
  constructor
  · nlinarith [mul_nonneg (sq_nonneg (curveSpeed P.flow c t x))
      (sub_nonneg.mpr hu)]
  · nlinarith [mul_nonneg (sq_nonneg (curveSpeed P.flow c t x))
      (sq_nonneg (m62Slope P c t x))]



theorem m65Projection_timeVelocity_le_curvature (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    (F.metric t).tangentNorm (c x t).1
      (curveVelocity (n := n) (fun r => (c x r).1) t) ≤ m62Curvature P.flow c t x := by
  let := P.charts.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun r => c x r) t := by
    have hj := hc.joint_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds (show (x, t) ∈ univ ×ˢ Ioo a b from
        ⟨mem_univ _, ht⟩))
    exact (hj.mdifferentiableAt (by simp)).comp t
      ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have hchain := mfderiv_comp_apply (f := fun r => c x r)
    (g := (Prod.fst : P.charts.Point → M)) t
    (hfst.mdifferentiableAt (by simp)) hcurve (1 : ℝ)
  change curveVelocity (n := n) (fun r => (c x r).1) t = _ at hchain
  rw [← P.charts.split_space] at hchain
  change curveVelocity (n := n) (fun r => (c x r).1) t =
    (P.charts.split (c x t) (curveVelocity (n := n + 1) (fun r => c x r) t)).1 at hchain
  rw [hc.equation t ht x] at hchain
  rw [hchain]
  exact m65Projection_tangentNorm_le P t (c x t) (m62CurvatureVector P.flow c t x)

end PoincareConjecture
