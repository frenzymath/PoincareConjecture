import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.CoordinateRecurrences

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m65ProjectedTimeVelocity_eq_curvature (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    curveVelocity (n := n) (fun r => (c x r).1) t =
      (P.charts.split (c x t) (m62CurvatureVector P.flow c t x)).1 := by
  let := P.charts.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun r => c x r) t := by
    exact (hc.joint_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, ht⟩)).mdifferentiableAt
        (by simp) |>.comp t
          ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have h := mfderiv_comp_apply (f := fun r => c x r)
    (g := (Prod.fst : P.charts.Point → M)) t
    (hfst.mdifferentiableAt (by simp)) hcurve (1 : ℝ)
  change curveVelocity (n := n) (fun r => (c x r).1) t = _ at h
  rw [← P.charts.split_space] at h
  change curveVelocity (n := n) (fun r => (c x r).1) t =
    (P.charts.split (c x t) (curveVelocity (n := n + 1) (fun r => c x r) t)).1 at h
  rw [hc.equation t ht x] at h
  exact h

theorem m65ProjectedChart_time_deriv (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    HasDerivAt (fun r => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c x r).1)
      (m65ProjectedCoordinateJet P c p 1 t x) t := by
  let := P.charts.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun r => c x r) t := by
    exact (hc.joint_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, ht⟩)).mdifferentiableAt
        (by simp) |>.comp t
          ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have hbase : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => (c x r).1) t :=
    (hfst.mdifferentiableAt (by simp)).comp t hcurve
  have hchart := (mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt hx
  have htime : HasDerivAt (fun r => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c x r).1)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) (c x t).1
        (curveVelocity (n := n) (fun r => (c x r).1) t)) t :=
    (hchart.hasMFDerivAt.comp t hbase.hasMFDerivAt).hasFDerivAt.hasDerivAt
  rw [m65ProjectedTimeVelocity_eq_curvature P c hc ht] at htime
  exact htime

end PoincareConjecture
