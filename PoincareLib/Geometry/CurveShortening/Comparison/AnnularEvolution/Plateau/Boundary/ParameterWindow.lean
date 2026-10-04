import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.BoundaryParameterLabels

/-!
# A physical boundary window for the actual continuous label

The original label's continuity puts both nearby endpoints in the fixed
axis interval and near the fixed target chart center. The window is
chosen before any semicircle or radius. Source: Morrey ICM pp. 183-185;
M64 phase-cone normalization derivation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Metric
open scoped Topology

namespace PoincareMT

/-- A continuous original label and observed boundary curve give one physical window for
both parameter and observation capture. Proof expansion for Morgan-Tian (2007), Lemma 19.15,
pp. 447-449; M64 derivation 2026-09-26-phase-cone-normalization.md. -/
theorem m64Boundary_parameter_window {E : Type*} [PseudoMetricSpace E]
    {sigma : ℝ → ℝ} {c : ℝ → E} (hsigma : Continuous sigma) (hc : Continuous c)
    (x : ℝ) {eta delta : ℝ} (heta : 0 < eta) (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ y : ℝ, |y - x| < epsilon →
      sigma y - sigma x ∈ Ioo (-eta) eta ∧
        dist (c (sigma y)) (c (sigma x)) < delta / 2 := by
  obtain ⟨e1, he1, h1⟩ := Metric.continuousAt_iff.mp (hsigma.continuousAt (x := x)) eta heta
  obtain ⟨e2, he2, h2⟩ := Metric.continuousAt_iff.mp
    ((hc.comp hsigma).continuousAt (x := x)) (delta / 2) (by positivity)
  refine ⟨min e1 e2, lt_min he1 he2, ?_⟩
  intro y hy
  have hy1 : dist y x < e1 := by
    simpa only [Real.dist_eq] using hy.trans_le (min_le_left e1 e2)
  have hy2 : dist y x < e2 := by
    simpa only [Real.dist_eq] using hy.trans_le (min_le_right e1 e2)
  have hparam : |sigma y - sigma x| < eta := by
    simpa only [Real.dist_eq] using h1 hy1
  exact ⟨abs_lt.mp hparam, h2 hy2⟩

end PoincareMT
