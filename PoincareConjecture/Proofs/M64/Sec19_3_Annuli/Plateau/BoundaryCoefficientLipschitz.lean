import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCoordinateCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture

local instance m64CoefficientLipschitz_secondGroup
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64CoefficientLipschitz_secondSpace
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toNormedSpace

theorem m64SmoothCoefficient_compact_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O : Set E} (hO : IsOpen O) {f : E → F} (hf : ContDiffOn ℝ ∞ f O)
    {a : E} {R : ℝ} (hKO : closedBall a R ⊆ O) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ closedBall a R,
      ‖f x‖ ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C ∧
      ∀ y ∈ closedBall a R, ‖f y - f x‖ ≤ C * ‖y - x‖ ∧
        ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ C * ‖y - x‖ := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) O := by
    intro x hx
    exact (((hf x hx).contDiffAt (hO.mem_nhds hx)).fderiv_right (by simp)).contDiffWithinAt
  have hdd : ContinuousOn (fderiv ℝ (fderiv ℝ f)) O :=
    hd.continuousOn_fderiv_of_isOpen hO (by simp)
  obtain ⟨C0, h0⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn
    (hf.continuousOn.mono hKO)
  obtain ⟨C1, h1⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn
    (hd.continuousOn.mono hKO)
  obtain ⟨C2, h2⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn (hdd.mono hKO)
  let C := 1 + |C0| + |C1| + |C2|
  have hc0 : C0 ≤ C := by dsimp [C]; linarith [le_abs_self C0, abs_nonneg C1, abs_nonneg C2]
  have hc1 : C1 ≤ C := by dsimp [C]; linarith [le_abs_self C1, abs_nonneg C0, abs_nonneg C2]
  have hc2 : C2 ≤ C := by dsimp [C]; linarith [le_abs_self C2, abs_nonneg C0, abs_nonneg C1]
  refine ⟨C, by dsimp [C]; positivity, fun x hx => ⟨(h0 x hx).trans hc0,
    (h1 x hx).trans hc1, fun y hy => ⟨?_, ?_⟩⟩⟩
  · exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => ((hf z (hKO hz)).contDiffAt (hO.mem_nhds (hKO hz))).differentiableAt
        (by simp))
      (fun z hz => (h1 z hz).trans hc1) (convex_closedBall a R) hx hy
  · exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => ((hd z (hKO hz)).contDiffAt (hO.mem_nhds (hKO hz))).differentiableAt
        (by simp))
      (fun z hz => (h2 z hz).trans hc2) (convex_closedBall a R) hx hy

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64CoefficientLipschitz_bilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance m64CoefficientLipschitz_bilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem m64ChartCoefficient_lipschitz_bounds (g : RiemannianMetric n M) (b : M)
    {a : E} {R : ℝ} (hK : closedBall a R ⊆ (extChartAt (𝓡 n) b).target) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ closedBall a R,
      ‖G x‖ ≤ C ∧ ‖fderiv ℝ G x‖ ≤ C ∧
      ∀ y ∈ closedBall a R, ‖G y - G x‖ ≤ C * ‖y - x‖ ∧
        ‖fderiv ℝ G y - fderiv ℝ G x‖ ≤ C * ‖y - x‖ :=
  m64SmoothCoefficient_compact_bounds (isOpen_extChartAt_target b)
    (g.contDiffOn_chartCoefficients b) hK

end PoincareConjecture
