import PoincareConjecture.Proofs.M09.CenteredCoordinateDifferential
import PoincareConjecture.Proofs.M09.SquareChartPairing
import PoincareConjecture.Proofs.M09.TimeSpaceDerivative








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem centeredChartRicci_contDiffOn (hM04 : RicciFlowCurvatureTheory.{u})
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (p : M) (V W : E) :
    ContDiffOn ℝ ∞ (fun y : E ↦ D.ricci ((chartAt E p).symm y)
      (chartVectorField p V ((chartAt E p).symm y))
      (chartVectorField p W ((chartAt E p).symm y))) (chartAt E p).target := by
  have hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun q : M ↦ D.ricci q (chartVectorField p V q) (chartVectorField p W q))
      (chartAt E p).source := by
    have h := (hM04.tensor_calculus n M g D).2.1.2
      (chartAt E p).source (chartAt E p).open_source
      (fun i : Fin 2 ↦ chartVectorField p (![V, W] i))
      (fun i ↦ chartVectorField_smooth p (![V, W] i))
    simpa [LeviCivitaData.ricciEvaluation] using h
  exact (hf.comp contMDiffOn_chart_symm
    (fun y hy ↦ (chartAt E p).map_target hy)).contDiffOn

set_option backward.isDefEq.respectTransparency false in
theorem squareChartMetric_time_at_center {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (V W : E) :
    fderiv ℝ (squareChartMetric F T p) (s, (chartAt E p) p) (1, 0) V W =
      4 * s * (F.connection (T - s ^ 2)).ricci p V W := by
  have hy := (chartAt E p).map_source (mem_chart_source E p)
  have h := squareChartMetric_time_pairing F T b hb hwindow p s hs ((chartAt E p) p) V W hy
  rw [← chartVectorField_at_inverse p V ((chartAt E p) p) hy,
    ← chartVectorField_at_inverse p W ((chartAt E p) p) hy] at h
  rw [(chartAt E p).left_inv (mem_chart_source E p)] at h
  simpa only [chartVectorField_self] using h

theorem squareChartMetric_time_space_at_center {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (U V W : E) :
    fderiv ℝ (fun y : E ↦ fderiv ℝ (squareChartMetric F T p) (s, y) (1, 0))
        ((chartAt E p) p) U V W =
      4 * s * fderiv ℝ (fun y : E ↦ (F.connection (T - s ^ 2)).ricci
        ((chartAt E p).symm y) (chartVectorField p V ((chartAt E p).symm y))
        (chartVectorField p W ((chartAt E p).symm y))) ((chartAt E p) p) U := by
  let H : E → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦
    fderiv ℝ (squareChartMetric F T p) (s, y) (1, 0)
  let r : E → ℝ := fun y ↦ (F.connection (T - s ^ 2)).ricci ((chartAt E p).symm y)
    (chartVectorField p V ((chartAt E p).symm y))
    (chartVectorField p W ((chartAt E p).symm y))
  have hy := (chartAt E p).map_source (mem_chart_source E p)
  have hH : DifferentiableAt ℝ H ((chartAt E p) p) := by
    have hG : ContDiffAt ℝ ∞ (squareChartMetric F T p) (s, (chartAt E p) p) :=
      (squareChartMetric_smooth F T b hb hwindow p).contDiffAt
      ((isOpen_Ioo.prod (chartAt E p).open_target).mem_nhds ⟨hs, hy⟩)
    exact (((hG.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).comp
      ((chartAt E p) p) ((hasFDerivAt_const s ((chartAt E p) p)).prodMk
        (hasFDerivAt_id ((chartAt E p) p))).differentiableAt).clm_apply
          (differentiableAt_const ((1, 0) : ℝ × E))
  have hr : DifferentiableAt ℝ r ((chartAt E p) p) :=
    ((centeredChartRicci_contDiffOn hM04 (F.connection (T - s ^ 2)) p V W).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have heq : (fun y ↦ H y V W) =ᶠ[𝓝 ((chartAt E p) p)] (fun y ↦ (4 * s) * r y) := by
    filter_upwards [(chartAt E p).open_target.mem_nhds hy] with y hy'
    dsimp only [H, r]
    rw [squareChartMetric_time_pairing F T b hb hwindow p s hs y V W hy',
      chartVectorField_at_inverse p V y hy', chartVectorField_at_inverse p W y hy']
  have hleft := (hH.hasFDerivAt.clm_apply (hasFDerivAt_const V ((chartAt E p) p))).clm_apply
    (hasFDerivAt_const W ((chartAt E p) p))
  have hright := hr.hasFDerivAt.const_mul (4 * s)
  have h := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  simpa using congrArg (fun L : E →L[ℝ] ℝ ↦ L U) h

end PoincareConjecture.Proofs.M09
