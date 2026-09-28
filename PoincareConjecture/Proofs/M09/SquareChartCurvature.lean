import PoincareConjecture.Proofs.M09.CenteredConnection
import PoincareConjecture.Proofs.M09.CenteredVectorDerivative
import PoincareConjecture.Proofs.M09.SquareChartConnection
import PoincareConjecture.Proofs.M09.CoordinateConnectionBilinear

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

set_option backward.isDefEq.respectTransparency false in
theorem squareChartConnection_slice_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (v w : E) :
    ContDiffOn ℝ ∞ (fun y ↦ coordinateConnection (squareChartMetric F T p) (s, y) v w)
      (chartAt E p).target := by
  have hC := coordinateConnectionBilinear_contDiffOn (squareChartMetric F T p)
    (Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt E p).target)
    (isOpen_Ioo.prod (chartAt E p).open_target)
    (squareChartMetric_smooth F T b hb hwindow p)
    (fun z hz a ha ↦ squareChartMetric_pos F T p z hz.2 a ha)
  have hi : ContDiffOn ℝ ∞ (fun y : E ↦ (s, y))
      (chartAt E p).target :=
    contDiffOn_const.prodMk contDiffOn_id
  exact ((hC.comp hi (fun y hy ↦ ⟨hs, hy⟩)).clm_apply contDiffOn_const).clm_apply
    contDiffOn_const

set_option backward.isDefEq.respectTransparency false in
theorem squareChartConnection_at_center {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (v w : E) :
    coordinateConnection (squareChartMetric F T p) (s, (chartAt E p) p) v w =
      ((F.connection (T - s ^ 2)).connection (chartVectorField p w) p v : E) := by
  have h := squareChartConnection_eq F T b hb hwindow p s hs ((chartAt E p) p)
    ((chartAt E p).map_source (mem_chart_source E p)) v w
  have hp : (chartAt E p).symm ((chartAt E p) p) = p :=
    (chartAt E p).left_inv (mem_chart_source E p)
  change (chartVectorField p (coordinateConnection (squareChartMetric F T p)
      (s, (chartAt E p) p) v w) ((chartAt E p).symm ((chartAt E p) p)) : E) =
    (F.connection (T - s ^ 2)).connection (chartVectorField p w)
      ((chartAt E p).symm ((chartAt E p) p))
      (chartVectorField p v ((chartAt E p).symm ((chartAt E p) p))) at h
  rw [hp] at h
  simpa only [chartVectorField_self] using h

set_option backward.isDefEq.respectTransparency false in
theorem squareChartConnection_iterated_at_center {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (U V W : E) :
    let D := F.connection (T - s ^ 2)
    let C : E → E → E → E := fun y v w ↦
      coordinateConnection (squareChartMetric F T p) (s, y) v w
    (D.connection (fun q ↦ D.connection (chartVectorField p W) q
      (chartVectorField p V q)) p U : E) =
        C ((chartAt E p) p) U (C ((chartAt E p) p) V W) +
          fderiv ℝ (fun y ↦ C y V W) ((chartAt E p) p) U := by
  let D := F.connection (T - s ^ 2)
  let φ : E → E := fun y ↦ coordinateConnection (squareChartMetric F T p) (s, y) V W
  let c : M → E := fun q ↦ φ ((chartAt E p) q)
  have hφ : DifferentiableAt ℝ φ ((chartAt E p) p) :=
    ((squareChartConnection_slice_contDiffOn F T b hb hwindow p s hs V W).contDiffAt
      ((chartAt E p).open_target.mem_nhds
        ((chartAt E p).map_source (mem_chart_source E p)))).differentiableAt (by simp)
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c p := hφ.mdifferentiableAt.comp p
    ((mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt (mem_chart_source E p))
  have heq : (fun q ↦ D.connection (chartVectorField p W) q (chartVectorField p V q))
      =ᶠ[𝓝 p] (fun q ↦ chartVectorField p (c q) q) := by
    filter_upwards [(chartAt E p).open_source.mem_nhds (mem_chart_source E p)] with q hq
    have h := squareChartConnection_eq F T b hb hwindow p s hs ((chartAt E p) q)
      ((chartAt E p).map_source hq) V W
    convert! h.symm using 1 <;> rw [(chartAt E p).left_inv hq]
  have h := connection_of_eventuallyEq_chartVectorField D p c hc _ heq U
  rw [mvfderiv_vector_centeredChart_of_eventuallyEq p c φ hφ
    (Filter.Eventually.of_forall (fun _ ↦ rfl)) U,
    frozenConnectionEndomorphism_apply, connection_frozenExtend_eq_chartVectorField,
    ← squareChartConnection_at_center F T b hb hwindow p s hs] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem squareChartCurvature_at_center {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (U V W : E) :
    let C : E → E → E → E := fun y v w ↦
      coordinateConnection (squareChartMetric F T p) (s, y) v w
    ((F.connection (T - s ^ 2)).curvature p U V W : E) =
      fderiv ℝ (fun y ↦ C y V W) ((chartAt E p) p) U -
      fderiv ℝ (fun y ↦ C y U W) ((chartAt E p) p) V +
      C ((chartAt E p) p) U (C ((chartAt E p) p) V W) -
      C ((chartAt E p) p) V (C ((chartAt E p) p) U W) := by
  let D := F.connection (T - s ^ 2)
  have h := (hM04.tensor_calculus n M (F.metric (T - s ^ 2)) D).2.2.2.2
    (chartAt E p).source (chartAt E p).open_source (chartVectorField p U)
    (chartVectorField p V) (chartVectorField p W)
    (chartVectorField_smooth p U) (chartVectorField_smooth p V) (chartVectorField_smooth p W)
    p (mem_chart_source E p)
  rw [chartVectorField_self, chartVectorField_self, chartVectorField_self] at h
  rw [← h, LeviCivitaData.curvatureOnFields, chartVectorField_self, chartVectorField_self,
    chartVectorField_bracket p U V p (mem_chart_source E p), map_zero, sub_zero]
  rw [squareChartConnection_iterated_at_center F T b hb hwindow p s hs U V W,
    squareChartConnection_iterated_at_center F T b hb hwindow p s hs V U W]
  abel

end PoincareConjecture.Proofs.M09
