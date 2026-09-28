import PoincareConjecture.Proofs.M09.ChartConnectionLocal
import PoincareConjecture.Proofs.M09.SquareChartCurvature
import PoincareConjecture.Proofs.M09.CoordinateBianchi








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem squareChartConnection_iterated_on_target {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (y : E) (hy : y ∈ (chartAt E p).target) (u v w : E) :
    let q := (chartAt E p).symm y
    let D := F.connection (T - s ^ 2)
    let C : E → E →L[ℝ] E →L[ℝ] E := fun z ↦
      coordinateConnectionBilinear (squareChartMetric F T p) (s, z)
    D.connection (fun x ↦ D.connection (chartVectorField p w) x (chartVectorField p v x))
        q (chartVectorField p u q) =
      chartVectorField p (C y u (C y v w) + fderiv ℝ C y u v w) q := by
  dsimp only
  let q := (chartAt E p).symm y
  let D := F.connection (T - s ^ 2)
  let C : E → E →L[ℝ] E →L[ℝ] E := fun z ↦
    coordinateConnectionBilinear (squareChartMetric F T p) (s, z)
  let φ : E → E := fun z ↦ C z v w
  let c : M → E := fun x ↦ φ ((chartAt E p) x)
  have hq : q ∈ (chartAt E p).source := (chartAt E p).map_target hy
  have hC : ContDiffAt ℝ ∞ C y := by
    have h := coordinateConnectionBilinear_contDiffOn (squareChartMetric F T p)
      (Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt E p).target)
      (isOpen_Ioo.prod (chartAt E p).open_target)
      (squareChartMetric_smooth F T b hb hwindow p)
      (fun z hz a ha ↦ squareChartMetric_pos F T p z hz.2 a ha)
    exact (h.contDiffAt ((isOpen_Ioo.prod (chartAt E p).open_target).mem_nhds
      ⟨hs, hy⟩)).comp y (contDiffAt_const.prodMk contDiffAt_id)
  have hφ : DifferentiableAt ℝ φ y :=
    ((hC.clm_apply contDiffAt_const).clm_apply contDiffAt_const).differentiableAt (by simp)
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c q := by
    have hφ' : MDifferentiableAt (𝓡 n) (𝓡 n) φ ((chartAt E p) q) := by
      simpa only [q, (chartAt E p).right_inv hy] using hφ.mdifferentiableAt
    exact hφ'.comp q ((mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt hq)
  have heq : (fun x ↦ D.connection (chartVectorField p w) x (chartVectorField p v x))
      =ᶠ[𝓝 q] (fun x ↦ chartVectorField p (c x) x) := by
    filter_upwards [(chartAt E p).open_source.mem_nhds hq] with x hx
    have h := squareChartConnection_eq F T b hb hwindow p s hs ((chartAt E p) x)
      ((chartAt E p).map_source hx) v w
    rw [(chartAt E p).left_inv hx] at h
    exact h.symm
  have hA (a : E) : D.connection (chartVectorField p a) q (chartVectorField p u q) =
      chartVectorField p (C y u a) q :=
    (squareChartConnection_eq F T b hb hwindow p s hs y hy u a).symm
  have hconn := connection_of_eventuallyEq_chartVectorField_on_source D p q hq c hc
    _ heq (chartVectorField p u q) (C y u) hA
  have hcφ : (fun z ↦ c ((chartAt E p).symm z)) =ᶠ[𝓝 y] φ := by
    filter_upwards [(chartAt E p).open_target.mem_nhds hy] with z hz
    exact congrArg φ ((chartAt E p).right_inv hz)
  have hder : mvfderiv (𝓡 n) c q (chartVectorField p u q) = fderiv ℝ C y u v w := by
    rw [mvfderiv_vector_chartVectorField p c y u hy hc, hcφ.fderiv_eq]
    have h := ((hC.differentiableAt (by simp)).hasFDerivAt.clm_apply
      (hasFDerivAt_const v y)).clm_apply (hasFDerivAt_const w y)
    simpa using congrArg (fun L : E →L[ℝ] E ↦ L u) h.fderiv
  have hcy : c q = C y v w := congrArg φ ((chartAt E p).right_inv hy)
  rw [hder, hcy] at hconn
  exact hconn

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem squareChartCurvature_on_target {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (y : E) (hy : y ∈ (chartAt E p).target) (u v w : E) :
    let q := (chartAt E p).symm y
    let C : E → E →L[ℝ] E →L[ℝ] E := fun z ↦
      coordinateConnectionBilinear (squareChartMetric F T p) (s, z)
    (F.connection (T - s ^ 2)).curvature q (chartVectorField p u q)
        (chartVectorField p v q) (chartVectorField p w q) =
      chartVectorField p (coefficientCurvature C y u v w) q := by
  dsimp only
  let q := (chartAt E p).symm y
  let D := F.connection (T - s ^ 2)
  have hq : q ∈ (chartAt E p).source := (chartAt E p).map_target hy
  have h := (hM04.tensor_calculus n M (F.metric (T - s ^ 2)) D).2.2.2.2
    (chartAt E p).source (chartAt E p).open_source (chartVectorField p u)
    (chartVectorField p v) (chartVectorField p w)
    (chartVectorField_smooth p u) (chartVectorField_smooth p v) (chartVectorField_smooth p w)
    q hq
  rw [← h, LeviCivitaData.curvatureOnFields,
    chartVectorField_bracket p u v q hq, map_zero, sub_zero]
  rw [squareChartConnection_iterated_on_target F T b hb hwindow p s hs y hy u v w,
    squareChartConnection_iterated_on_target F T b hb hwindow p s hs y hy v u w]
  let L : E →L[ℝ] TangentSpace (𝓡 n) q :=
    (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) q).inverse
  change L _ - L _ = L _
  rw [← map_sub]
  congr 1
  dsimp only [coefficientCurvature]
  abel

end PoincareConjecture.Proofs.M09
