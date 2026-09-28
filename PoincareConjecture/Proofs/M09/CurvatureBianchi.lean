import PoincareConjecture.Proofs.M09.FixedChartCurvature
import PoincareConjecture.Proofs.M09.CoordinateCompatibility

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

theorem coefficientCurvature_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : E → E →L[ℝ] E →L[ℝ] E) (x : E) (hC : ContDiffAt ℝ ∞ C x)
    (u v w : E) : ContDiffAt ℝ ∞ (fun y ↦ coefficientCurvature C y u v w) x := by
  have hD := hC.fderiv_right (m := ∞) (by simp)
  have hfirst := ((hD.clm_apply (contDiffAt_const (c := u))).clm_apply
    (contDiffAt_const (c := v))).clm_apply (contDiffAt_const (c := w))
  have hsecond := ((hD.clm_apply (contDiffAt_const (c := v))).clm_apply
    (contDiffAt_const (c := u))).clm_apply (contDiffAt_const (c := w))
  exact ((hfirst.sub hsecond).add ((hC.clm_apply contDiffAt_const).clm_apply
    ((hC.clm_apply contDiffAt_const).clm_apply contDiffAt_const))).sub
      ((hC.clm_apply contDiffAt_const).clm_apply
        ((hC.clm_apply contDiffAt_const).clm_apply contDiffAt_const))

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem covariantRiemannDerivative_centeredChart {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) (a u v w z : TangentSpace (𝓡 n) p) :
    D.covariantTensorDerivative D.riemannEvaluation p ![a, u, v, w, z] =
      mvfderiv (𝓡 n) (fun q ↦ D.curvatureTensor q (chartVectorField p u q)
        (chartVectorField p v q) (chartVectorField p w q) (chartVectorField p z q)) p a -
      D.curvatureTensor p (D.connection (chartVectorField p u) p a) v w z -
      D.curvatureTensor p u (D.connection (chartVectorField p v) p a) w z -
      D.curvatureTensor p u v (D.connection (chartVectorField p w) p a) z -
      D.curvatureTensor p u v w (D.connection (chartVectorField p z) p a) := by
  have h := covariantTensorDerivative_centeredChart D D.riemannEvaluation p a ![u, v, w, z]
  simpa [LeviCivitaData.riemannEvaluation, Fin.sum_univ_succ, sub_add_eq_sub_sub] using h

theorem squareChartCoefficient_contDiffAt {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (y : E) (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (fun z ↦ coordinateConnectionBilinear (squareChartMetric F T p) (s, z)) y := by
  have h := coordinateConnectionBilinear_contDiffOn (squareChartMetric F T p)
    (Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt E p).target)
    (isOpen_Ioo.prod (chartAt E p).open_target)
    (squareChartMetric_smooth F T b hb hwindow p)
    (fun z hz a ha ↦ squareChartMetric_pos F T p z hz.2 a ha)
  exact (h.contDiffAt ((isOpen_Ioo.prod (chartAt E p).open_target).mem_nhds
    ⟨hs, hy⟩)).comp y (contDiffAt_const.prodMk contDiffAt_id)

set_option backward.isDefEq.respectTransparency false in
theorem squareChartCurvature_coefficient_at_center {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (u v w : E) :
    ((F.connection (T - s ^ 2)).curvature p u v w : E) =
      coefficientCurvature
        (fun z ↦ coordinateConnectionBilinear (squareChartMetric F T p) (s, z))
        ((chartAt E p) p) u v w := by
  have h := squareChartCurvature_on_target F hM04 T b hb hwindow p s hs
    ((chartAt E p) p) ((chartAt E p).map_source (mem_chart_source E p)) u v w
  dsimp only at h
  rw [(chartAt E p).left_inv (mem_chart_source E p)] at h
  simpa only [chartVectorField_self] using h

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem squareChartCovariantCurvature_at_center {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (a u v w z : E) :
    let D := F.connection (T - s ^ 2)
    let C : E → E →L[ℝ] E →L[ℝ] E := fun y ↦
      coordinateConnectionBilinear (squareChartMetric F T p) (s, y)
    D.covariantTensorDerivative D.riemannEvaluation p ![a, u, v, w, z] =
      (F.metric (T - s ^ 2)).inner p
        (coefficientCurvatureCovariantDerivative («E» := E) C ((chartAt E p) p) a u v z) w := by
  dsimp only
  let D := F.connection (T - s ^ 2)
  let g := F.metric (T - s ^ 2)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let e := chartAt E p
  let y0 := e p
  let C : E → E →L[ℝ] E →L[ℝ] E := fun y ↦
    coordinateConnectionBilinear (squareChartMetric F T p) (s, y)
  let φ : E → E := fun y ↦ coefficientCurvature C y u v z
  let c : M → E := fun q ↦ φ (e q)
  let K : (q : M) → TangentSpace (𝓡 n) q := fun q ↦ chartVectorField p (c q) q
  have hsrc : p ∈ e.source := mem_chart_source E p
  have htar : y0 ∈ e.target := e.map_source hsrc
  have hC : ContDiffAt ℝ ∞ C y0 :=
    squareChartCoefficient_contDiffAt F T b hb hwindow p s hs y0 htar
  have hφ : DifferentiableAt ℝ φ y0 :=
    (coefficientCurvature_contDiffAt C y0 hC u v z).differentiableAt (by simp)
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c p := hφ.mdifferentiableAt.comp p
    ((mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt hsrc)
  have hK := mdifferentiableAt_chartVectorField_variable p c hc
  have hw := ((chartVectorField_smooth p w).contMDiffAt (e.open_source.mem_nhds hsrc)).mdifferentiableAt
    (by simp)
  have hconn (A B : E) : (D.connection (chartVectorField p B) p A : E) = C y0 A B :=
    (squareChartConnection_at_center F T b hb hwindow p s hs A B).symm
  have hKconn := connection_chartVectorField_variable D p c hc a
  dsimp only at hKconn
  rw [frozenConnectionEndomorphism_apply, connection_frozenExtend_eq_chartVectorField,
    hconn, mvfderiv_vector_centeredChart_of_eventuallyEq p c φ hφ
      (Filter.Eventually.of_forall (fun _ ↦ rfl)) a] at hKconn
  have hKp : K p = φ y0 := chartVectorField_self p (φ y0)
  have hmetric := D.metricCompatible.mvfderiv_inner_eq (FiberBundle.extend E (x := p) a) hK hw
  have hmetric' : mvfderiv (𝓡 n)
      (fun q ↦ g.inner q (K q) (chartVectorField p w q)) p a =
      g.inner p (C y0 a (φ y0) + fderiv ℝ φ y0 a) w +
        g.inner p (φ y0) (C y0 a w) := by
    simpa only [FiberBundle.extend_apply_self, chartVectorField_self, hKp, hKconn,
      hconn, K, c, y0, e] using! hmetric
  have heq : (fun q ↦ D.curvatureTensor q (chartVectorField p u q)
      (chartVectorField p v q) (chartVectorField p w q) (chartVectorField p z q)) =ᶠ[𝓝 p]
      (fun q ↦ g.inner q (K q) (chartVectorField p w q)) := by
    filter_upwards [e.open_source.mem_nhds hsrc] with q hq
    have hR := squareChartCurvature_on_target F hM04 T b hb hwindow p s hs
      (e q) (e.map_source hq) u v z
    have hR' : D.curvature q (chartVectorField p u q) (chartVectorField p v q)
        (chartVectorField p z q) = K q := by
      dsimp only at hR
      rw [e.left_inv hq] at hR
      exact hR
    change g.inner q (D.curvature q (chartVectorField p u q)
      (chartVectorField p v q) (chartVectorField p z q)) (chartVectorField p w q) = _
    rw [hR']
  have hmetric'' : mvfderiv (𝓡 n)
      (fun q ↦ D.curvatureTensor q (chartVectorField p u q) (chartVectorField p v q)
        (chartVectorField p w q) (chartVectorField p z q)) p a =
      g.inner p (C y0 a (φ y0) + fderiv ℝ φ y0 a) w +
        g.inner p (φ y0) (C y0 a w) := by
    rw [mvfderiv, heq.mfderiv_eq]
    exact hmetric'
  have hR (U V W Z : E) : D.curvatureTensor p U V W Z =
      g.inner p (coefficientCurvature C y0 U V Z) W :=
    congrArg (fun ξ : E ↦ g.inner p ξ W)
      (squareChartCurvature_coefficient_at_center F hM04 T b hb hwindow p s hs U V Z)
  have h := covariantRiemannDerivative_centeredChart D p a u v w z
  rw [hmetric''] at h
  simp only [hconn, hR] at h
  rw [h]
  change _ = g.inner p (coefficientCurvatureCovariantDerivative («E» := E) C y0 a u v z) w
  simp only [coefficientCurvatureCovariantDerivative, coefficientCurvatureExteriorDerivative,
    map_sub, map_add, sub_apply, add_apply, φ]
  let r0 := g.inner p (C y0 a (coefficientCurvature C y0 u v z)) w
  let r1 := g.inner p (fderiv ℝ φ y0 a) w
  let r2 := g.inner p (coefficientCurvature C y0 u v z) (C y0 a w)
  let r3 := g.inner p (coefficientCurvature C y0 (C y0 a u) v z) w
  let r4 := g.inner p (coefficientCurvature C y0 u (C y0 a v) z) w
  let r5 := g.inner p (coefficientCurvature C y0 u v (C y0 a z)) w
  change r0 + r1 + r2 - r3 - r4 - r2 - r5 = r1 + r0 - r5 - r3 - r4
  ring

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem squareTime_curvature_second_bianchi {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (a u v w z : E) :
    let D := F.connection (T - s ^ 2)
    D.covariantTensorDerivative D.riemannEvaluation p ![a, u, v, w, z] +
      D.covariantTensorDerivative D.riemannEvaluation p ![u, v, a, w, z] +
      D.covariantTensorDerivative D.riemannEvaluation p ![v, a, u, w, z] = 0 := by
  dsimp only
  let y0 := (chartAt E p) p
  let C : E → E →L[ℝ] E →L[ℝ] E := fun y ↦
    coordinateConnectionBilinear (squareChartMetric F T p) (s, y)
  have hy : y0 ∈ (chartAt E p).target := (chartAt E p).map_source (mem_chart_source E p)
  have hC := squareChartCoefficient_contDiffAt F T b hb hwindow p s hs y0 hy
  have hG : DifferentiableAt ℝ (squareChartMetric F T p) (s, y0) :=
    ((squareChartMetric_smooth F T b hb hwindow p).contDiffAt
    ((isOpen_Ioo.prod (chartAt E p).open_target).mem_nhds ⟨hs, hy⟩)).differentiableAt (by simp)
  have hsym (U V : E) : C y0 U V = C y0 V U :=
    coordinateConnection_symm (squareChartMetric F T p) (s, y0) hG
      (Filter.Eventually.of_forall (fun q A B ↦ squareChartMetric_symm F T p q A B)) U V
  have h := coefficientCurvature_bianchi C y0 hC hsym a u v z
  have hp := congrArg (fun ξ : E ↦ (F.metric (T - s ^ 2)).inner p ξ w) h
  simp only [map_add, add_apply, map_zero, zero_apply] at hp
  rw [squareChartCovariantCurvature_at_center F hM04 T b hb hwindow p s hs,
    squareChartCovariantCurvature_at_center F hM04 T b hb hwindow p s hs,
    squareChartCovariantCurvature_at_center F hM04 T b hb hwindow p s hs]
  exact hp

end PoincareConjecture.Proofs.M09
