import PoincareConjecture.Proofs.M08.ChartConnection
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance chartTensorDerivativesDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance chartTensorDerivativesDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance chartTensorDerivativesBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance chartTensorDerivativesBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem tangent_eq_of_chart_metric_pair (g : RiemannianMetric n M) {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {v w : TangentSpace (𝓡 n) y}
    (h : ∀ q : EuclideanSpace ℝ (Fin n),
      g.inner y v (chartFrame x q y) = g.inner y w (chartFrame x q y)) : v = w := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have heq := h (e.continuousLinearMapAt ℝ y (v - w))
  have hframe : chartFrame x (e.continuousLinearMapAt ℝ y (v - w)) y = v - w :=
    e.symmL_continuousLinearMapAt hy _
  rw [hframe] at heq
  have hz : g.inner y (v - w) (v - w) = 0 := by
    calc
      _ = g.inner y v (v - w) - g.inner y w (v - w) :=
        congrArg (fun L : TangentSpace (𝓡 n) y →L[ℝ] ℝ ↦ L (v - w))
          ((g.inner y).map_sub v w)
      _ = 0 := sub_eq_zero.mpr heq
  by_contra hne
  exact (ne_of_gt (g.pos y (v - w) (sub_ne_zero.mpr hne))) hz

theorem section_chartCoefficient_contMDiffAt {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (X : ∀ p : M, TangentSpace (𝓡 n) p)
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p (X p)) y) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞
      (fun p ↦ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).continuousLinearMapAt
        ℝ p (X p)) y := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have h := (e.contMDiffAt_iff (x₀ := y)
    (f := fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p (X p))
    (e.mem_source.mpr hy)).mp hX
  apply h.2.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hy] with p hp
  exact e.continuousLinearMapAt_apply_of_mem ℝ hp _

theorem section_metric_pair_contMDiffAt (g : RiemannianMetric n M)
    {y : M} (X W : ∀ p : M, TangentSpace (𝓡 n) p)
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p (X p)) y)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p (W p)) y) :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun p ↦ g.inner p (X p) (W p)) y := by
  have h : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞
      (fun p ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p
        (g.inner p (X p) (W p))) y := by
    apply ContMDiffAt.clm_bundle_apply₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
    · exact g.contMDiff.contMDiffAt
    · exact hX
    · exact hW
  simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
    using (Bundle.contMDiffAt_totalSpace.mp h).2

set_option maxHeartbeats 1600000 in
theorem connection_chart_section {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C)
    (X : ∀ p : M, TangentSpace (𝓡 n) p)
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p (X p)) y)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hc : DifferentiableAt ℝ c (extChartAt (𝓡 n) x y))
    (hrep : ∀ᶠ p in 𝓝 y, X p = chartFrame x (c (extChartAt (𝓡 n) x p)) p)
    (v : EuclideanSpace ℝ (Fin n)) :
    (F.connection (T - s ^ 2)).connection X y (chartFrame x v y) =
      chartFrame x (fderiv ℝ c (extChartAt (𝓡 n) x y) v +
        closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y)
          v (c (extChartAt (𝓡 n) x y))) y := by
  let g := F.metric (T - s ^ 2)
  let D := F.connection (T - s ^ 2)
  let e := extChartAt (𝓡 n) x
  have hy' : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have ht : e y ∈ e.target := e.map_source hy'
  have hinv := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) x _ ht).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds ht)
  have hrep₀ := hrep.self_of_nhds
  have hframe (w : EuclideanSpace ℝ (Fin n)) :=
    (chartFrame_contMDiffOn x w y hy).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)
  have hG := hasFDerivAt_spatialWithin (isOpen_extChartAt_target (I := 𝓡 n) x) _
    (chartActionMetric_closed_contDiffOn F T x htime) hs ht
  apply tangent_eq_of_chart_metric_pair g hy
  intro w
  let f : M → ℝ := fun p ↦ g.inner p (X p) (chartFrame x w p)
  have hf := section_metric_pair_contMDiffAt g X (chartFrame x w) hX (hframe w)
  have heq : (fun q ↦ chartActionMetric F T x (s, q) (c q) w) =ᶠ[𝓝 (e y)] f ∘ e.symm := by
    have hrep' : ∀ᶠ q in 𝓝 (e y),
        X (e.symm q) = chartFrame x (c (e (e.symm q))) (e.symm q) := by
      have hcont : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
        have hh : Tendsto e.symm (𝓝 (e y)) (𝓝 (e.symm (e y))) := hinv.continuousAt.tendsto
        rwa [e.left_inv hy'] at hh
      exact hcont hrep
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds ht, hrep'] with q hq hqX
    have hq' : e.symm q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
      simpa only [e, extChartAt_source] using e.map_target hq
    dsimp only [Function.comp_def, f]
    rw [hqX, e.right_inv hq]
    exact metricInChart_apply g hq' (c q) w
  have heval := (hG.clm_apply hc.hasFDerivAt).clm_apply (hasFDerivAt_const w (e y))
  have hcalc := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ A v)
    (heq.fderiv_eq (𝕜 := ℝ))
  rw [heval.fderiv, chart_scalar_fderiv_apply hy f (hf.mdifferentiableAt (by simp))] at hcalc
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_zero, zero_add] at hcalc
  have hsp := chartActionMetric_closed_spatial_apply F T htime hy hs v (c (e y)) w
  have hpair := chartActionMetric_apply F T hy s (fderiv ℝ c (e y) v) w
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hx := D.metricCompatible.mvfderiv_inner_eq (chartFrame x v)
    (hX.mdifferentiableAt (by simp)) ((hframe w).mdifferentiableAt (by simp))
  have hconst := D.metricCompatible.mvfderiv_inner_eq (chartFrame x v)
    ((hframe (c (e y))).mdifferentiableAt (by simp)) ((hframe w).mdifferentiableAt (by simp))
  change mvfderiv (𝓡 n) f y (chartFrame x v y) =
    g.inner y (D.connection X y (chartFrame x v y)) (chartFrame x w y) +
      g.inner y (X y) (D.connection (chartFrame x w) y (chartFrame x v y)) at hx
  change mvfderiv (𝓡 n)
      (fun p ↦ g.inner p (chartFrame x (c (e y)) p) (chartFrame x w p)) y (chartFrame x v y) =
    g.inner y (D.connection (chartFrame x (c (e y))) y (chartFrame x v y)) (chartFrame x w y) +
      g.inner y (chartFrame x (c (e y)) y)
        (D.connection (chartFrame x w) y (chartFrame x v y)) at hconst
  rw [hrep₀] at hx
  have hconnection := closedChartChristoffel_connection F T htime hy hs v (c (e y))
  change D.connection (chartFrame x (c (e y))) y (chartFrame x v y) = _ at hconnection
  rw [hconnection] at hconst
  change g.inner y (D.connection X y (chartFrame x v y)) (chartFrame x w y) = _
  rw [show chartFrame x (fderiv ℝ c (e y) v +
        closedChartChristoffel F T x C (s, e y) v (c (e y))) y =
      chartFrame x (fderiv ℝ c (e y) v) y +
        chartFrame x (closedChartChristoffel F T x C (s, e y) v (c (e y))) y from
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).symmL ℝ y |>.map_add _ _]
  simp only [map_add, ContinuousLinearMap.add_apply]
  dsimp only [g, e] at hx hconst hcalc hpair hsp ⊢
  linarith

def sectionModel (x : M) (X : ∀ p : M, TangentSpace (𝓡 n) p)
    (q : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).continuousLinearMapAt
    ℝ ((extChartAt (𝓡 n) x).symm q)
      (X ((extChartAt (𝓡 n) x).symm q))

theorem chartFrame_sectionModel {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (X : ∀ p : M, TangentSpace (𝓡 n) p) :
    chartFrame x (sectionModel x X (extChartAt (𝓡 n) x y)) y = X y := by
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by simpa only [extChartAt_source] using hy
  unfold sectionModel chartFrame
  rw [(extChartAt (𝓡 n) x).left_inv hy']
  exact (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).symmL_continuousLinearMapAt hy _

theorem sectionModel_contDiffAt {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (X : ∀ p : M, TangentSpace (𝓡 n) p)
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p (X p)) y) :
    ContDiffAt ℝ ∞ (sectionModel x X) (extChartAt (𝓡 n) x y) := by
  let e := extChartAt (𝓡 n) x
  have hy' : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have ht := e.map_source hy'
  have hinv := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) x _ ht).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds ht)
  have hc := section_chartCoefficient_contMDiffAt hy X hX
  have hc' : ContMDiffAt (𝓡 n) (𝓡 n) ∞
      (fun p ↦ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).continuousLinearMapAt
        ℝ p (X p)) (e.symm (e y)) := by
    rwa [e.left_inv hy']
  exact (hc'.comp (e y) hinv).contDiffAt

theorem sectionModel_at_chartFrame {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v : EuclideanSpace ℝ (Fin n)) :
    sectionModel x (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (chartFrame x v y))
      (extChartAt (𝓡 n) x y) = v := by
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by simpa only [extChartAt_source] using hy
  unfold sectionModel
  rw [(extChartAt (𝓡 n) x).left_inv hy', FiberBundle.extend_apply_self]
  exact (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).continuousLinearMapAt_symmL hy v

set_option maxHeartbeats 1600000 in
theorem hessian_chart {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (f : M → ℝ)
    (hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f)
    (v w : EuclideanSpace ℝ (Fin n)) :
    (F.connection (T - s ^ 2)).hessian f y (chartFrame x v y) (chartFrame x w y) =
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 n) x).symm))
          (extChartAt (𝓡 n) x y) v w -
        fderiv ℝ (f ∘ (extChartAt (𝓡 n) x).symm) (extChartAt (𝓡 n) x y)
          (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) v w) := by
  let e := extChartAt (𝓡 n) x
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (chartFrame x w y)
  let c := sectionModel x Y
  let f₀ := f ∘ e.symm
  let H : M → ℝ := fun p ↦ mvfderiv (𝓡 n) f p (Y p)
  let H₀ : EuclideanSpace ℝ (Fin n) → ℝ := fun q ↦ fderiv ℝ f₀ q (c q)
  have hy' : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have ht := e.map_source hy'
  have hinv := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) x _ ht).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds ht)
  have hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p (Y p)) y :=
    FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (chartFrame x w y)
  have hc : ContDiffAt ℝ ∞ c (e y) := sectionModel_contDiffAt hy Y hY
  have hc₀ : c (e y) = w := sectionModel_at_chartFrame hy w
  have hrep : ∀ᶠ p in 𝓝 y, Y p = chartFrame x (c (e p)) p := by
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy] with p hp
    exact (chartFrame_sectionModel hp Y).symm
  have hf₀ : ContDiffAt ℝ ∞ f₀ (e y) :=
    (hf.contMDiffAt.comp (e y) hinv).contDiffAt
  have hdf₀ : DifferentiableAt ℝ (fderiv ℝ f₀) (e y) :=
    (hf₀.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hH₀ := hdf₀.hasFDerivAt.clm_apply (hc.differentiableAt (by simp)).hasFDerivAt
  have hHrep : H =ᶠ[𝓝 y] H₀ ∘ e := by
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy, hrep]
      with p hp hpY
    dsimp only [H, H₀, Function.comp_def]
    rw [hpY]
    exact (chart_scalar_fderiv_apply hp f (hf.mdifferentiableAt (by simp)) (c (e p))).symm
  have hH : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) H y :=
    ((hH₀.differentiableAt.mdifferentiableAt).comp y
      ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hy).mdifferentiableAt (by simp))).congr_of_eventuallyEq hHrep
  have heq : H ∘ e.symm =ᶠ[𝓝 (e y)] H₀ := by
    have hcont : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
      have hh : Tendsto e.symm (𝓝 (e y)) (𝓝 (e.symm (e y))) := hinv.continuousAt.tendsto
      rwa [e.left_inv hy'] at hh
    filter_upwards [hcont hHrep, (isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds ht]
      with q hq hqt
    change H (e.symm q) = H₀ (e (e.symm q)) at hq
    simpa only [Function.comp_def, e.right_inv hqt] using hq
  have hHderiv := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ A v)
    (heq.fderiv_eq (𝕜 := ℝ))
  rw [chart_scalar_fderiv_apply hy H hH, hH₀.fderiv] at hHderiv
  simp only [add_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    hc₀] at hHderiv
  have hconn := connection_chart_section F T htime hy hs Y hY c
    (hc.differentiableAt (by simp)) hrep v
  rw [hc₀] at hconn
  unfold LeviCivitaData.hessian LeviCivitaData.hessianOnFields
  rw [FiberBundle.extend_apply_self]
  change mvfderiv (𝓡 n) H y (chartFrame x v y) -
    mvfderiv (𝓡 n) f y ((F.connection (T - s ^ 2)).connection Y y (chartFrame x v y)) = _
  rw [hHderiv, hconn, ← chart_scalar_fderiv_apply hy f (hf.mdifferentiableAt (by simp))]
  simp only [map_add]
  ring

theorem ricci_add_left_of_curvatureTheory (hM04 : RicciFlowCurvatureTheory.{u})
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (v w z : TangentSpace (𝓡 n) x) : D.ricci x (v + w) z = D.ricci x v z + D.ricci x w z := by
  obtain ⟨A, hA⟩ := ((hM04.tensor_calculus n M g D).2.1).1 x
  have heval (a b : TangentSpace (𝓡 n) x) : D.ricci x a b = A ![a, b] := by
    simpa only [LeviCivitaData.ricciEvaluation, Matrix.cons_val_zero,
      Matrix.cons_val_one] using hA ![a, b]
  rw [heval, heval, heval]
  simpa only [Matrix.vecCons] using A.cons_add ![z] v w

def chartRicciForm (hM04 : RicciFlowCurvatureTheory.{u})
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (q : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := by
  let y := (extChartAt (𝓡 n) x).symm q
  let R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun v w ↦ D.ricci y (chartFrame x v y) (chartFrame x w y)
  have hsym (v w : EuclideanSpace ℝ (Fin n)) : R v w = R w v :=
    ((hM04.tensor_calculus n M g D).2.2.2.1 y
      (chartFrame x v y) (chartFrame x w y) 0 0).2.2.2
  have hadd (v w z : EuclideanSpace ℝ (Fin n)) : R (v + w) z = R v z + R w z := by
    dsimp only [R, chartFrame]
    rw [map_add]
    exact ricci_add_left_of_curvatureTheory hM04 D y _ _ _
  have hsmul (a : ℝ) (v w : EuclideanSpace ℝ (Fin n)) : R (a • v) w = a • R v w := by
    dsimp only [R, chartFrame]
    rw [map_smul, ricci_smul_left_of_curvatureTheory hM04, smul_eq_mul]
  let B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ R hadd hsmul
      (fun v w z ↦ by rw [hsym v (w + z), hadd, hsym w v, hsym z v])
      (fun a v w ↦ by rw [hsym v (a • w), hsmul, hsym w v])
  exact LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).toLinearMap.comp B)

theorem chartRicciForm_apply (hM04 : RicciFlowCurvatureTheory.{u})
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (q v w : EuclideanSpace ℝ (Fin n)) :
    chartRicciForm hM04 D x q v w =
      D.ricci ((extChartAt (𝓡 n) x).symm q)
        (chartFrame x v ((extChartAt (𝓡 n) x).symm q))
        (chartFrame x w ((extChartAt (𝓡 n) x).symm q)) := rfl

theorem chartRicciForm_at (hM04 : RicciFlowCurvatureTheory.{u})
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v w : EuclideanSpace ℝ (Fin n)) :
    chartRicciForm hM04 D x (extChartAt (𝓡 n) x y) v w =
      D.ricci y (chartFrame x v y) (chartFrame x w y) := by
  rw [chartRicciForm_apply, (extChartAt (𝓡 n) x).left_inv
    (show y ∈ (extChartAt (𝓡 n) x).source by simpa only [extChartAt_source] using hy)]

theorem chartRicciForm_contDiffOn (hM04 : RicciFlowCurvatureTheory.{u})
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M) :
    ContDiffOn ℝ ∞ (chartRicciForm hM04 D x) (extChartAt (𝓡 n) x).target := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  have h := ((hM04.tensor_calculus n M g D).2.1).2
    (chartAt (EuclideanSpace ℝ (Fin n)) x).source
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
    ![chartFrame x v, chartFrame x w] (by
      intro i
      fin_cases i
      · exact chartFrame_contMDiffOn x v
      · exact chartFrame_contMDiffOn x w)
  have hi := contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) x
  have hc := h.comp hi (fun q hq ↦ by
    simpa only [extChartAt_source, mem_preimage] using (extChartAt (𝓡 n) x).map_target hq)
  simpa only [Function.comp_def, chartRicciForm_apply, LeviCivitaData.ricciEvaluation,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hc.contDiffOn

theorem ricciDerivativePairing_expand {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (y : M) (v w z : TangentSpace (𝓡 n) y) :
    ricciDerivativePairing D y v w z =
      mvfderiv (𝓡 n) (fun p ↦ D.ricci p
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w p)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z p)) y v -
      D.ricci y (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) y v) z -
      D.ricci y w (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) y v) := by
  simp [ricciDerivativePairing, LeviCivitaData.covariantTensorDerivative,
    LeviCivitaData.ricciEvaluation, Fin.sum_univ_two, Function.update_apply,
    sub_add_eq_sub_sub]

set_option maxHeartbeats 1800000 in
theorem ricciDerivativePairing_chart {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (v w z : EuclideanSpace ℝ (Fin n)) :
    ricciDerivativePairing (F.connection (T - s ^ 2)) y
        (chartFrame x v y) (chartFrame x w y) (chartFrame x z y) =
      fderiv ℝ (chartRicciForm hM04 (F.connection (T - s ^ 2)) x)
        (extChartAt (𝓡 n) x y) v w z -
      chartRicciForm hM04 (F.connection (T - s ^ 2)) x (extChartAt (𝓡 n) x y)
        (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) v w) z -
      chartRicciForm hM04 (F.connection (T - s ^ 2)) x (extChartAt (𝓡 n) x y)
        w (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) v z) := by
  let e := extChartAt (𝓡 n) x
  let D := F.connection (T - s ^ 2)
  let B := chartRicciForm hM04 D x
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (chartFrame x w y)
  let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (chartFrame x z y)
  let c := sectionModel x Y
  let d := sectionModel x Z
  let H : M → ℝ := fun p ↦ D.ricci p (Y p) (Z p)
  let H₀ := fun q ↦ B q (c q) (d q)
  have hy' : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have ht := e.map_source hy'
  have hinv := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) x _ ht).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds ht)
  have hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p (Y p)) y :=
    FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (chartFrame x w y)
  have hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p (Z p)) y :=
    FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (chartFrame x z y)
  have hc : DifferentiableAt ℝ c (e y) := (sectionModel_contDiffAt hy Y hY).differentiableAt (by simp)
  have hd : DifferentiableAt ℝ d (e y) := (sectionModel_contDiffAt hy Z hZ).differentiableAt (by simp)
  have hc₀ : c (e y) = w := sectionModel_at_chartFrame hy w
  have hd₀ : d (e y) = z := sectionModel_at_chartFrame hy z
  have hrep (X : ∀ p : M, TangentSpace (𝓡 n) p) :
      ∀ᶠ p in 𝓝 y, X p = chartFrame x (sectionModel x X (e p)) p := by
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy] with p hp
    exact (chartFrame_sectionModel hp X).symm
  have hB : DifferentiableAt ℝ B (e y) :=
    (((chartRicciForm_contDiffOn hM04 D x) _ ht).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds ht)).differentiableAt (by simp)
  have hH₀ := (hB.hasFDerivAt.clm_apply hc.hasFDerivAt).clm_apply hd.hasFDerivAt
  have hHrep : H =ᶠ[𝓝 y] H₀ ∘ e := by
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy,
      hrep Y, hrep Z] with p hp hpY hpZ
    dsimp only [H, H₀, Function.comp_def]
    rw [hpY, hpZ]
    exact (chartRicciForm_at hM04 D hp _ _).symm
  have hH : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) H y :=
    ((hH₀.differentiableAt.mdifferentiableAt).comp y
      ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hy).mdifferentiableAt (by simp))).congr_of_eventuallyEq hHrep
  have heq : H ∘ e.symm =ᶠ[𝓝 (e y)] H₀ := by
    have hcont : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
      have hh : Tendsto e.symm (𝓝 (e y)) (𝓝 (e.symm (e y))) := hinv.continuousAt.tendsto
      rwa [e.left_inv hy'] at hh
    filter_upwards [hcont hHrep, (isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds ht]
      with q hq hqt
    change H (e.symm q) = H₀ (e (e.symm q)) at hq
    simpa only [Function.comp_def, e.right_inv hqt] using hq
  have hHderiv := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ A v)
    (heq.fderiv_eq (𝕜 := ℝ))
  rw [chart_scalar_fderiv_apply hy H hH, hH₀.fderiv] at hHderiv
  simp only [add_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    hc₀, hd₀] at hHderiv
  have hconnY := connection_chart_section F T htime hy hs Y hY c hc (hrep Y) v
  have hconnZ := connection_chart_section F T htime hy hs Z hZ d hd (hrep Z) v
  rw [hc₀] at hconnY
  rw [hd₀] at hconnZ
  rw [ricciDerivativePairing_expand]
  change mvfderiv (𝓡 n) H y (chartFrame x v y) -
    D.ricci y (D.connection Y y (chartFrame x v y)) (chartFrame x z y) -
    D.ricci y (chartFrame x w y) (D.connection Z y (chartFrame x v y)) = _
  rw [hHderiv, hconnY, hconnZ, ← chartRicciForm_at hM04 D hy,
    ← chartRicciForm_at hM04 D hy]
  dsimp only [B, D, e]
  simp only [map_add, add_apply]
  ring

end PoincareConjecture.M08
