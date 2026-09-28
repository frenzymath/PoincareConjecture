import PoincareConjecture.Proofs.M09.FrozenChartCoordinates
import PoincareConjecture.Proofs.M09.BilinearFamily
import PoincareConjecture.Definitions.Ch01.TensorRegularity

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem mvfderiv_clm_application
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : M → V →L[ℝ] W) (c : M → V) (q : M)
    (hB : MDifferentiableAt (𝓡 n) (𝓘(ℝ, V →L[ℝ] W)) B q)
    (hc : MDifferentiableAt (𝓡 n) (𝓘(ℝ, V)) c q) (X : TangentSpace (𝓡 n) q) :
    mvfderiv (𝓡 n) (fun x ↦ B x (c x)) q X =
      B q (mvfderiv (𝓡 n) c q X) + mvfderiv (𝓡 n) B q X (c q) := by
  let z := (B q, c q)
  have he := (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).clm_apply
    (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  have hp : HasMFDerivAt (𝓡 n) (𝓘(ℝ, (V →L[ℝ] W) × V))
      (fun x ↦ (B x, c x)) q ((mvfderiv (𝓡 n) B q).prod (mvfderiv (𝓡 n) c q)) := by
    convert! hB.hasMFDerivAt.prodMk hc.hasMFDerivAt using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have h := he.hasMFDerivAt.comp q hp
  convert! congrArg (fun L : TangentSpace (𝓡 n) q →L[ℝ] W ↦ L X) h.mfderiv using 1

noncomputable def chartTensorBilinear (T : CovariantTensorEvaluation n M 2)
    (hT : IsSmoothCovariantTensor T) (p q : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  bilinearOfMultilinear ((hT.1 q).choose.compLinearMap
    (fun _ ↦ (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) q).inverse.toLinearMap))

set_option backward.isDefEq.respectTransparency false in
theorem chartTensorBilinear_apply (T : CovariantTensorEvaluation n M 2)
    (hT : IsSmoothCovariantTensor T) (p q : M) (v w : E) :
    chartTensorBilinear T hT p q v w =
      T q ![chartVectorField p v q, chartVectorField p w q] := by
  rw [chartTensorBilinear, bilinearOfMultilinear_apply, MultilinearMap.compLinearMap_apply,
    ← (hT.1 q).choose_spec]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem chartTensorBilinear_smooth (T : CovariantTensorEvaluation n M 2)
    (hT : IsSmoothCovariantTensor T) (p : M) :
    ContMDiffOn (𝓡 n) (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞ (chartTensorBilinear T hT p)
      (chartAt E p).source := by
  apply contMDiffOn_bilinear_iff.mpr
  intro v w
  have h := hT.2 (chartAt E p).source (chartAt E p).open_source
    (fun i ↦ chartVectorField p (![v, w] i)) (fun i ↦ chartVectorField_smooth p _)
  apply h.congr
  intro x _
  rw [chartTensorBilinear_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem covariantTensorDerivative_fixedChart {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (T : CovariantTensorEvaluation n M 2)
    (hT : IsSmoothCovariantTensor T) (p q : M) (hq : q ∈ (chartAt E p).source)
    (X : TangentSpace (𝓡 n) q) (A : E →L[ℝ] E)
    (hA : ∀ v : E, D.connection (chartVectorField p v) q X = chartVectorField p (A v) q)
    (v w : E) :
    D.covariantTensorDerivative T q ![X, chartVectorField p v q, chartVectorField p w q] =
      mvfderiv (𝓡 n) (chartTensorBilinear T hT p) q X v w -
        chartTensorBilinear T hT p q (A v) w - chartTensorBilinear T hT p q v (A w) := by
  classical
  let V := chartVectorField p v q
  let W := chartVectorField p w q
  let c := frozenChartCoordinates p q V
  let d := frozenChartCoordinates p q W
  let B := chartTensorBilinear T hT p
  have hc := (frozenChartCoordinates_contMDiffAt p q hq V).mdifferentiableAt (by simp)
  have hd := (frozenChartCoordinates_contMDiffAt p q hq W).mdifferentiableAt (by simp)
  have hB := ((chartTensorBilinear_smooth T hT p).contMDiffAt
    ((chartAt E p).open_source.mem_nhds hq)).mdifferentiableAt (by simp)
  have hcv : c q = v := frozenChartCoordinates_at_base p q hq v
  have hdw : d q = w := frozenChartCoordinates_at_base p q hq w
  have heq : (fun x ↦ T x ![FiberBundle.extend E V x, FiberBundle.extend E W x]) =ᶠ[𝓝 q]
      (fun x ↦ B x (c x) (d x)) := by
    filter_upwards [(chartAt E p).open_source.mem_nhds hq] with x hx
    rw [chartTensorBilinear_apply, frozenChartCoordinates_reconstruct p q x V hx,
      frozenChartCoordinates_reconstruct p q x W hx]
  have hder : mvfderiv (𝓡 n)
      (fun x ↦ T x ![FiberBundle.extend E V x, FiberBundle.extend E W x]) q X =
      B q v (mvfderiv (𝓡 n) d q X) + B q (mvfderiv (𝓡 n) c q X) w +
        mvfderiv (𝓡 n) B q X v w := by
    rw [mvfderiv, heq.mfderiv_eq]
    change mvfderiv (𝓡 n) (fun x ↦ B x (c x) (d x)) q X = _
    rw [mvfderiv_clm_application (fun x ↦ B x (c x)) d q (hB.clm_apply hc) hd X,
      mvfderiv_clm_application B c q hB hc X, hcv, hdw, ContinuousLinearMap.add_apply]
    ring
  have hup0 (a : TangentSpace (𝓡 n) q) : Function.update ![V, W] (0 : Fin 2) a = ![a, W] := by
    funext i
    fin_cases i <;> simp
  have hup1 (a : TangentSpace (𝓡 n) q) : Function.update ![V, W] (1 : Fin 2) a = ![V, a] := by
    funext i
    fin_cases i <;> simp
  have htail : (fun i : Fin 2 ↦ ![X, V, W] i.succ) = ![V, W] := rfl
  have hfields : (fun x ↦ T x (fun i : Fin 2 ↦ FiberBundle.extend E (![V, W] i) x)) =
      (fun x ↦ T x ![FiberBundle.extend E V x, FiberBundle.extend E W x]) := by
    funext x
    congr 1
    funext i
    fin_cases i <;> rfl
  unfold LeviCivitaData.covariantTensorDerivative
  change mvfderiv (𝓡 n)
      (fun x ↦ T x (fun i : Fin 2 ↦ FiberBundle.extend E (![X, V, W] i.succ) x)) q X -
      (∑ i : Fin 2, T q (Function.update (fun j : Fin 2 ↦ ![X, V, W] j.succ) i
        (D.connection (FiberBundle.extend E (![X, V, W] i.succ)) q X))) = _
  simp only [Matrix.cons_val_succ]
  rw [hfields, Fin.sum_univ_two, hup0, hup1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [connection_frozenChartCoordinates D p q hq X A hA v,
    connection_frozenChartCoordinates D p q hq X A hA w]
  rw [← chartTensorBilinear_apply T hT p q _ w, ← chartTensorBilinear_apply T hT p q v _, hder]
  simp only [map_add, ContinuousLinearMap.add_apply]
  ring

end PoincareConjecture.Proofs.M09
