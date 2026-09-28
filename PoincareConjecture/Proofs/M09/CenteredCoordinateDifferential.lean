import PoincareConjecture.Proofs.M09.CenteredChartOperators
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Definitions.Ch06.LGeometry









set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_chartAt_self (p : M) :
    mfderiv (𝓡 n) (𝓡 n) (chartAt E p) p = ContinuousLinearMap.id ℝ E := by
  convert! mfderiv_extChartAt_self (I := 𝓡 n) (x := p) using 1

set_option backward.isDefEq.respectTransparency false in
theorem mvfderiv_centeredChart_of_eventuallyEq (p : M) (f : M → ℝ) (φ : E → ℝ)
    (hφ : DifferentiableAt ℝ φ ((chartAt E p) p))
    (heq : f =ᶠ[𝓝 p] (fun q ↦ φ ((chartAt E p) q))) (U : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) f p U = fderiv ℝ φ ((chartAt E p) p) U := by
  have hc := (mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt (mem_chart_source E p)
  have h := (hφ.mdifferentiableAt.hasMFDerivAt.comp p hc.hasMFDerivAt).mfderiv
  rw [mfderiv_eq_fderiv] at h
  change mfderiv (𝓡 n) (𝓘(ℝ, ℝ)) (fun q ↦ φ ((chartAt E p) q)) p =
    (fderiv ℝ φ ((chartAt E p) p)).comp (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) p) at h
  rw [mvfderiv, heq.mfderiv_eq, h, mfderiv_chartAt_self]
  rfl

theorem covariantTensorDerivative_centeredCoordinates {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {k : ℕ} (T : CovariantTensorEvaluation n M k)
    (hT : IsSmoothCovariantTensor T) (p : M) (X : TangentSpace (𝓡 n) p)
    (v : Fin k → TangentSpace (𝓡 n) p) :
    D.covariantTensorDerivative T p (Fin.cons X v) =
      fderiv ℝ (fun y : E ↦ T ((chartAt E p).symm y)
        (fun i ↦ chartVectorField p (v i) ((chartAt E p).symm y))) ((chartAt E p) p) X -
        ∑ i, T p (Function.update v i (D.connection (chartVectorField p (v i)) p X)) := by
  let f : M → ℝ := fun q ↦ T q (fun i ↦ chartVectorField p (v i) q)
  let φ : E → ℝ := fun y ↦ f ((chartAt E p).symm y)
  have hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f (chartAt E p).source :=
    hT.2 _ (chartAt E p).open_source (fun i ↦ chartVectorField p (v i))
      (fun i ↦ chartVectorField_smooth p (v i))
  have hφ : ContDiffOn ℝ ∞ φ (chartAt E p).target :=
    (hf.comp contMDiffOn_chart_symm (fun y hy ↦ (chartAt E p).map_target hy)).contDiffOn
  have heq : f =ᶠ[𝓝 p] (fun q ↦ φ ((chartAt E p) q)) := by
    filter_upwards [(chartAt E p).open_source.mem_nhds (mem_chart_source E p)] with q hq
    exact congrArg f ((chartAt E p).left_inv hq).symm
  rw [covariantTensorDerivative_centeredChart]
  exact congrArg (· - ∑ i, T p (Function.update v i
    (D.connection (chartVectorField p (v i)) p X)))
      (mvfderiv_centeredChart_of_eventuallyEq p f φ
        ((hφ.contDiffAt ((chartAt E p).open_target.mem_nhds
          ((chartAt E p).map_source (mem_chart_source E p)))).differentiableAt (by simp)) heq X)

theorem ricciDerivativePairing_centeredCoordinates (hM04 : RicciFlowCurvatureTheory.{u})
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (p : M)
    (U V W : TangentSpace (𝓡 n) p) :
    ricciDerivativePairing D p U V W =
      fderiv ℝ (fun y : E ↦ D.ricci ((chartAt E p).symm y)
        (chartVectorField p V ((chartAt E p).symm y))
        (chartVectorField p W ((chartAt E p).symm y))) ((chartAt E p) p) U -
        D.ricci p (D.connection (chartVectorField p V) p U) W -
        D.ricci p V (D.connection (chartVectorField p W) p U) := by
  have h := covariantTensorDerivative_centeredCoordinates D D.ricciEvaluation
    (hM04.tensor_calculus n M g D).2.1 p U ![V, W]
  have hzero (a : TangentSpace (𝓡 n) p) :
      Function.update ![V, W] (0 : Fin 2) a = ![a, W] := by
    funext i
    fin_cases i <;> simp
  have hone (a : TangentSpace (𝓡 n) p) :
      Function.update ![V, W] (1 : Fin 2) a = ![V, a] := by
    funext i
    fin_cases i <;> simp
  simpa [ricciDerivativePairing, Fin.sum_univ_two, hzero, hone,
    LeviCivitaData.ricciEvaluation, sub_add_eq_sub_sub] using h

end PoincareConjecture.Proofs.M09
