import PoincareConjecture.Proofs.M09.CenteredHessian
import PoincareConjecture.Proofs.M09.SquareChartCurvature
import PoincareConjecture.Proofs.M09.BasisContractions
import PoincareConjecture.Proofs.M09.TensorTrace
import PoincareConjecture.Statements.Ch04.CurvatureTheory

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem squareTime_hessian_exists_bilinear {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (f : M → ℝ) (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f (chartAt E p).source) :
    ∃ H : E →L[ℝ] E →L[ℝ] ℝ,
      ∀ U V : E, (F.connection (T - s ^ 2)).hessian f p U V = H U V := by
  let φ : E → ℝ := fun y ↦ f ((chartAt E p).symm y)
  let y0 := (chartAt E p) p
  let C := coordinateConnectionBilinear (squareChartMetric F T p) (s, y0)
  have hφ : ContDiffOn ℝ ∞ φ (chartAt E p).target :=
    (hf.comp contMDiffOn_chart_symm (fun y hy ↦ (chartAt E p).map_target hy)).contDiffOn
  have hy : y0 ∈ (chartAt E p).target := (chartAt E p).map_source (mem_chart_source E p)
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) y0 :=
    (((hφ.contDiffAt ((chartAt E p).open_target.mem_nhds hy)).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp))
  let H : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ φ) y0 -
    (ContinuousLinearMap.compL ℝ E E ℝ (fderiv ℝ φ y0)).comp C
  refine ⟨H, ?_⟩
  intro U V
  have hd : fderiv ℝ (fun y ↦ fderiv ℝ φ y V) y0 U =
      fderiv ℝ (fderiv ℝ φ) y0 U V := by
    have h := hD.hasFDerivAt.clm_apply (hasFDerivAt_const V y0)
    simpa using congrArg (fun L : E →L[ℝ] ℝ ↦ L U) h.fderiv
  rw [hessian_centeredCoordinates (F.connection (T - s ^ 2)) f p hf U V]
  change fderiv ℝ (fun y ↦ fderiv ℝ φ y V) y0 U -
    fderiv ℝ φ y0 ((F.connection (T - s ^ 2)).connection (chartVectorField p V) p U) = H U V
  rw [hd, ← squareChartConnection_at_center F T b hb hwindow p s hs U V]
  rfl

theorem squareTime_laplacian_orthonormal_trace {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (f : M → ℝ) (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f (chartAt E p).source)
    {ι : Type*} [Fintype ι] :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
    ∀ e : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) p),
      (∑ i, (F.connection (T - s ^ 2)).hessian f p (e i) (e i)) =
        (F.connection (T - s ^ 2)).laplacian f p := by
  obtain ⟨H, hH⟩ := squareTime_hessian_exists_bilinear F T b hb hwindow p s hs f hf
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 n) : M → Type _) p
  let L : TangentSpace (𝓡 n) p →ₗ[ℝ] TangentSpace (𝓡 n) p →ₗ[ℝ] ℝ := {
    toFun := fun v ↦ (H v).toLinearMap
    map_add' := by intro v w; ext z; exact congrArg (fun B : E →L[ℝ] ℝ ↦ B z) (H.map_add v w)
    map_smul' := by intro c v; ext z; exact congrArg (fun B : E →L[ℝ] ℝ ↦ B z) (H.map_smul c v)
  }
  let B : TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p →L[ℝ] ℝ :=
    ((LinearMap.toContinuousLinearMap : (TangentSpace (𝓡 n) p →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      (TangentSpace (𝓡 n) p →L[ℝ] ℝ)).toLinearMap.comp L).toContinuousLinearMap
  intro e
  have h := bilinear_trace_basis_eq B e ((F.metric (T - s ^ 2)).orthonormalBasis p)
  change (∑ i, H (e i) (e i)) =
    ∑ j, H ((F.metric (T - s ^ 2)).orthonormalBasis p j)
      ((F.metric (T - s ^ 2)).orthonormalBasis p j) at h
  change (∑ i, (F.connection (T - s ^ 2)).hessian f p (e i) (e i)) =
    ∑ j, (F.connection (T - s ^ 2)).hessian f p
      ((F.metric (T - s ^ 2)).orthonormalBasis p j)
      ((F.metric (T - s ^ 2)).orthonormalBasis p j)
  exact (Finset.sum_congr rfl (fun i _ ↦ hH (e i) (e i))).trans
    (h.trans (Finset.sum_congr rfl (fun j _ ↦ hH _ _)).symm)

theorem scalarCurvature_contMDiff (hM04 : RicciFlowCurvatureTheory.{u})
    {g : RiemannianMetric n M} (D : LeviCivitaData g) :
    ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ D.scalarCurvature :=
  tensorMetricTrace_smooth g D.ricciEvaluation (hM04.tensor_calculus n M g D).2.1

end PoincareConjecture.Proofs.M09
