import PoincareConjecture.Proofs.M09.CurvatureSlice
import PoincareConjecture.Proofs.M09.TensorTrace
import PoincareConjecture.Statements.Ch04.CurvatureTheory








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators Topology RealInnerProductSpace

open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}

theorem frameCurvatureSlice_trace (D : LeviCivitaData g)
    (hR : IsSmoothCovariantTensor D.riemannEvaluation) (p : M)
    (v w : TangentSpace (𝓡 n) p) (q : M)
    (hq : q ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p).baseSet) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) p
    metricFormTrace (frameMetricForm g p q) (frameCurvatureSlice D hR p v w q) =
      D.ricci q (extensionMap p q v) (extensionMap p q w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) q) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) q
  have h := metricFormTrace_pullback (extensionEquiv p q hq) (frameMetricForm g p q)
    (by intro a b; rw [frameMetricForm_apply]; rw [← extensionEquiv_coe p q hq]; rfl)
    (curvatureSliceBilinear D hR q (extensionMap p q v) (extensionMap p q w))
    (g.orthonormalBasis q)
  rw [extensionEquiv_coe] at h
  simpa only [frameCurvatureSlice, curvatureSliceBilinear_apply, LeviCivitaData.ricci]
    using! h

theorem ricciExtension_mvfderiv (D : LeviCivitaData g)
    (hR : IsSmoothCovariantTensor D.riemannEvaluation) (p : M)
    (X v w : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) (fun q ↦ D.ricci q (extensionMap p q v) (extensionMap p q w)) p X =
      (∑ i, D.covariantTensorDerivative D.riemannEvaluation p
        ![X, v, g.orthonormalBasis p i, w, g.orthonormalBasis p i]) +
      D.ricci p (frozenConnectionEndomorphism D p X v) w +
      D.ricci p v (frozenConnectionEndomorphism D p X w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hp : e.baseSet ∈ 𝓝 p :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' p)
  let G := frameMetricForm g p
  let B := frameCurvatureSlice D hR p v w
  let P := frozenConnectionEndomorphism D p X
  have hG := ((frameMetricForm_smooth g p).contMDiffAt hp).mdifferentiableAt (by simp)
  have hB := ((frameCurvatureSlice_smooth D hR p v w).contMDiffAt hp).mdifferentiableAt
    (by simp)
  let C := mvfderiv (𝓡 n) B p X -
    (B p).bilinearComp P (ContinuousLinearMap.id ℝ _) -
    (B p).bilinearComp (ContinuousLinearMap.id ℝ _) P
  have heval (f : M → TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p →L[ℝ] ℝ)
      (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, TangentSpace (𝓡 n) p →L[ℝ]
        TangentSpace (𝓡 n) p →L[ℝ] ℝ)) f p) (a b : TangentSpace (𝓡 n) p) :
      mvfderiv (𝓡 n) (fun q ↦ f q a b) p X = mvfderiv (𝓡 n) f p X a b := by
    exact mvfderiv_const_clm
      ((ContinuousLinearMap.apply ℝ ℝ b).comp
        (ContinuousLinearMap.apply ℝ (TangentSpace (𝓡 n) p →L[ℝ] ℝ) a)) f p hf X
  have hC (a b : TangentSpace (𝓡 n) p) :
      C a b = D.covariantTensorDerivative D.riemannEvaluation p ![X, v, a, w, b] +
        D.curvatureTensor p (P v) a w b + D.curvatureTensor p v a (P w) b := by
    dsimp only [C]
    simp only [sub_apply, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.id_apply]
    rw [← heval B hB, frameCurvatureSlice_derivative D hR]
    simp only [B, frameCurvatureSlice_self, curvatureSliceBilinear_apply, P]
    ring
  have hunit : IsUnit (formOperator (G p)) := by
    dsimp only [G]
    rw [formOperator_frameMetricForm_self]
    exact isUnit_one
  have hder := metricFormTrace_mvfderiv G B p X hG hB hunit P C
    (by
      intro a b
      rw [← heval G hG, frameMetricForm_derivative D]
      simp only [G, frameMetricForm_self, P])
    (by
      intro a b
      dsimp only [C]
      simp only [sub_apply, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.id_apply]
      ring)
  have heq : (fun q ↦ D.ricci q (extensionMap p q v) (extensionMap p q w)) =ᶠ[𝓝 p]
      (fun q ↦ metricFormTrace (G q) (B q)) := by
    filter_upwards [hp] with q hq
    exact (frameCurvatureSlice_trace D hR p v w q hq).symm
  rw [mvfderiv, heq.mfderiv_eq]
  change mvfderiv (𝓡 n) (fun q ↦ metricFormTrace (G q) (B q)) p X = _
  rw [hder, metricFormTrace]
  dsimp only [G]
  rw [formOperator_frameMetricForm_self, Ring.inverse_one, one_mul,
    continuousTrace_formOperator _ (g.orthonormalBasis p)]
  simp_rw [hC, Finset.sum_add_distrib]
  rfl

theorem covariantRicci_eq_contraction (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (p : M) (X v w : TangentSpace (𝓡 n) p) :
    D.covariantTensorDerivative D.ricciEvaluation p ![X, v, w] =
      ∑ i, D.covariantTensorDerivative D.riemannEvaluation p
        ![X, v, g.orthonormalBasis p i, w, g.orthonormalBasis p i] := by
  have hR := (hM04.tensor_calculus n M g D).1
  have hRic := (hM04.tensor_calculus n M g D).2.1
  have h := frameTensorForm_derivative D D.ricciEvaluation hRic p X v w
  simp only [frameTensorForm_apply, LeviCivitaData.ricciEvaluation,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [ricciExtension_mvfderiv D hR] at h
  linarith

theorem scalarCurvature_mvfderiv_contraction (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (p : M) (X : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) D.scalarCurvature p X =
      ∑ i, ∑ j, D.covariantTensorDerivative D.riemannEvaluation p
        ![X, g.orthonormalBasis p i, g.orthonormalBasis p j,
          g.orthonormalBasis p i, g.orthonormalBasis p j] := by
  have h := tensorMetricTrace_mvfderiv D D.ricciEvaluation
    (hM04.tensor_calculus n M g D).2.1 p X
  simp_rw [covariantRicci_eq_contraction hM04 D] at h
  change mvfderiv (𝓡 n) D.scalarCurvature p X = _ at h
  exact h

end PoincareConjecture.Proofs.M09
