import PoincareConjecture.Proofs.M09.FrameForms
import PoincareConjecture.Proofs.M09.ManifoldTraceDerivative

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators Topology RealInnerProductSpace

open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

noncomputable def tensorMetricTrace (g : RiemannianMetric n M)
    (T : CovariantTensorEvaluation n M 2) (q : M) : ℝ :=
  ∑ i, T q ![g.orthonormalBasis q i, g.orthonormalBasis q i]

theorem tensorMetricTrace_eq_frame (g : RiemannianMetric n M)
    (T : CovariantTensorEvaluation n M 2) (hT : IsSmoothCovariantTensor T)
    (p q : M)
    (hq : q ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p).baseSet) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) p
    tensorMetricTrace g T q =
      metricFormTrace (frameMetricForm g p q) (frameTensorForm g T hT p q) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) q) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) q
  have h := metricFormTrace_pullback (extensionEquiv p q hq) (frameMetricForm g p q)
    (by intro v w; rw [frameMetricForm_apply]; rw [← extensionEquiv_coe p q hq]; rfl)
    (tensorBilinear g T hT q) (g.orthonormalBasis q)
  rw [extensionEquiv_coe] at h
  simpa only [tensorMetricTrace, tensorBilinear_apply, frameTensorForm] using! h.symm

theorem formOperator_frameMetricForm_self (g : RiemannianMetric n M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) p
    formOperator (frameMetricForm g p p) =
      (1 : TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  ext v
  apply ext_inner_right ℝ
  intro w
  rw [formOperator_pairing, frameMetricForm_self]
  rfl

theorem tensorMetricTrace_smooth (g : RiemannianMetric n M)
    (T : CovariantTensorEvaluation n M 2) (hT : IsSmoothCovariantTensor T) :
    ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (tensorMetricTrace g T) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro p
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hp : e.baseSet ∈ 𝓝 p :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' p)
  have hG := (frameMetricForm_smooth g p).contMDiffAt hp
  have hB := (frameTensorForm_smooth g T hT p).contMDiffAt hp
  have hunit : IsUnit (formOperator (frameMetricForm g p p)) := by
    rw [formOperator_frameMetricForm_self]
    exact isUnit_one
  have h := (metricFormTrace_contDiffAt _ _ hunit).contMDiffAt.comp p (hG.prodMk_space hB)
  apply h.congr_of_eventuallyEq
  filter_upwards [hp] with q hq
  exact tensorMetricTrace_eq_frame g T hT p q hq

theorem tensorMetricTrace_mvfderiv {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (T : CovariantTensorEvaluation n M 2)
    (hT : IsSmoothCovariantTensor T) (p : M) (X : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) (tensorMetricTrace g T) p X =
      ∑ i, D.covariantTensorDerivative T p ![X, g.orthonormalBasis p i,
        g.orthonormalBasis p i] := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hp : e.baseSet ∈ 𝓝 p :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' p)
  let G := frameMetricForm g p
  let B := frameTensorForm g T hT p
  let P := frozenConnectionEndomorphism D p X
  have hG := ((frameMetricForm_smooth g p).contMDiffAt hp).mdifferentiableAt (by simp)
  have hB := ((frameTensorForm_smooth g T hT p).contMDiffAt hp).mdifferentiableAt (by simp)
  let C := mvfderiv (𝓡 n) B p X -
    (B p).bilinearComp P (ContinuousLinearMap.id ℝ _) -
    (B p).bilinearComp (ContinuousLinearMap.id ℝ _) P
  have heval (f : M → TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p →L[ℝ] ℝ)
      (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, TangentSpace (𝓡 n) p →L[ℝ]
        TangentSpace (𝓡 n) p →L[ℝ] ℝ)) f p) (v w : TangentSpace (𝓡 n) p) :
      mvfderiv (𝓡 n) (fun q ↦ f q v w) p X = mvfderiv (𝓡 n) f p X v w := by
    exact mvfderiv_const_clm
      ((ContinuousLinearMap.apply ℝ ℝ w).comp
        (ContinuousLinearMap.apply ℝ (TangentSpace (𝓡 n) p →L[ℝ] ℝ) v)) f p hf X
  have hC (v w : TangentSpace (𝓡 n) p) :
      C v w = D.covariantTensorDerivative T p ![X, v, w] := by
    dsimp only [C]
    simp only [sub_apply, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.id_apply]
    rw [← heval B hB, frameTensorForm_derivative D T hT]
    simp only [B, frameTensorForm_self, tensorBilinear_apply, P]
    ring
  have hunit : IsUnit (formOperator (G p)) := by
    dsimp only [G]
    rw [formOperator_frameMetricForm_self]
    exact isUnit_one
  have hder := metricFormTrace_mvfderiv G B p X hG hB hunit P C
    (by
      intro v w
      rw [← heval G hG, frameMetricForm_derivative D]
      simp only [G, frameMetricForm_self, P])
    (by
      intro v w
      dsimp only [C]
      simp only [sub_apply, ContinuousLinearMap.bilinearComp_apply,
        ContinuousLinearMap.id_apply]
      ring)
  have heq : tensorMetricTrace g T =ᶠ[𝓝 p] (fun q ↦ metricFormTrace (G q) (B q)) := by
    filter_upwards [hp] with q hq
    exact tensorMetricTrace_eq_frame g T hT p q hq
  rw [mvfderiv, heq.mfderiv_eq]
  change mvfderiv (𝓡 n) (fun q ↦ metricFormTrace (G q) (B q)) p X = _
  rw [hder, metricFormTrace]
  dsimp only [G]
  rw [formOperator_frameMetricForm_self, Ring.inverse_one, one_mul,
    continuousTrace_formOperator _ (g.orthonormalBasis p)]
  exact Finset.sum_congr rfl fun i _ ↦ hC _ _

end PoincareConjecture.Proofs.M09
