import PoincareConjecture.Proofs.M09.FrozenFrame
import PoincareConjecture.Proofs.M09.BilinearFamily
import PoincareConjecture.Definitions.Ch01.TensorRegularity








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

noncomputable def tensorBilinear (g : RiemannianMetric n M)
    (T : CovariantTensorEvaluation n M 2) (hT : IsSmoothCovariantTensor T) (q : M) :
    TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (𝓡 n) q →L[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) q) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) q
  exact bilinearOfMultilinear (hT.1 q).choose

theorem tensorBilinear_apply (g : RiemannianMetric n M)
    (T : CovariantTensorEvaluation n M 2) (hT : IsSmoothCovariantTensor T) (q : M)
    (v w : TangentSpace (𝓡 n) q) : tensorBilinear g T hT q v w = T q ![v, w] := by
  simp only [tensorBilinear, bilinearOfMultilinear_apply]
  exact ((hT.1 q).choose_spec ![v, w]).symm

noncomputable def frameMetricForm (g : RiemannianMetric n M) (p q : M) :
    TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p →L[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (g.inner q).bilinearComp (extensionMap p q) (extensionMap p q)

theorem frameMetricForm_apply (g : RiemannianMetric n M) (p q : M)
    (v w : TangentSpace (𝓡 n) p) :
    frameMetricForm g p q v w = g.inner q (extensionMap p q v) (extensionMap p q w) := rfl

theorem frameMetricForm_self (g : RiemannianMetric n M) (p : M) :
    frameMetricForm g p p = g.inner p := by
  ext v w
  simp only [frameMetricForm_apply, extensionMap_self, ContinuousLinearMap.id_apply]

noncomputable def frameTensorForm (g : RiemannianMetric n M)
    (T : CovariantTensorEvaluation n M 2) (hT : IsSmoothCovariantTensor T) (p q : M) :
    TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p →L[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (tensorBilinear g T hT q).bilinearComp (extensionMap p q) (extensionMap p q)

theorem frameTensorForm_apply (g : RiemannianMetric n M)
    (T : CovariantTensorEvaluation n M 2) (hT : IsSmoothCovariantTensor T) (p q : M)
    (v w : TangentSpace (𝓡 n) p) :
    frameTensorForm g T hT p q v w = T q ![extensionMap p q v, extensionMap p q w] :=
  tensorBilinear_apply g T hT q _ _

theorem frameTensorForm_self (g : RiemannianMetric n M)
    (T : CovariantTensorEvaluation n M 2) (hT : IsSmoothCovariantTensor T) (p : M) :
    frameTensorForm g T hT p p = tensorBilinear g T hT p := by
  ext v w
  simp only [frameTensorForm_apply, tensorBilinear_apply, extensionMap_self,
    ContinuousLinearMap.id_apply]

theorem frameMetricForm_smooth (g : RiemannianMetric n M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ContMDiffOn (𝓡 n) (𝓘(ℝ, TangentSpace (𝓡 n) p →L[ℝ]
      TangentSpace (𝓡 n) p →L[ℝ] ℝ)) ∞ (frameMetricForm g p)
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  apply contMDiffOn_bilinear_iff.mpr
  intro v w
  have h := g.contMDiff.contMDiffOn.clm_bundle_apply₂
    (extensionMap_smooth p v) (extensionMap_smooth p w)
  intro q hq
  exact (Bundle.contMDiffWithinAt_totalSpace.mp (h q hq)).2

theorem frameTensorForm_smooth (g : RiemannianMetric n M)
    (T : CovariantTensorEvaluation n M 2) (hT : IsSmoothCovariantTensor T) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ContMDiffOn (𝓡 n) (𝓘(ℝ, TangentSpace (𝓡 n) p →L[ℝ]
      TangentSpace (𝓡 n) p →L[ℝ] ℝ)) ∞ (frameTensorForm g T hT p)
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  apply contMDiffOn_bilinear_iff.mpr
  intro v w
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have h := hT.2 e.baseSet e.open_baseSet
    (fun i q ↦ extensionMap p q (![v, w] i)) (fun i ↦ extensionMap_smooth p _)
  have heq : (fun q ↦ frameTensorForm g T hT p q v w) =
      (fun q ↦ T q (fun i ↦ extensionMap p q (![v, w] i))) := by
    funext q
    rw [frameTensorForm_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact h

theorem frameMetricForm_derivative {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) (X v w : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) (fun q ↦ frameMetricForm g p q v w) p X =
      g.inner p (frozenConnectionEndomorphism D p X v) w +
        g.inner p v (frozenConnectionEndomorphism D p X w) :=
  extensionMetric_derivative D p X v w

theorem frameTensorForm_derivative {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (T : CovariantTensorEvaluation n M 2)
    (hT : IsSmoothCovariantTensor T) (p : M) (X v w : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) (fun q ↦ frameTensorForm g T hT p q v w) p X =
      D.covariantTensorDerivative T p ![X, v, w] +
        T p ![frozenConnectionEndomorphism D p X v, w] +
        T p ![v, frozenConnectionEndomorphism D p X w] := by
  have h := extensionTensor_derivative D T p X ![v, w]
  have heq : (fun q ↦ T q (fun i ↦ extensionMap p q (![v, w] i))) =
      (fun q ↦ frameTensorForm g T hT p q v w) := by
    funext q
    rw [frameTensorForm_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [heq] at h
  have hzero (a : TangentSpace (𝓡 n) p) : Function.update ![v, w] (0 : Fin 2) a = ![a, w] := by
    funext i
    fin_cases i <;> simp
  have hone (a : TangentSpace (𝓡 n) p) : Function.update ![v, w] (1 : Fin 2) a = ![v, a] := by
    funext i
    fin_cases i <;> simp
  simpa [Fin.sum_univ_two, hzero, hone, add_assoc] using h

end PoincareConjecture.Proofs.M09
