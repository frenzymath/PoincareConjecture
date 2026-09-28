import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.MaximumPrinciple.TensorCoordinates
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.MaximumPrinciple.BundleContact

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.TensorFiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {k : ℕ}

def evaluation (a : Fin k → E) : TensorFiber E k →L[ℝ] ℝ :=
  (show TensorFiber E k →ₗ[ℝ] ℝ from
    { toFun := fun T => T a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

@[simp] lemma evaluation_apply (a : Fin k → E) (T : TensorFiber E k) :
    evaluation a T = T a := rfl

lemma contDiffAt_of_evaluation {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {S : H → TensorFiber E k} {x : H}
    (hS : ∀ a, ContDiffAt ℝ ∞ (fun z => S z a) x) :
    ContDiffAt ℝ ∞ S x := by
  let C := components (E := E) k
  have hC : ContDiffAt ℝ ∞ (fun z => C (S z)) x := by
    apply (contDiffAt_piLp 2).2
    intro a
    exact hS _
  have hleft := C.leftInverse.toContinuousLinearMap.contDiff.contDiffAt.comp x hC
  change ContDiffAt ℝ ∞ (fun z => C.leftInverse (C (S z))) x at hleft
  have hker : C.ker = ⊥ := LinearMap.ker_eq_bot.mpr (components_injective k)
  simpa only [LinearMap.leftInverse_apply_of_inj hker] using hleft

lemma fderiv_evaluation {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {S : H → TensorFiber E k} {x : H} (hS : DifferentiableAt ℝ S x)
    (a : Fin k → E) (u : H) :
    fderiv ℝ (fun z => S z a) x u = (fderiv ℝ S x u) a := by
  exact congrArg (fun L => L u) ((evaluation a).hasFDerivAt.comp x hS.hasFDerivAt).fderiv

def slotAction (A : E →L[ℝ] E) (i : Fin k) (T : TensorFiber E k) :
    TensorFiber E k :=
  toMultilinear.symm ((toMultilinear T).compLinearMap
    (Function.update (fun _ => LinearMap.id) i A.toLinearMap))

omit [FiniteDimensional ℝ E] in
@[simp] lemma slotAction_apply (A : E →L[ℝ] E) (i : Fin k)
    (T : TensorFiber E k) (a : Fin k → E) :
    slotAction A i T a = T (Function.update a i (A (a i))) := by
  change T (fun j => Function.update (fun _ => LinearMap.id) i A.toLinearMap j (a j)) = _
  congr 1
  ext j
  by_cases h : j = i <;> simp [h, Function.update_of_ne]

def negativeSlotAction (A : E →L[ℝ] E) : TensorFiber E k →L[ℝ] TensorFiber E k :=
  (show TensorFiber E k →ₗ[ℝ] TensorFiber E k from
    { toFun := fun T => -(∑ i, slotAction A i T)
      map_add' := by
        intro T S
        apply TensorFiber.ext
        intro a
        change evaluation a (-(∑ i, slotAction A i (T + S))) =
          evaluation a (-(∑ i, slotAction A i T) + -(∑ i, slotAction A i S))
        simp only [map_neg, map_sum, map_add, evaluation_apply, slotAction_apply,
          _root_.add_apply, Finset.sum_add_distrib, neg_add_rev]
        ring
      map_smul' := by
        intro c T
        apply TensorFiber.ext
        intro a
        change evaluation a (-(∑ i, slotAction A i (c • T))) =
          evaluation a (c • -(∑ i, slotAction A i T))
        simp only [map_neg, map_sum, map_smul, evaluation_apply, slotAction_apply,
          _root_.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        ring }).toContinuousLinearMap

@[simp] lemma negativeSlotAction_apply (A : E →L[ℝ] E)
    (T : TensorFiber E k) (a : Fin k → E) :
    negativeSlotAction A T a = -∑ i, T (Function.update a i (A (a i))) := by
  change evaluation a (-(∑ i, slotAction A i T)) = _
  simp only [map_neg, map_sum, evaluation_apply, slotAction_apply]

end PoincareConjecture.TensorFiber

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

def tensorCoordinateSection {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (p x : M) :
    TensorFiber (EuclideanSpace ℝ (Fin n)) k :=
  TensorFiber.toMultilinear.symm ((hT.1 x).choose.compLinearMap
    (fun _ => ((trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).symmL ℝ x).toLinearMap))

@[simp] lemma tensorCoordinateSection_apply {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (p x : M) (a : Fin k → EuclideanSpace ℝ (Fin n)) :
    tensorCoordinateSection hT p x a = tensorCoordinateEvaluation p T x a :=
  ((hT.1 x).choose_spec _).symm

lemma contDiffAt_tensorCoordinateSection {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (p : M) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ (extChartAt (𝓡 n) p).target) :
    ContDiffAt ℝ ∞
      (fun w => tensorCoordinateSection hT p ((extChartAt (𝓡 n) p).symm w)) z := by
  apply TensorFiber.contDiffAt_of_evaluation
  intro a
  simp only [tensorCoordinateSection_apply]
  have hx : (extChartAt (𝓡 n) p).symm z ∈
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet := by
    simpa using (extChartAt (𝓡 n) p).map_target hz
  have ht := hT.contMDiffAt_apply
    (fun i => contMDiffAt_constantCoordinateField p (a i) hx)
  have hc := (contMDiffWithinAt_extChartAt_symm_range (I := 𝓡 n) (n := ∞) p hz).contMDiffAt
    (by simp)
  exact (ht.comp z hc).contDiffAt

def tensorCoordinateConnectionCoefficient (D : LeviCivitaData g) (p x : M) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ]
      TensorFiber (EuclideanSpace ℝ (Fin n)) k →L[ℝ]
        TensorFiber (EuclideanSpace ℝ (Fin n)) k :=
  (show EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      TensorFiber (EuclideanSpace ℝ (Fin n)) k →L[ℝ]
        TensorFiber (EuclideanSpace ℝ (Fin n)) k from
    { toFun := fun u => TensorFiber.negativeSlotAction (D.coordinateConnectionCoefficient p x u)
      map_add' := by
        intro u v
        apply ContinuousLinearMap.ext
        intro T
        apply TensorFiber.ext
        intro a
        simp only [add_apply, TensorFiber.negativeSlotAction_apply,
          map_add]
        change -(∑ i, (TensorFiber.toMultilinear T)
          (Function.update a i (_ + _))) = _
        simp only [MultilinearMap.map_update_add, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro c u
        apply ContinuousLinearMap.ext
        intro T
        apply TensorFiber.ext
        intro a
        simp only [smul_apply, TensorFiber.negativeSlotAction_apply,
          map_smul, RingHom.id_apply]
        change -(∑ i, (TensorFiber.toMultilinear T)
          (Function.update a i (c • _))) = _
        simp only [MultilinearMap.map_update_smul, smul_eq_mul, ← Finset.mul_sum]
        ring
    }).toContinuousLinearMap

@[simp] lemma tensorCoordinateConnectionCoefficient_apply
    (D : LeviCivitaData g) (p x : M) {k : ℕ}
    (u : EuclideanSpace ℝ (Fin n)) (T : TensorFiber (EuclideanSpace ℝ (Fin n)) k)
    (a : Fin k → EuclideanSpace ℝ (Fin n)) :
    D.tensorCoordinateConnectionCoefficient p x k u T a =
      -∑ i, T (Function.update a i (D.coordinateConnectionCoefficient p x u (a i))) :=
  TensorFiber.negativeSlotAction_apply _ _ _

theorem covariantDerivative_tensorCoordinateSection_apply (D : LeviCivitaData g)
    {k : ℕ} {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (p : M) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ (extChartAt (𝓡 n) p).target)
    (u : EuclideanSpace ℝ (Fin n)) (a : Fin k → EuclideanSpace ℝ (Fin n)) :
    Poincare.Riemannian.RadialTransport.covariantDerivative
      (fun w => D.tensorCoordinateConnectionCoefficient p ((extChartAt (𝓡 n) p).symm w) k)
      (fun w => tensorCoordinateSection hT p ((extChartAt (𝓡 n) p).symm w)) z u a =
      tensorCoordinateEvaluation p (D.covariantTensorDerivative T)
        ((extChartAt (𝓡 n) p).symm z) (Fin.cons u a) := by
  let e := extChartAt (𝓡 n) p
  have hx : e.symm z ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).baseSet := by
    simpa [e] using e.map_target hz
  have hf := (contDiffAt_tensorCoordinateSection hT p hz).differentiableAt (by simp)
  rw [D.tensorCoordinateDerivative_eq_fderiv_sub hT p hx]
  rw [show extChartAt (𝓡 n) p ((extChartAt (𝓡 n) p).symm z) = z from e.right_inv hz]
  simp only [Poincare.Riemannian.RadialTransport.covariantDerivative,
    TensorFiber.add_apply, tensorCoordinateConnectionCoefficient_apply,
    tensorCoordinateSection_apply, sub_eq_add_neg]
  congr 1
  simpa only [tensorCoordinateSection_apply] using (TensorFiber.fderiv_evaluation hf a u).symm

theorem second_covariantDerivative_tensorCoordinateSection_apply (D : LeviCivitaData g)
    {k : ℕ} {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (p : M) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ (extChartAt (𝓡 n) p).target)
    (u v : EuclideanSpace ℝ (Fin n)) (a : Fin k → EuclideanSpace ℝ (Fin n)) :
    let Γ := fun w => D.tensorCoordinateConnectionCoefficient p
      ((extChartAt (𝓡 n) p).symm w) k
    let S := fun w => tensorCoordinateSection hT p ((extChartAt (𝓡 n) p).symm w)
    Poincare.Riemannian.RadialTransport.covariantDerivative Γ
        (fun w => Poincare.Riemannian.RadialTransport.covariantDerivative Γ S w v) z u a -
      Poincare.Riemannian.RadialTransport.covariantDerivative Γ S z
        (D.coordinateConnectionCoefficient p ((extChartAt (𝓡 n) p).symm z) u v) a =
      tensorCoordinateEvaluation p (D.iteratedCovariantTensorDerivative T 2)
        ((extChartAt (𝓡 n) p).symm z) (Fin.cons u (Fin.cons v a)) := by
  let Γ := fun w => D.tensorCoordinateConnectionCoefficient p
    ((extChartAt (𝓡 n) p).symm w) k
  let S := fun w => tensorCoordinateSection hT p ((extChartAt (𝓡 n) p).symm w)
  let B := fun w => Poincare.Riemannian.RadialTransport.covariantDerivative Γ S w v
  let e := extChartAt (𝓡 n) p
  have hDT := D.covariantTensorDerivative_isSmooth hT
  have heq (b : Fin k → EuclideanSpace ℝ (Fin n)) :
      (fun w => B w b) =ᶠ[𝓝 z]
        (fun w => tensorCoordinateEvaluation p (D.covariantTensorDerivative T)
          (e.symm w) (Fin.cons v b)) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hz] with w hw
    exact D.covariantDerivative_tensorCoordinateSection_apply hT p hw v b
  have hB : ContDiffAt ℝ ∞ B z := by
    apply TensorFiber.contDiffAt_of_evaluation
    intro b
    have h := (TensorFiber.evaluation (Fin.cons v b)).contDiff.contDiffAt.comp z
      (contDiffAt_tensorCoordinateSection hDT p hz)
    have h' : ContDiffAt ℝ ∞
        (fun w => tensorCoordinateEvaluation p (D.covariantTensorDerivative T)
          (e.symm w) (Fin.cons v b)) z := by
      simpa only [Function.comp_def, TensorFiber.evaluation_apply,
        tensorCoordinateSection_apply] using h
    exact h'.congr_of_eventuallyEq (heq b)
  have hder : (fderiv ℝ B z u) a =
      fderiv ℝ (fun w => tensorCoordinateEvaluation p (D.covariantTensorDerivative T)
        (e.symm w) (Fin.cons v a)) z u := by
    rw [← TensorFiber.fderiv_evaluation (hB.differentiableAt (by simp))]
    exact congrArg (fun L => L u) ((heq a).fderiv_eq (𝕜 := ℝ))
  have hx : e.symm z ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).baseSet := by
    simpa [e] using e.map_target hz
  have hDD := D.tensorCoordinateDerivative_eq_fderiv_sub hDT p hx u (Fin.cons v a)
  rw [show extChartAt (𝓡 n) p (e.symm z) = z from e.right_inv hz] at hDD
  change Poincare.Riemannian.RadialTransport.covariantDerivative Γ B z u a - _ = _
  rw [Poincare.Riemannian.RadialTransport.covariantDerivative, TensorFiber.add_apply, hder]
  simp only [Γ, tensorCoordinateConnectionCoefficient_apply]
  change _ + -(∑ i, B z (Function.update a i
    (D.coordinateConnectionCoefficient p (e.symm z) u (a i)))) - _ = _
  simp_rw [show ∀ b, B z b = tensorCoordinateEvaluation p
    (D.covariantTensorDerivative T) (e.symm z) (Fin.cons v b) from
      fun b => D.covariantDerivative_tensorCoordinateSection_apply hT p hz v b]
  rw [D.covariantDerivative_tensorCoordinateSection_apply hT p hz]
  rw [Fin.sum_univ_succ] at hDD
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero] at hDD
  have hupdate (i : Fin k) (w : EuclideanSpace ℝ (Fin n)) :
      Function.update (Fin.cons v a : Fin (k + 1) → EuclideanSpace ℝ (Fin n)) i.succ w =
        Fin.cons v (Function.update a i w) := by rw [Fin.cons_update]
  simp_rw [hupdate] at hDD
  change _ = tensorCoordinateEvaluation p
    (D.covariantTensorDerivative (D.covariantTensorDerivative T)) (e.symm z)
      (Fin.cons u (Fin.cons v a))
  linarith [hDD]

def orthonormalCoordinateDirection (p x : M)
    (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    EuclideanSpace ℝ (Fin n) :=
  (trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) p).continuousLinearMapAt ℝ x (g.orthonormalBasis x i)

def coordinateTensorTrace {k : ℕ} (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M k) (p x : M)
    (a : Fin k → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, tensorCoordinateEvaluation p (D.iteratedCovariantTensorDerivative T 2) x
    (Fin.cons (orthonormalCoordinateDirection (g := g) p x i)
      (Fin.cons (orthonormalCoordinateDirection (g := g) p x i) a))

theorem coordinateTensorTrace_eq_tensorLaplacian {k : ℕ}
    (D : LeviCivitaData g) (T : CovariantTensorEvaluation n M k)
    (p x : M) (a : Fin k → EuclideanSpace ℝ (Fin n))
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).baseSet) :
    D.coordinateTensorTrace T p x a =
      tensorCoordinateEvaluation p (D.tensorLaplacian T) x a := by
  unfold coordinateTensorTrace tensorCoordinateEvaluation
    orthonormalCoordinateDirection tensorLaplacian
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext j
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) p
  have hbase := FiberBundle.mem_baseSet_trivializationAt
    (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  cases j using Fin.cases with
  | zero =>
      exact e.symmL_continuousLinearMapAt (R := ℝ) hx (g.orthonormalBasis x i)
  | succ j =>
      cases j using Fin.cases with
      | zero =>
          exact e.symmL_continuousLinearMapAt (R := ℝ) hx (g.orthonormalBasis x i)
      | succ j =>
          rfl

theorem coordinateRoughLaplacian_tensorCoordinateSection {k : ℕ}
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (p : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).baseSet) :
    Poincare.Riemannian.RadialTransport.coordinateRoughLaplacian
      (fun z => D.tensorCoordinateConnectionCoefficient p ((extChartAt (𝓡 n) p).symm z) k)
      (fun z => tensorCoordinateSection hT p ((extChartAt (𝓡 n) p).symm z))
      (orthonormalCoordinateDirection (g := g) p x)
      (∑ i, D.coordinateConnectionCoefficient p x
        (orthonormalCoordinateDirection (g := g) p x i)
        (orthonormalCoordinateDirection (g := g) p x i))
      (extChartAt (𝓡 n) p x) =
        tensorCoordinateSection (D.tensorLaplacian_isSmooth hT) p x := by
  let Γ := fun z => D.tensorCoordinateConnectionCoefficient p
    ((extChartAt (𝓡 n) p).symm z) k
  let S := fun z => tensorCoordinateSection hT p ((extChartAt (𝓡 n) p).symm z)
  let b := orthonormalCoordinateDirection (g := g) p x
  let z := extChartAt (𝓡 n) p x
  have hxs : x ∈ (extChartAt (𝓡 n) p).source := by simpa using hx
  have hz := (extChartAt (𝓡 n) p).map_source hxs
  have hsum : Poincare.Riemannian.RadialTransport.covariantDerivative Γ S z
        (∑ i, D.coordinateConnectionCoefficient p x (b i) (b i)) =
      ∑ i, Poincare.Riemannian.RadialTransport.covariantDerivative Γ S z
        (D.coordinateConnectionCoefficient p x (b i) (b i)) := by
    simp only [Poincare.Riemannian.RadialTransport.covariantDerivative,
      map_sum, sum_apply, Finset.sum_add_distrib]
  apply TensorFiber.ext
  intro a
  change TensorFiber.evaluation a
    ((∑ i, Poincare.Riemannian.RadialTransport.covariantDerivative Γ
      (fun w => Poincare.Riemannian.RadialTransport.covariantDerivative Γ S w (b i)) z (b i)) -
      Poincare.Riemannian.RadialTransport.covariantDerivative Γ S z
        (∑ i, D.coordinateConnectionCoefficient p x (b i) (b i))) = _
  rw [hsum]
  simp only [map_sub, map_sum, TensorFiber.evaluation_apply, tensorCoordinateSection_apply]
  rw [← Finset.sum_sub_distrib, ← D.coordinateTensorTrace_eq_tensorLaplacian T p x a hx]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [(extChartAt (𝓡 n) p).left_inv hxs] using
    D.second_covariantDerivative_tensorCoordinateSection_apply hT p hz (b i) (b i) a

end PoincareConjecture.LeviCivitaData
