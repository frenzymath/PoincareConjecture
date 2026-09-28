import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Tensor.Pairing
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.VectorGreen
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite
import Mathlib.Analysis.InnerProductSpace.Trace









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Bundle
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private def smoothCovectorCLM
    {α : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 1}
    (hα : IsSmoothCovariantTensor α) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  ((MultilinearMap.ofSubsingleton ℝ (EuclideanSpace ℝ (Fin n)) ℝ (0 : Fin 1)).symm
    (hα.1 x).choose).toContinuousLinearMap

private theorem smoothCovectorCLM_apply
    {α : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 1}
    (hα : IsSmoothCovariantTensor α) (x v : EuclideanSpace ℝ (Fin n)) :
    smoothCovectorCLM hα x v = α x ![v] := by
  change (hα.1 x).choose (fun _ => v) = α x ![v]
  rw [← (hα.1 x).choose_spec]
  congr 1
  ext i
  fin_cases i
  rfl


def tensorCovectorDual (_D : LeviCivitaData g)
    {α : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 1}
    (hα : IsSmoothCovariantTensor α) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (g.euclideanCoefficients x).inverse (smoothCovectorCLM hα x)


theorem inner_tensorCovectorDual (D : LeviCivitaData g)
    {α : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 1}
    (hα : IsSmoothCovariantTensor α) (x v : EuclideanSpace ℝ (Fin n)) :
    g.inner x (D.tensorCovectorDual hα x) v = α x ![v] := by
  have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v)
    ((g.inner_isInvertible x).self_apply_inverse (smoothCovectorCLM hα x))
  exact h.trans (smoothCovectorCLM_apply hα x v)


theorem contDiff_tensorCovectorDual (D : LeviCivitaData g)
    {α : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 1}
    (hα : IsSmoothCovariantTensor α) :
    ContDiff ℝ ∞ (D.tensorCovectorDual hα) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hG := g.contDiffAt_euclideanCoefficients x
  have hginv : (g.euclideanCoefficients x).IsInvertible := g.inner_isInvertible x
  have hinv := (hginv.contDiffAt_map_inverse (n := ∞)).comp x hG
  apply hinv.clm_apply
  apply contMDiffAt_iff_contDiffAt.mp
  apply PoincareConjecture.contMDiffAt_clm_of_apply
  intro v
  simp_rw [smoothCovectorCLM_apply]
  have hconst : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) v) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have h := contMDiffOn_univ.mp
    (hα.2 Set.univ isOpen_univ (fun _ _ => v) (fun _ => hconst.contMDiffOn))
  have heq : (fun y => α y (fun _ => v)) = fun y => α y ![v] := by
    funext y
    congr 1
    ext i
    fin_cases i
    rfl
  rw [heq] at h
  exact h.contMDiffAt


theorem covariantTensorDerivative_covector_eq_inner_connection (D : LeviCivitaData g)
    {α : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 1}
    (hα : IsSmoothCovariantTensor α) (x u v : EuclideanSpace ℝ (Fin n)) :
    D.covariantTensorDerivative α x ![u, v] =
      g.inner x (D.connection (D.tensorCovectorDual hα) x u) v := by
  let U := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (show TangentSpace (𝓡 n) x from u)
  let V := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (show TangentSpace (𝓡 n) x from v)
  let A := D.tensorCovectorDual hα
  have hA : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) (A y)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (D.contDiff_tensorCovectorDual hα)
  have hV := FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n))
    (show TangentSpace (𝓡 n) x from v)
  have hd := D.horizon_mvfderiv_inner U ((hA x).mdifferentiableAt (by simp))
    (hV.mdifferentiableAt (by simp))
  have hfun : (fun y => g.inner y (A y) (V y)) = fun y => α y ![V y] := by
    funext y
    exact D.inner_tensorCovectorDual hα y (V y)
  rw [hfun] at hd
  simp only [U, V, covariantDerivativeOnFields, FiberBundle.extend_apply_self] at hd
  rw [D.inner_tensorCovectorDual] at hd
  have ht := D.covariantTensorDerivative_on_fields hα (fun _ => V) x
    (fun _ => hV.mdifferentiableAt (by simp)) u
  have hsingle (y : EuclideanSpace ℝ (Fin n)) :
      (fun _ : Fin 1 => V y) = ![V y] := by
    ext i
    fin_cases i
    rfl
  simp only [hsingle, V, FiberBundle.extend_apply_self,
    Fin.sum_univ_one] at ht
  have hvconst : (fun _ : Fin 1 => (show TangentSpace (𝓡 n) x from v)) =
      ![(show TangentSpace (𝓡 n) x from v)] := by
    ext i
    fin_cases i
    rfl
  rw [hvconst] at ht
  simp only [Matrix.Fin.cons_vecCons] at ht
  have hupdate : Function.update ![v] (0 : Fin 1) (D.connection V x u) =
      ![D.connection V x u] := by
    ext i
    fin_cases i
    simp
  rw [hupdate] at ht
  rw [ht, hd]
  ring


theorem trace_connection_tensorCovectorDual (D : LeviCivitaData g)
    {α : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 1}
    (hα : IsSmoothCovariantTensor α) (x : EuclideanSpace ℝ (Fin n)) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
        (D.connection (D.tensorCovectorDual hα) x).toLinearMap =
      g.tensorTrace (D.covariantTensorDerivative α) x ![] := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change LinearMap.trace ℝ (TangentSpace (𝓡 n) x)
    (D.connection (D.tensorCovectorDual hα) x).toLinearMap = _
  rw [LinearMap.trace_eq_sum_inner _ (g.orthonormalBasis x)]
  apply Finset.sum_congr rfl
  intro i _
  change g.inner x (g.orthonormalBasis x i)
    (D.connection (D.tensorCovectorDual hα) x (g.orthonormalBasis x i)) = _
  rw [g.symm]
  exact (D.covariantTensorDerivative_covector_eq_inner_connection hα x _ _).symm


theorem hasCompactSupport_tensorCovectorDual (D : LeviCivitaData g)
    {α : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 1}
    (hα : IsSmoothCovariantTensor α)
    (hc : HasCompactSupport (fun x (v : Fin 1 → EuclideanSpace ℝ (Fin n)) => α x v)) :
    HasCompactSupport (D.tensorCovectorDual hα) := by
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro x hx
  by_contra hx'
  have hzero := image_eq_zero_of_notMem_tsupport hx'
  have hclm : smoothCovectorCLM hα x = 0 := by
    ext v
    rw [smoothCovectorCLM_apply]
    exact congrFun hzero ![v]
  exact hx (by simp [tensorCovectorDual, hclm])


theorem covariantTensorDerivative_eq_zero_of_eventually_zero (D : LeviCivitaData g)
    {k : ℕ} {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) k}
    {x : EuclideanSpace ℝ (Fin n)}
    (hT : (fun y (v : Fin k → EuclideanSpace ℝ (Fin n)) => T y v) =ᶠ[𝓝 x] fun _ => 0) :
    D.covariantTensorDerivative T x = 0 := by
  funext v
  have hx : ∀ v, T x v = 0 := fun v => congrFun hT.eq_of_nhds v
  have hfun :
      (fun y => T y (fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n))
        (v i.succ) y)) =ᶠ[𝓝 x] fun _ => 0 :=
    hT.mono fun y hy => congrFun hy _
  have hd : mvfderiv (𝓡 n)
      (fun y => T y (fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n))
        (v i.succ) y)) x = mvfderiv (𝓡 n) (fun _ => (0 : ℝ)) x := by
    unfold mvfderiv
    rw [hfun.mfderiv_eq, mfderiv_const]
    simp
  unfold covariantTensorDerivative
  rw [hd, mvfderiv_const]
  simp [hx]


theorem hasCompactSupport_covariantTensorDerivative (D : LeviCivitaData g)
    {k : ℕ} {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) k}
    (hc : HasCompactSupport (fun x (v : Fin k → EuclideanSpace ℝ (Fin n)) => T x v)) :
    HasCompactSupport (fun x (v : Fin (k + 1) → EuclideanSpace ℝ (Fin n)) =>
      D.covariantTensorDerivative T x v) := by
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro x hx
  by_contra hx'
  exact hx (D.covariantTensorDerivative_eq_zero_of_eventually_zero
    (notMem_tsupport_iff_eventuallyEq.mp hx'))


theorem contMDiff_tensorPairingThree_derivative (D : LeviCivitaData g)
    {F : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 3}
    {Z : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hF : IsSmoothCovariantTensor F) (hZ : IsSmoothCovariantTensor Z) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (g.tensorPairingThree F (D.covariantTensorDerivative Z)) := by
  have hα := D.isSmoothCovariantTensor_tensorPairingCovector hF hZ
  have htrace := (D.covariantTensorDerivative_isSmooth hα).tensorTrace (g := g)
  have hA := contMDiffOn_univ.mp
    (htrace.2 Set.univ isOpen_univ (fun i => Fin.elim0 i) (fun i => Fin.elim0 i))
  have hB := D.contMDiff_tensorPairingTwo
    ((D.covariantTensorDerivative_isSmooth hF).tensorTrace (g := g)) hZ
  convert hA.sub hB using 1
  funext x
  have hempty (v : Fin 0 → TangentSpace (𝓡 n) x) :
      g.tensorTrace (D.covariantTensorDerivative (g.tensorPairingCovector F Z)) x v =
      g.tensorTrace (D.covariantTensorDerivative (g.tensorPairingCovector F Z)) x ![] :=
    congrArg _ (Subsingleton.elim _ _)
  rw [hempty]
  rw [D.tensorTrace_derivative_tensorPairingCovector hF hZ]
  ring


theorem integral_tensorDivergence_pairing (D : LeviCivitaData g)
    {F : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 3}
    {Z : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hF : IsSmoothCovariantTensor F) (hZ : IsSmoothCovariantTensor Z)
    (hc : HasCompactSupport (fun x (v : Fin 2 → EuclideanSpace ℝ (Fin n)) => Z x v)) :
    (∫ x, g.tensorPairingTwo (g.tensorTrace (D.covariantTensorDerivative F)) Z x
      ∂g.volumeMeasure) =
      -(∫ x, g.tensorPairingThree F (D.covariantTensorDerivative Z) x
        ∂g.volumeMeasure) := by
  have hα := D.isSmoothCovariantTensor_tensorPairingCovector hF hZ
  have hαc : HasCompactSupport (fun x (v : Fin 1 → EuclideanSpace ℝ (Fin n)) =>
      g.tensorPairingCovector F Z x v) := by
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro x hx
    by_contra hx'
    have hz := image_eq_zero_of_notMem_tsupport hx'
    exact hx (by ext v; simp [RiemannianMetric.tensorPairingCovector, hz])
  have hdiv := D.integral_trace_connection_eq_zero
    ((D.contDiff_tensorCovectorDual hα).of_le (by simp))
    (D.hasCompactSupport_tensorCovectorDual hα hαc)
  simp_rw [D.trace_connection_tensorCovectorDual,
    D.tensorTrace_derivative_tensorPairingCovector hF hZ] at hdiv
  have hleft : Integrable
      (g.tensorPairingTwo (g.tensorTrace (D.covariantTensorDerivative F)) Z)
      g.volumeMeasure := by
    apply (D.contMDiff_tensorPairingTwo
      ((D.covariantTensorDerivative_isSmooth hF).tensorTrace (g := g)) hZ).continuous
        |>.integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro x hx
    by_contra hx'
    exact hx (by simp [RiemannianMetric.tensorPairingTwo,
      image_eq_zero_of_notMem_tsupport hx'])
  have hright : Integrable
      (g.tensorPairingThree F (D.covariantTensorDerivative Z)) g.volumeMeasure := by
    apply (D.contMDiff_tensorPairingThree_derivative hF hZ).continuous
      |>.integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact
      (D.hasCompactSupport_covariantTensorDerivative hc)
    intro x hx
    by_contra hx'
    exact hx (by simp [RiemannianMetric.tensorPairingThree,
      image_eq_zero_of_notMem_tsupport hx'])
  rw [integral_add hleft hright] at hdiv
  linarith


theorem integral_tensorLaplacian_pairing (D : LeviCivitaData g)
    {T Z : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hT : IsSmoothCovariantTensor T) (hZ : IsSmoothCovariantTensor Z)
    (hc : HasCompactSupport (fun x (v : Fin 2 → EuclideanSpace ℝ (Fin n)) => Z x v)) :
    (∫ x, g.tensorPairingTwo (D.tensorLaplacian T) Z x ∂g.volumeMeasure) =
      -(∫ x, g.tensorPairingThree (D.covariantTensorDerivative T)
        (D.covariantTensorDerivative Z) x ∂g.volumeMeasure) :=
  D.integral_tensorDivergence_pairing (D.covariantTensorDerivative_isSmooth hT) hZ hc

end PoincareConjecture.LeviCivitaData
