import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.MaximumPrinciple.TensorLaplacianCoordinates
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.NormBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Manifold
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanNorm
import PoincareConjecture.Proofs.M04.TensorNorm
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.TensorFiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {k : ℕ}

def continuousMultilinear : TensorFiber E k →L[ℝ]
    ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ :=
  (show TensorFiber E k →ₗ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ from
    { toFun := fun T =>
        { toMultilinearMap := toMultilinear T
          cont := (toMultilinear T).continuous_of_bound
            (Real.sqrt (∑ a : Fin k → Fin (Module.finrank ℝ E),
              (T (fun i => stdOrthonormalBasis ℝ E (a i))) ^ 2))
            (fun v => by
              simpa only [Real.norm_eq_abs] using
                abs_multilinear_apply_le_orthonormal_tensor_norm
                  (toMultilinear T) (stdOrthonormalBasis ℝ E) v) }
      map_add' := fun _ _ => by ext; rfl
      map_smul' := fun _ _ => by ext; rfl }).toContinuousLinearMap

@[simp] theorem continuousMultilinear_apply (T : TensorFiber E k) (a : Fin k → E) :
    continuousMultilinear T a = T a := rfl

theorem fderiv_apply
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {S : P → TensorFiber E k} {V : Fin k → P → E} {p : P}
    (hS : DifferentiableAt ℝ S p) (hV : ∀ i, DifferentiableAt ℝ (V i) p)
    (d : P) :
    fderiv ℝ (fun x => S x (fun i => V i x)) p d =
      (fderiv ℝ S p d) (fun i => V i p) +
        ∑ i, S p (Function.update (fun j => V j p) i (fderiv ℝ (V i) p d)) := by
  have hC := (continuousMultilinear (E := E) (k := k)).hasFDerivAt.comp p hS.hasFDerivAt
  have h := hC.continuousMultilinearMap_apply (fun i => (hV i).hasFDerivAt)
  have he := congrArg (fun L => L d) h.fderiv
  simpa only [Function.comp_apply, continuousMultilinear_apply, ContinuousLinearMap.comp_apply,
    _root_.add_apply, sum_apply,
    ContinuousMultilinearMap.apply_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply] using he

end PoincareConjecture.TensorFiber

namespace PoincareConjecture.LeviCivitaData

open ConnectionVariation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem iteratedCovariantTensorDerivative_isSmooth
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (m : ℕ) :
    IsSmoothCovariantTensor (D.iteratedCovariantTensorDerivative T m) := by
  induction m with
  | zero => exact hT
  | succ m ih => exact D.covariantTensorDerivative_isSmooth ih

theorem fderiv_tensorCoordinatePullback
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (a : M)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {q : P → EuclideanSpace ℝ (Fin n)} {V : Fin k → P → EuclideanSpace ℝ (Fin n)}
    {p : P} (hq : DifferentiableAt ℝ q p)
    (hp : q p ∈ (extChartAt (𝓡 n) a).target)
    (hV : ∀ i, DifferentiableAt ℝ (V i) p) (d : P) :
    fderiv ℝ (fun z => tensorCoordinateEvaluation a T
      ((extChartAt (𝓡 n) a).symm (q z)) (fun i => V i z)) p d =
      tensorCoordinateEvaluation a (D.covariantTensorDerivative T)
        ((extChartAt (𝓡 n) a).symm (q p))
        (Fin.cons (fderiv ℝ q p d) (fun i => V i p)) +
      ∑ i, tensorCoordinateEvaluation a T ((extChartAt (𝓡 n) a).symm (q p))
        (Function.update (fun j => V j p) i
          (covDerivAlong
            (fun z => D.coordinateConnectionCoefficient a ((extChartAt (𝓡 n) a).symm z))
            q (V i) d p)) := by
  classical
  let c := extChartAt (𝓡 n) a
  let S := fun z => tensorCoordinateSection hT a (c.symm z)
  have hS : DifferentiableAt ℝ S (q p) :=
    (contDiffAt_tensorCoordinateSection hT a hp).differentiableAt (by simp)
  have hSp : DifferentiableAt ℝ (S ∘ q) p := hS.comp p hq
  have hprod := TensorFiber.fderiv_apply hSp hV d
  have hchain := congrArg (fun L => L d) (hS.hasFDerivAt.comp p hq.hasFDerivAt).fderiv
  simp only [ContinuousLinearMap.comp_apply] at hchain
  rw [hchain] at hprod
  have heval := TensorFiber.fderiv_evaluation hS (fun i => V i p) (fderiv ℝ q p d)
  rw [← heval] at hprod
  have hx : c.symm (q p) ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) a).baseSet := by
    simpa only [c, extChartAt_source, TangentBundle.trivializationAt_baseSet] using c.map_target hp
  have hcov := D.tensorCoordinateDerivative_eq_fderiv_sub hT a hx
    (fderiv ℝ q p d) (fun i => V i p)
  have hcenter : c (c.symm (q p)) = q p := c.right_inv hp
  change tensorCoordinateEvaluation a (D.covariantTensorDerivative T) (c.symm (q p))
      (Fin.cons (fderiv ℝ q p d) (fun i => V i p)) =
    fderiv ℝ (fun z => tensorCoordinateEvaluation a T (c.symm z) (fun i => V i p))
      (c (c.symm (q p))) (fderiv ℝ q p d) - _ at hcov
  rw [hcenter] at hcov
  simp only [Function.comp_apply, S, tensorCoordinateSection_apply] at hprod
  rw [hprod, hcov]
  have hslot (i : Fin k) :
      tensorCoordinateEvaluation a T (c.symm (q p))
        (Function.update (fun j => V j p) i
          (covDerivAlong (fun z => D.coordinateConnectionCoefficient a (c.symm z)) q (V i) d p)) =
      tensorCoordinateEvaluation a T (c.symm (q p))
        (Function.update (fun j => V j p) i (fderiv ℝ (V i) p d)) +
      tensorCoordinateEvaluation a T (c.symm (q p))
        (Function.update (fun j => V j p) i
          (D.coordinateConnectionCoefficient a (c.symm (q p))
            (fderiv ℝ q p d) (V i p))) := by
    simpa only [S, TensorFiber.toMultilinear_apply, tensorCoordinateSection_apply,
      covDerivAlong_def] using
      (TensorFiber.toMultilinear (S (q p))).map_update_add (fun j => V j p) i
        (fderiv ℝ (V i) p d)
        (D.coordinateConnectionCoefficient a (c.symm (q p)) (fderiv ℝ q p d) (V i p))
  dsimp only [c] at hslot
  simp_rw [hslot]
  rw [Finset.sum_add_distrib]
  ring

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.LeviCivitaData

open ConnectionVariation CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

@[simp] theorem constantCoordinateField_model (a v x : EuclideanSpace ℝ (Fin n)) :
    constantCoordinateField a v x = v := by
  unfold constantCoordinateField
  rw [TangentBundle.symmL_model_space]
  rfl

@[simp] theorem tensorCoordinateEvaluation_model {k : ℕ}
    (T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) k)
    (a x : EuclideanSpace ℝ (Fin n)) (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    tensorCoordinateEvaluation a T x v = T x v := by
  simp only [tensorCoordinateEvaluation, constantCoordinateField_model]

theorem coordinateConnectionCoefficient_model (D : LeviCivitaData g)
    (a x : EuclideanSpace ℝ (Fin n)) :
    D.coordinateConnectionCoefficient a x = christoffelBilinear g.euclideanCoefficients x := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rw [D.coordinateConnectionCoefficient_apply a (by simp)]
  have hc : constantCoordinateField a v = fun _ => v := by
    funext z
    exact constantCoordinateField_model a v z
  simp only [coordinateRepresentative, covariantDerivativeOnFields,
    constantCoordinateField_model, hc, TangentBundle.continuousLinearMapAt_model_space]
  change D.connection (fun _ => v) x u = _
  exact D.connection_const_eq_inverse x u v

theorem manifoldCovDerivAlong_model
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (q V : P → EuclideanSpace ℝ (Fin n)) (d p : P) :
    manifoldCovDerivAlong g q V d p =
      covDerivAlong (christoffelBilinear g.euclideanCoefficients) q V d p := by
  change (mfderiv (𝓡 n) (𝓡 n) id (q p)).inverse
    (covDerivAlong (christoffelBilinear (g.pullbackCoefficients id)) q
      (fun z => mfderiv (𝓡 n) (𝓡 n) id (q z) (V z)) d p) = _
  simp only [mfderiv_id, ContinuousLinearMap.inverse_id]
  have hmetric : g.pullbackCoefficients id = g.euclideanCoefficients := by
    funext x
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp [RiemannianMetric.pullbackCoefficients, RiemannianMetric.euclideanCoefficients]
    rfl
  rw [hmetric]
  rfl

theorem fderiv_covariantTensor_pullback_model
    (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) k}
    (hT : IsSmoothCovariantTensor T)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {q : P → EuclideanSpace ℝ (Fin n)} {V : Fin k → P → EuclideanSpace ℝ (Fin n)}
    {p : P} (hq : DifferentiableAt ℝ q p)
    (hV : ∀ i, DifferentiableAt ℝ (V i) p) (d : P) :
    fderiv ℝ (fun z => T (q z) (fun i => V i z)) p d =
      D.covariantTensorDerivative T (q p)
        (Fin.cons (fderiv ℝ q p d) (fun i => V i p)) +
      ∑ i, T (q p) (Function.update (fun j => V j p) i
        (manifoldCovDerivAlong g q (V i) d p)) := by
  have h := D.fderiv_tensorCoordinatePullback hT (0 : EuclideanSpace ℝ (Fin n))
    hq (by simp) hV d
  simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    id_eq, tensorCoordinateEvaluation_model, D.coordinateConnectionCoefficient_model,
    manifoldCovDerivAlong_model] using h

theorem riemannEvaluation_isSmooth_model (D : LeviCivitaData g) :
    IsSmoothCovariantTensor D.riemannEvaluation := by
  constructor
  · intro x
    exact D.exists_multilinear_curvatureTensor x
  · intro U hU X hX x hx
    have hXi (i : Fin 4) : ContDiffAt ℝ ∞ (X i) x := by
      have h := (contMDiffAt_totalSpace.mp ((hX i).contMDiffAt (hU.mem_nhds hx))).2
      simpa using contMDiffAt_iff_contDiffAt.mp h
    have hB := g.contDiffAt_euclideanCoefficients x
    have hΓ := contDiffAt_christoffelBilinear hB (g.inner_isInvertible x)
    have hΓd := hΓ.fderiv_right (m := ∞) (by simp)
    have hcurv : ContDiffAt ℝ ∞
        (fun y => christoffelCurvature (christoffelBilinear g.euclideanCoefficients) y
          (X 0 y) (X 1 y) (X 3 y)) x := by
      unfold christoffelCurvature
      have h₁ := ((hΓd.clm_apply (hXi 0)).clm_apply (hXi 1)).clm_apply (hXi 3)
      have h₂ := ((hΓd.clm_apply (hXi 1)).clm_apply (hXi 0)).clm_apply (hXi 3)
      have h₃ := (hΓ.clm_apply (hXi 0)).clm_apply ((hΓ.clm_apply (hXi 1)).clm_apply (hXi 3))
      have h₄ := (hΓ.clm_apply (hXi 1)).clm_apply ((hΓ.clm_apply (hXi 0)).clm_apply (hXi 3))
      exact ((h₁.sub h₂).add h₃).sub h₄
    have heq : (fun y => D.riemannEvaluation y (fun i => X i y)) =
        fun y => g.euclideanCoefficients y
          (christoffelCurvature (christoffelBilinear g.euclideanCoefficients) y
            (X 0 y) (X 1 y) (X 3 y)) (X 2 y) := by
      funext y
      change g.inner y (D.curvature y (X 0 y) (X 1 y) (X 3 y)) (X 2 y) = _
      rw [← coordinateCurvature_eq_retained D,
        coordinateCurvature_eq_christoffelCurvature
          ((contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients y)
            (g.inner_isInvertible y)).differentiableAt (by simp))]
      rfl
    rw [heq]
    exact (contMDiffAt_iff_contDiffAt.mpr
      ((hB.clm_apply hcurv).clm_apply (hXi 2))).contMDiffWithinAt

theorem fderiv_iteratedCurvature_pullback_model
    (D : LeviCivitaData g) (m : ℕ)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {q : P → EuclideanSpace ℝ (Fin n)}
    {V : Fin (4 + m) → P → EuclideanSpace ℝ (Fin n)}
    {p : P} (hq : DifferentiableAt ℝ q p)
    (hV : ∀ i, DifferentiableAt ℝ (V i) p) (d : P) :
    fderiv ℝ (fun z => D.iteratedCovariantTensorDerivative D.riemannEvaluation m
      (q z) (fun i => V i z)) p d =
      D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) (q p)
        (Fin.cons (fderiv ℝ q p d) (fun i => V i p)) +
      ∑ i, D.iteratedCovariantTensorDerivative D.riemannEvaluation m (q p)
        (Function.update (fun j => V j p) i
          (manifoldCovDerivAlong g q (V i) d p)) := by
  exact D.fderiv_covariantTensor_pullback_model
    (D.iteratedCovariantTensorDerivative_isSmooth D.riemannEvaluation_isSmooth_model m)
    hq hV d

end PoincareConjecture.LeviCivitaData
