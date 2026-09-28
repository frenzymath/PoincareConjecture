import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Hessian.Divergence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Tensor.Green
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Regularity









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma metricTensor_smooth :
    IsSmoothCovariantTensor (fun x (v : Fin 2 → TangentSpace (𝓡 n) x) =>
      g.inner x (v 0) (v 1)) := by
  constructor
  · intro x
    let A : MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace (𝓡 n) x) ℝ :=
      { toFun := fun v => g.inner x (v 0) (v 1)
        map_update_add' := by
          intro _ v i a b
          fin_cases i <;> simp [map_add]
        map_update_smul' := by
          intro _ v i c a
          fin_cases i <;> simp }
    exact ⟨A, fun _ => rfl⟩
  · intro U hU X hX
    have hi := (g.contMDiff.contMDiffOn.clm_bundle_apply (hX 0)).clm_bundle_apply (hX 1)
    intro x hx
    exact (Bundle.contMDiffAt_totalSpace.mp
      ((hi x hx).contMDiffAt (hU.mem_nhds hx))).2.contMDiffWithinAt

private lemma metric_covector_product_smooth
    {β : CovariantTensorEvaluation n M 1} (hβ : IsSmoothCovariantTensor β) :
    IsSmoothCovariantTensor (k := 3)
      (fun x v => g.inner x (v 0) (v 1) * β x ![v 2]) := by
  have hp := isSmoothCovariantTensor_tensorProduct (metricTensor_smooth (g := g)) hβ
  convert hp using 1
  funext x v
  unfold tensorProduct
  congr 1
  congr 1
  ext i
  fin_cases i
  rfl


theorem twoTensorDivergenceFlux_isSmooth (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (D.twoTensorDivergenceFlux T) := by
  have hDT := D.covariantTensorDerivative_isSmooth hT
  have hβ : IsSmoothCovariantTensor (D.tensorDivergence T) := hDT.tensorTrace
  have hC : IsSmoothCovariantTensor (D.twoTensorCodazziDefect T) := by
    unfold twoTensorCodazziDefect
    exact hDT.sub (hDT.perm _)
  exact (metric_covector_product_smooth hβ).add hC


theorem twoTensorCurvatureTrace_isSmooth (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (D.twoTensorCurvatureTrace T) := by
  have hL : IsSmoothCovariantTensor (D.tensorLaplacian T) :=
    (D.covariantTensorDerivative_isSmooth
      (D.covariantTensorDerivative_isSmooth hT)).tensorTrace
  have hF : IsSmoothCovariantTensor (D.tensorDivergence (D.twoTensorDivergenceFlux T)) :=
    (D.covariantTensorDerivative_isSmooth (D.twoTensorDivergenceFlux_isSmooth hT)).tensorTrace
  have heq : D.twoTensorCurvatureTrace T =
      (fun x v => D.tensorLaplacian T x v -
        D.tensorDivergence (D.twoTensorDivergenceFlux T) x v) := by
    funext x v
    have hv : v = ![v 0, v 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hv]
    have h := D.tensorLaplacian_eq_divergence_flux hT x (v 0) (v 1)
    linarith
  rw [heq]
  exact hL.sub hF



theorem hessianCurvatureFlux_eq_divergenceFlux_sub_laplacian
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    D.hessianCurvatureFlux f =
      (fun x v =>
        D.twoTensorDivergenceFlux (fun y z => D.hessian f y (z 0) (z 1)) x v -
          g.inner x (v 0) (v 1) * mvfderiv (𝓡 n) (D.laplacian f) x (v 2)) := by
  funext x v
  have hdiv := D.sum_covariantTensorDerivative_hessian_apply hf x (v 2)
  change D.tensorDivergence (fun y z => D.hessian f y (z 0) (z 1)) x ![v 2] =
    mvfderiv (𝓡 n) (D.laplacian f) x (v 2) + D.ricci x (D.gradient f x) (v 2) at hdiv
  have hc : D.twoTensorCodazziDefect (fun y z => D.hessian f y (z 0) (z 1)) x v =
      -mvfderiv (𝓡 n) f x (D.curvature x (v 0) (v 1) (v 2)) := by
    have hv : v = ![v 0, v 1, v 2] := by
      ext i
      fin_cases i <;> rfl
    rw [hv]
    exact D.covariantTensorDerivative_hessian_commutator hf x (v 0) (v 1) (v 2)
  unfold hessianCurvatureFlux twoTensorDivergenceFlux
  rw [hdiv, hc]
  ring


theorem hessianCurvatureFlux_isSmooth (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    IsSmoothCovariantTensor (D.hessianCurvatureFlux f) := by
  rw [D.hessianCurvatureFlux_eq_divergenceFlux_sub_laplacian hf]
  have hβ := differentialEvaluation_isSmooth (D.contMDiff_laplacian hf)
  exact (D.twoTensorDivergenceFlux_isSmooth (D.hessian_isSmoothCovariantTensor hf)).sub
    (metric_covector_product_smooth hβ)

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private lemma integrable_tensorPairingTwo_compact (D : LeviCivitaData g)
    {A Z : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hA : IsSmoothCovariantTensor A) (hZ : IsSmoothCovariantTensor Z)
    (hc : HasCompactSupport (fun x (v : Fin 2 → EuclideanSpace ℝ (Fin n)) => Z x v)) :
    Integrable (g.tensorPairingTwo A Z) g.volumeMeasure := by
  apply (D.contMDiff_tensorPairingTwo hA hZ).continuous.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro x hx
  by_contra hx'
  exact hx (by simp [RiemannianMetric.tensorPairingTwo,
    image_eq_zero_of_notMem_tsupport hx'])



theorem integral_covariantHessian_pairing (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {Z : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hZ : IsSmoothCovariantTensor Z)
    (hc : HasCompactSupport (fun x (v : Fin 2 → EuclideanSpace ℝ (Fin n)) => Z x v))
    (hharm : ∀ x ∈ tsupport (fun x (v : Fin 2 → EuclideanSpace ℝ (Fin n)) => Z x v),
      D.laplacian f =ᶠ[𝓝 x] fun _ => 0) :
    (∫ x, g.tensorPairingThree
      (D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)))
      (D.covariantTensorDerivative Z) x ∂g.volumeMeasure) =
      (∫ x, g.tensorPairingThree (D.hessianCurvatureFlux f)
        (D.covariantTensorDerivative Z) x ∂g.volumeMeasure) -
      (∫ x, g.tensorPairingTwo
        (D.twoTensorCurvatureTrace (fun y v => D.hessian f y (v 0) (v 1))) Z x
        ∂g.volumeMeasure) := by
  let H : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2 :=
    fun y v => D.hessian f y (v 0) (v 1)
  have hH : IsSmoothCovariantTensor H := D.hessian_isSmoothCovariantTensor hf
  have hB := D.hessianCurvatureFlux_isSmooth hf
  have hA := D.twoTensorCurvatureTrace_isSmooth hH
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
      g.tensorPairingTwo (D.tensorLaplacian H) Z x =
        g.tensorPairingTwo (D.tensorDivergence (D.hessianCurvatureFlux f)) Z x +
          g.tensorPairingTwo (D.twoTensorCurvatureTrace H) Z x := by
    by_cases hx : x ∈ tsupport (fun x (v : Fin 2 → EuclideanSpace ℝ (Fin n)) => Z x v)
    · simp only [RiemannianMetric.tensorPairingTwo, H,
        D.tensorLaplacian_hessian_eq_divergence_curvature hf x (hharm x hx),
        add_mul, Finset.sum_add_distrib]
    · have hz := image_eq_zero_of_notMem_tsupport hx
      simp [RiemannianMetric.tensorPairingTwo, hz]
  have hdivI := D.integrable_tensorPairingTwo_compact
    ((D.covariantTensorDerivative_isSmooth hB).tensorTrace (g := g)) hZ hc
  have hAI := D.integrable_tensorPairingTwo_compact hA hZ hc
  have hI : (∫ x, g.tensorPairingTwo (D.tensorLaplacian H) Z x ∂g.volumeMeasure) =
      (∫ x, g.tensorPairingTwo (D.tensorDivergence (D.hessianCurvatureFlux f)) Z x
        ∂g.volumeMeasure) +
      (∫ x, g.tensorPairingTwo (D.twoTensorCurvatureTrace H) Z x ∂g.volumeMeasure) := by
    simp_rw [hpoint]
    exact integral_add hdivI hAI
  rw [D.integral_tensorLaplacian_pairing hH hZ hc,
    show (∫ x, g.tensorPairingTwo (D.tensorDivergence (D.hessianCurvatureFlux f)) Z x
      ∂g.volumeMeasure) =
        -(∫ x, g.tensorPairingThree (D.hessianCurvatureFlux f)
          (D.covariantTensorDerivative Z) x ∂g.volumeMeasure) from
      D.integral_tensorDivergence_pairing hB hZ hc] at hI
  change (∫ x, g.tensorPairingThree (D.covariantTensorDerivative H)
    (D.covariantTensorDerivative Z) x ∂g.volumeMeasure) = _
  linarith

end PoincareConjecture.LeviCivitaData
