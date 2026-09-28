import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundModelChristoffel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundSecondJetConversion
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.MaximumPrinciple.TensorLaplacianCoordinates










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M28.tube

open PoincareConjecture.SpacetimeBounds
open PoincareConjecture.CoordinateExponential

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

abbrev ModelE := EuclideanSpace ℝ (Fin 3)
abbrev ModelTensor2 := PoincareConjecture.TensorFiber ModelE 2



noncomputable def modelTensorSlotActionLift (L : ModelE →L[ℝ] ModelE) :
    ModelTensor2 →L[ℝ] ModelTensor2 :=
  PoincareConjecture.TensorFiber.negativeSlotAction L


noncomputable def modelTensorConnectionLift
    (Γ : ModelE →L[ℝ] ModelE →L[ℝ] ModelE) :
    ModelE →L[ℝ] ModelTensor2 →L[ℝ] ModelTensor2 :=
  (show ModelE →ₗ[ℝ] ModelTensor2 →L[ℝ] ModelTensor2 from
      { toFun := fun u => modelTensorSlotActionLift (Γ u)
        map_add' := by
          intro u v
          apply ContinuousLinearMap.ext
          intro T
          apply PoincareConjecture.TensorFiber.ext
          intro a
          simp [modelTensorSlotActionLift,
            PoincareConjecture.TensorFiber.negativeSlotAction_apply]
          ring
        map_smul' := by
          intro c u
          apply ContinuousLinearMap.ext
          intro T
          apply PoincareConjecture.TensorFiber.ext
          intro a
          simp [modelTensorSlotActionLift,
            PoincareConjecture.TensorFiber.negativeSlotAction_apply]
          ring }).toContinuousLinearMap

noncomputable def modelTensorConnectionLiftMap :
    (ModelE →L[ℝ] ModelE →L[ℝ] ModelE) →L[ℝ]
      (ModelE →L[ℝ] ModelTensor2 →L[ℝ] ModelTensor2) :=
  (show (ModelE →L[ℝ] ModelE →L[ℝ] ModelE) →ₗ[ℝ]
      (ModelE →L[ℝ] ModelTensor2 →L[ℝ] ModelTensor2) from
    { toFun := modelTensorConnectionLift
      map_add' := by
        intro Γ Δ
        apply ContinuousLinearMap.ext
        intro u
        apply ContinuousLinearMap.ext
        intro T
        apply PoincareConjecture.TensorFiber.ext
        intro a
        simp [modelTensorConnectionLift, modelTensorSlotActionLift,
          PoincareConjecture.TensorFiber.negativeSlotAction_apply]
        ring
      map_smul' := by
        intro c Γ
        apply ContinuousLinearMap.ext
        intro u
        apply ContinuousLinearMap.ext
        intro T
        apply PoincareConjecture.TensorFiber.ext
        intro a
        simp [modelTensorConnectionLift, modelTensorSlotActionLift,
          PoincareConjecture.TensorFiber.negativeSlotAction_apply]
        ring }).toContinuousLinearMap

noncomputable def roundModelTensorConnection
    (B : ModelE → ModelE →L[ℝ] ModelE →L[ℝ] ℝ) :
    ModelE → ModelE →L[ℝ] ModelTensor2 →L[ℝ] ModelTensor2 :=
  fun x => modelTensorConnectionLift (christoffelBilinear B x)

@[simp] theorem roundModelTensorConnection_apply
    (B : ModelE → ModelE →L[ℝ] ModelE →L[ℝ] ℝ)
    (x u : ModelE) (T : ModelTensor2) :
    roundModelTensorConnection B x u T =
      modelTensorSlotActionLift (christoffelBilinear B x u) T := by
  rfl

theorem contDiffAt_roundModelTensorConnection
    {B : ModelE → ModelE →L[ℝ] ModelE →L[ℝ] ℝ} {x : ModelE}
    (hB : ContDiffAt ℝ ∞ B x) (hBinv : (B x).IsInvertible) :
    ContDiffAt ℝ ∞ (roundModelTensorConnection B) x := by
  have hΓ := contDiffAt_christoffelBilinear hB hBinv
  change ContDiffAt ℝ ∞
    (fun y => modelTensorConnectionLiftMap (christoffelBilinear B y)) x
  exact modelTensorConnectionLiftMap.contDiff.contDiffAt.comp x hΓ

theorem norm_fderiv_roundModelTensorConnection_le
    {B : ModelE → ModelE →L[ℝ] ModelE →L[ℝ] ℝ} {C : ℝ}
    (hB : ContDiffAt ℝ ∞ B 0) (hBinv : (B 0).IsInvertible)
    (_hC : 0 ≤ C)
    (hΓ : ∀ u : ModelE,
      ‖fderiv ℝ (christoffelBilinear B) 0 u‖ ≤ C * ‖u‖) (u : ModelE) :
    ‖fderiv ℝ (roundModelTensorConnection B) 0 u‖ ≤
      ‖modelTensorConnectionLiftMap‖ * C * ‖u‖ := by
  have hΓd : DifferentiableAt ℝ (christoffelBilinear B) 0 :=
    (contDiffAt_christoffelBilinear hB hBinv).differentiableAt (by simp)
  have hcomp := (modelTensorConnectionLiftMap.hasFDerivAt.comp 0
    hΓd.hasFDerivAt).fderiv
  have heq : fderiv ℝ (roundModelTensorConnection B) 0 u =
      modelTensorConnectionLiftMap
        ((fderiv ℝ (christoffelBilinear B) 0) u) := by
    have hcomp' : fderiv ℝ (fun y =>
        modelTensorConnectionLiftMap (christoffelBilinear B y)) 0 =
        modelTensorConnectionLiftMap.comp
          (fderiv ℝ (christoffelBilinear B) 0) := hcomp
    rw [show roundModelTensorConnection B = fun y =>
      modelTensorConnectionLiftMap (christoffelBilinear B y) by rfl, hcomp']
    rfl
  rw [heq]
  calc
    ‖modelTensorConnectionLiftMap
        ((fderiv ℝ (christoffelBilinear B) 0) u)‖ ≤
        ‖modelTensorConnectionLiftMap‖ *
          ‖(fderiv ℝ (christoffelBilinear B) 0) u‖ := by
      exact ContinuousLinearMap.le_opNorm modelTensorConnectionLiftMap
        ((fderiv ℝ (christoffelBilinear B) 0) u)
    _ ≤ ‖modelTensorConnectionLiftMap‖ * (C * ‖u‖) := by
      exact mul_le_mul_of_nonneg_left (hΓ u)
        (norm_nonneg modelTensorConnectionLiftMap)
    _ = ‖modelTensorConnectionLiftMap‖ * C * ‖u‖ := by ring

theorem exists_round_model_tensor_connection_fderiv_bound
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (e : ModelE → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (hcenter : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ModelE,
        ‖fderiv ℝ (roundModelTensorConnection
          (N.model_metric.pullbackCoefficients e)) 0 u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, _hrawPoint, hrawOp, _hrawNorm⟩ :=
    exists_round_model_christoffel_operator_jet_bound
      N hρ hρR e he hi hcenter hgauss
  let C' := ‖modelTensorConnectionLiftMap‖ * C
  have hC' : 0 ≤ C' := mul_nonneg (norm_nonneg _) hC
  refine ⟨C', hC', ?_⟩
  intro u
  have hB : ContDiffAt ℝ ∞
      (N.model_metric.pullbackCoefficients e) 0 := by
    exact N.model_metric.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (isOpen_ball.mem_nhds (mem_ball_self
        (hρ.trans hρR))))
  have hBinv :
      (N.model_metric.pullbackCoefficients e 0).IsInvertible := by
    exact N.model_metric.isInvertible_pullbackCoefficients
      (hi 0 (mem_ball.mpr (by simpa using hρ.trans hρR))).injective
  simpa [C'] using norm_fderiv_roundModelTensorConnection_le
    hB hBinv hC (fun v => hrawOp v) u

theorem round_model_tensor_connection_zero
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (e : ModelE → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (hcenter : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w) :
    roundModelTensorConnection (N.model_metric.pullbackCoefficients e) 0 = 0 := by
  have hzero := round_model_christoffel_zero N hρ hρR e he hi hcenter hgauss
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro T
  rw [roundModelTensorConnection_apply, hzero]
  apply PoincareConjecture.TensorFiber.ext
  intro a
  simp [modelTensorSlotActionLift,
    PoincareConjecture.TensorFiber.negativeSlotAction_apply]





theorem norm_round_model_second_fderiv_le
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (e : ModelE → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (hcenter : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w)
    {S : ModelE → ModelTensor2} (hS : ContDiffAt ℝ ∞ S 0)
    (u v : ModelE) {A G V W : ℝ}
    (hA : ‖Poincare.Riemannian.RadialTransport.covariantDerivative
      (roundModelTensorConnection (N.model_metric.pullbackCoefficients e))
      (fun y => Poincare.Riemannian.RadialTransport.covariantDerivative
        (roundModelTensorConnection (N.model_metric.pullbackCoefficients e)) S y v)
      0 u‖ ≤ A)
    (hG : ‖fderiv ℝ (roundModelTensorConnection
      (N.model_metric.pullbackCoefficients e)) 0 u‖ ≤ G)
    (hV : ‖v‖ ≤ V) (hW : ‖S 0‖ ≤ W)
    (hA0 : 0 ≤ A) (hG0 : 0 ≤ G) (hV0 : 0 ≤ V) (hW0 : 0 ≤ W) :
    ‖fderiv ℝ (fun y => fderiv ℝ S y v) 0 u‖ ≤ A + G * V * W := by
  apply norm_second_fderiv_le_of_zero_connection
  · exact contDiffAt_roundModelTensorConnection (by
      exact (N.model_metric.contDiffAt_pullbackCoefficients
        (he.contMDiffAt (isOpen_ball.mem_nhds (mem_ball_self (hρ.trans hρR))))))
      (N.model_metric.isInvertible_pullbackCoefficients
        (hi 0 (mem_ball.mpr (by simpa using hρ.trans hρR))).injective)
  · exact hS
  · exact round_model_tensor_connection_zero N hρ hρR e he hi hcenter hgauss
  · exact hA
  · exact hG
  · exact hV
  · exact hW
  · exact hA0
  · exact hG0
  · exact hV0
  · exact hW0

theorem norm_round_model_second_fderiv_le_of_covariant_bound
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (e : ModelE → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (hcenter : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w)
    {S : ModelE → ModelTensor2} (hS : ContDiffAt ℝ ∞ S 0)
    (u v : ModelE) {A V W : ℝ}
    (hA : ‖Poincare.Riemannian.RadialTransport.covariantDerivative
      (roundModelTensorConnection (N.model_metric.pullbackCoefficients e))
      (fun y => Poincare.Riemannian.RadialTransport.covariantDerivative
        (roundModelTensorConnection (N.model_metric.pullbackCoefficients e)) S y v)
      0 u‖ ≤ A)
    (hV : ‖v‖ ≤ V) (hW : ‖S 0‖ ≤ W)
    (hA0 : 0 ≤ A) (hV0 : 0 ≤ V) (hW0 : 0 ≤ W) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖fderiv ℝ (fun y => fderiv ℝ S y v) 0 u‖ ≤
        A + (C * ‖u‖) * V * W := by
  obtain ⟨C, hC, hconn⟩ :=
    exists_round_model_tensor_connection_fderiv_bound
      N hρ hρR e he hi hcenter hgauss
  have hG : ‖fderiv ℝ (roundModelTensorConnection
      (N.model_metric.pullbackCoefficients e)) 0 u‖ ≤
      C * ‖u‖ := hconn u
  have hG0 : 0 ≤ C * ‖u‖ :=
    mul_nonneg hC (norm_nonneg _)
  refine ⟨C, hC, ?_⟩
  exact norm_round_model_second_fderiv_le N hρ hρR e he hi hcenter hgauss
    hS u v hA hG hV hW hA0 hG0 hV0 hW0

end PoincareConjecture.M28.tube
