import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.TensorCone
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.CurvatureTensor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology InnerProductSpace

namespace PoincareConjecture.AncientKappaRoundness

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance

private theorem ricciComplementEvaluation_eq_inner_operator
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ v w : TangentSpace (𝓡 3) x,
      D.ricciComplementEvaluation x ![v, w] = inner ℝ v
        (TensorFiber.operatorTensorEquiv.symm (D.ricciComplementTensor hD x) w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro v w
  calc
    _ = D.ricciComplementTensor hD x ![v, w] := (D.ricciComplementTensor_apply hD x _).symm
    _ = TensorFiber.operatorTensor
        (TensorFiber.operatorTensorEquiv.symm (D.ricciComplementTensor hD x)).toLinearMap
          ![v, w] := congrArg (fun T : TensorFiber (TangentSpace (𝓡 3) x) 2 => T ![v, w])
            (TensorFiber.operatorTensorEquiv.apply_symm_apply (D.ricciComplementTensor hD x)).symm
    _ = _ := rfl

theorem ricciComplement_mem_tensorPinchingCone_iff
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) (c : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    D.ricciComplementTensor hD x ∈ tensorPinchingCone c ↔
      (∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 →
        0 ≤ D.ricciComplementEvaluation x ![v, v]) ∧
      ∀ v w : TangentSpace (𝓡 3) x, g.inner x v v = 1 → g.inner x w w = 1 →
        D.ricciComplementEvaluation x ![v, v] ≤ c * D.ricciComplementEvaluation x ![w, w] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A := TensorFiber.operatorTensorEquiv.symm (D.ricciComplementTensor hD x)
  have hpair (v w : TangentSpace (𝓡 3) x) :
      inner ℝ v (A w) = D.ricciComplementEvaluation x ![v, w] :=
    (ricciComplementEvaluation_eq_inner_operator D hD x v w).symm
  have hsym : A.toLinearMap.IsSymmetric := by
    intro v w
    change inner ℝ (A v) w = inner ℝ v (A w)
    rw [real_inner_comm, hpair, hpair]
    exact D.ricciComplementEvaluation_symm hD x w v
  have hunit (v : TangentSpace (𝓡 3) x) : ‖v‖ = 1 ↔ g.inner x v v = 1 := by
    change ‖v‖ = 1 ↔ inner ℝ v v = 1
    rw [real_inner_self_eq_norm_sq]
    constructor
    · intro h
      rw [h]
      norm_num
    · intro h
      nlinarith [norm_nonneg v]
  change (A.toLinearMap.IsSymmetric ∧ _ ∧ _) ↔ _
  dsimp only [A] at hpair
  simp only [hsym, true_and, hpair, hunit]

private theorem ricciComplementEvaluation_smul_pair
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (a : ℝ) (v w : TangentSpace (𝓡 3) x) :
    D.ricciComplementEvaluation x ![a • v, a • w] =
      a ^ 2 * D.ricciComplementEvaluation x ![v, w] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [ricciComplementEvaluation_eq_inner_operator D hD x,
    ricciComplementEvaluation_eq_inner_operator D hD x]
  simp only [map_smul, inner_smul_left, inner_smul_right, conj_trivial]
  ring

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {τ : ℝ}

theorem ricciComplement_mem_of_rescaling
    (R : AncientRescaling K τ) {t : ℝ} (ht : t < 0)
    (hsource : (K.flow.connection (τ * t)).CurvatureTensorCalculus)
    (hrescaled : (R.flow.connection t).CurvatureTensorCalculus)
    (x : M) (c : ℝ)
    (hmem : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨(R.flow.metric t).toRiemannianMetric⟩
      (R.flow.connection t).ricciComplementTensor hrescaled x ∈ tensorPinchingCone c) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(K.flow.metric (τ * t)).toRiemannianMetric⟩
    (K.flow.connection (τ * t)).ricciComplementTensor hsource x ∈ tensorPinchingCone c := by
  rw [ricciComplement_mem_tensorPinchingCone_iff] at hmem ⊢
  have hτ : τ ≠ 0 := R.tau_pos.ne'
  have hsqrt : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt R.tau_pos.le
  have hunit (v : TangentSpace (𝓡 3) x)
      (hv : (K.flow.metric (τ * t)).inner x v v = 1) :
      (R.flow.metric t).inner x (Real.sqrt τ • v) (Real.sqrt τ • v) = 1 := by
    rw [R.metric_scale t ht]
    simp only [map_smul, smul_apply, smul_eq_mul, hv]
    field_simp [hτ]
    nlinarith [hsqrt]
  have heval (v w : TangentSpace (𝓡 3) x) :
      (R.flow.connection t).ricciComplementEvaluation x ![v, w] =
        (K.flow.connection (τ * t)).ricciComplementEvaluation x ![v, w] := by
    change ((R.flow.connection t).scalarCurvature x / 2) * (R.flow.metric t).inner x v w -
        (R.flow.connection t).ricci x v w =
      ((K.flow.connection (τ * t)).scalarCurvature x / 2) *
          (K.flow.metric (τ * t)).inner x v w - (K.flow.connection (τ * t)).ricci x v w
    rw [R.scalar_scale t ht, R.metric_scale t ht, R.ricci_scale t ht]
    field_simp [hτ]
  have hscaled (v : TangentSpace (𝓡 3) x) :
      (R.flow.connection t).ricciComplementEvaluation x ![Real.sqrt τ • v, Real.sqrt τ • v] =
        τ * (K.flow.connection (τ * t)).ricciComplementEvaluation x ![v, v] := by
    rw [heval, ricciComplementEvaluation_smul_pair _ hsource, hsqrt]
  constructor
  · intro v hv
    have h := hmem.1 (Real.sqrt τ • v) (hunit v hv)
    rw [hscaled] at h
    exact (mul_nonneg_iff_of_pos_left R.tau_pos).mp h
  · intro v w hv hw
    have h := hmem.2 (Real.sqrt τ • v) (Real.sqrt τ • w) (hunit v hv) (hunit w hw)
    rw [hscaled, hscaled] at h
    apply (mul_le_mul_iff_right₀ R.tau_pos).mp
    simpa only [mul_left_comm] using h

end PoincareConjecture.AncientKappaRoundness
