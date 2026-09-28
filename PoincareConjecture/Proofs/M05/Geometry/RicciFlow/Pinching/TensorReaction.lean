
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.ReactionSupport
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.TensorRegion
import PoincareConjecture.Proofs.M05.Analysis.Parabolic.ConvexSupport












namespace Poincare.HamiltonIvey

noncomputable section

open PoincareConjecture TensorFiber
open Set
open scoped ContDiff Topology NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


noncomputable def tensorReaction (T : TensorFiber E 2) : TensorFiber E 2 :=
  operatorTensorEquiv
    ((endomorphismReaction (operatorTensorEquiv.symm T).toLinearMap).toContinuousLinearMap)

@[simp] theorem tensorReaction_operatorTensor (A : E →ₗ[ℝ] E) :
    tensorReaction (operatorTensor A) = operatorTensor (endomorphismReaction A) := by
  have hA := operatorTensorEquiv_symm_apply A.toContinuousLinearMap
  simp only [LinearMap.coe_toContinuousLinearMap] at hA
  simp only [tensorReaction, hA, LinearMap.coe_toContinuousLinearMap,
    operatorTensorEquiv_apply]


noncomputable def scaledTensorReaction (t : ℝ) (T : TensorFiber E 2) : TensorFiber E 2 :=
  (1 + t)⁻¹ • (T + tensorReaction T)

theorem endomorphismReaction_conj
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (e : E ≃ₗ[ℝ] F) (A : E →ₗ[ℝ] E) :
    endomorphismReaction (e.conj A) = e.conj (endomorphismReaction A) := by
  have hmul : e.conj (A * A) = e.conj A * e.conj A := e.conj_comp A A
  have hone : e.conj (1 : E →ₗ[ℝ] E) = 1 := e.conj_id
  simp only [endomorphismReaction, map_add, map_sub, map_nsmul, map_smul,
    LinearMap.trace_conj', hone, ← hmul]

theorem tensorReaction_transport
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (e : E ≃ₗᵢ[ℝ] F) (T : TensorFiber E 2) :
    tensorReaction (transport e 2 T) = transport e 2 (tensorReaction T) := by
  obtain ⟨A, rfl⟩ := (operatorTensorEquiv (E := E)).surjective T
  rw [operatorTensorEquiv_apply, transport_operatorTensor_eq,
    tensorReaction_operatorTensor, tensorReaction_operatorTensor,
    transport_operatorTensor_eq, endomorphismReaction_conj]

theorem scaledTensorReaction_transport
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (e : E ≃ₗᵢ[ℝ] F) (t : ℝ) (T : TensorFiber E 2) :
    scaledTensorReaction t (transport e 2 T) =
      transport e 2 (scaledTensorReaction t T) := by
  simp only [scaledTensorReaction, tensorReaction_transport, map_smul, map_add]

theorem contDiff_tensorReaction :
    ContDiff ℝ ∞ (tensorReaction (E := E)) := by
  unfold tensorReaction
  exact (operatorTensorEquiv (E := E)).contDiff.comp
    ((contDiff_continuousEndomorphismReaction (E := E)).comp
      (operatorTensorEquiv (E := E)).symm.contDiff)

theorem exists_lipschitzOnWith_tensorReaction
    (K : Set (TensorFiber E 2)) (hK : IsCompact K) (hconv : Convex ℝ K) :
    ∃ C : ℝ≥0, LipschitzOnWith C (tensorReaction (E := E)) K := by
  exact contDiff_tensorReaction.contDiffOn.exists_lipschitzOnWith
    (by simp) hconv hK

theorem exists_lipschitzOnWith_scaledTensorReaction (R : ℝ) :
    ∃ C : ℝ≥0, ∀ t : ℝ, 0 ≤ t →
      LipschitzOnWith C (scaledTensorReaction (E := E) t) (Metric.closedBall 0 R) := by
  obtain ⟨C, hC⟩ := (contDiff_id.add (contDiff_tensorReaction (E := E))).contDiffOn
    |>.exists_lipschitzOnWith (by simp) (convex_closedBall (0 : TensorFiber E 2) R)
      (isCompact_closedBall 0 R)
  refine ⟨C, fun t ht => LipschitzOnWith.of_dist_le_mul fun T hT S hS => ?_⟩
  have ht0 : 0 ≤ (1 + t)⁻¹ := inv_nonneg.mpr (by linarith)
  have ht1 : (1 + t)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr (by linarith)
  calc
    dist (scaledTensorReaction t T) (scaledTensorReaction t S) =
        (1 + t)⁻¹ * dist (T + tensorReaction T) (S + tensorReaction S) := by
      simp only [scaledTensorReaction, dist_eq_norm, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg ht0]
    _ ≤ dist (T + tensorReaction T) (S + tensorReaction S) :=
      mul_le_of_le_one_left dist_nonneg ht1
    _ ≤ C * dist T S := hC.dist_le_mul T hT S hS

theorem exists_uniform_lipschitzOnWith_scaledTensorReaction
    {B : Type*} {V : B → Type*} [∀ x, NormedAddCommGroup (V x)]
    [∀ x, InnerProductSpace ℝ (V x)] [∀ x, FiniteDimensional ℝ (V x)]
    (hn : ∀ x, Module.finrank ℝ (V x) = 3) (R : ℝ) :
    ∃ C : ℝ≥0, ∀ x t, 0 ≤ t →
      LipschitzOnWith C (scaledTensorReaction (E := V x) t) (Metric.closedBall 0 R) := by
  obtain ⟨C, hC⟩ := exists_lipschitzOnWith_scaledTensorReaction
    (E := EuclideanSpace ℝ (Fin 3)) R
  refine ⟨C, fun x t ht => ?_⟩
  let b : OrthonormalBasis (Fin 3) ℝ (V x) :=
    (stdOrthonormalBasis ℝ (V x)).reindex (finCongr (hn x))
  let e := transport b.repr 2
  apply LipschitzOnWith.of_dist_le_mul
  intro T hT S hS
  have hT' : e T ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hT
  have hS' : e S ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hS
  have h := (hC t ht).dist_le_mul (e T) hT' (e S) hS'
  simpa only [e, scaledTensorReaction_transport, LinearIsometryEquiv.dist_map] using h

theorem tensorReaction_support_nonpos
    (hn : Module.finrank ℝ E = 3) {t : ℝ} (ht : 0 ≤ t)
    {T : TensorFiber E 2} (hT : T ∈ tensorRegion hn 0)
    (l : (TensorFiber E 2) →L[ℝ] ℝ)
    (hsupport : ∀ S ∈ tensorRegion hn 0, l (S - T) ≤ 0) :
    l ((1 + t)⁻¹ • (T + tensorReaction T)) ≤ 0 := by
  let A : E →L[ℝ] E := operatorTensorEquiv.symm T
  let l' : (E →L[ℝ] E) →L[ℝ] ℝ :=
    l.comp (operatorTensorEquiv (E := E)).toContinuousLinearMap
  have hA : A ∈ continuousRegion hn 0 := hT
  have hsupport' : ∀ B ∈ continuousRegion hn 0, l' (B - A) ≤ 0 := by
    intro B hB
    have hmem : operatorTensorEquiv B ∈ tensorRegion hn 0 := by
      change operatorTensorEquiv.symm (operatorTensorEquiv B) ∈ continuousRegion hn 0
      simpa using hB
    change l (operatorTensorEquiv (B - A)) ≤ 0
    rw [map_sub]
    simpa only [A, ContinuousLinearEquiv.apply_symm_apply] using
      hsupport (operatorTensorEquiv B) hmem
  have h := scaled_reaction_support_nonpos hn ht hA l' hsupport'
  change l (operatorTensorEquiv
    ((1 + t)⁻¹ • (A +
      (endomorphismReaction A.toLinearMap).toContinuousLinearMap))) ≤ 0 at h
  simpa [tensorReaction, A, l', map_add, map_smul] using h


theorem scaledTensorReaction_inner_nonpos
    (hn : Module.finrank ℝ E = 3) {t : ℝ} (ht : 0 ≤ t)
    {q : TensorFiber E 2 × TensorFiber E 2}
    (hq : q ∈ Poincare.Parabolic.unitSupportSet (tensorRegion hn 0)) :
    ⟪q.2, scaledTensorReaction t q.1⟫_ℝ ≤ 0 := by
  exact tensorReaction_support_nonpos hn ht hq.1
    (innerSL ℝ q.2) hq.2.2

end

end Poincare.HamiltonIvey
