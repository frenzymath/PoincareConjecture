import PoincareConjecture.Proofs.M35.Uniqueness.KillingPreservation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem positive_vector_heat_preserves_killing
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB : 0 ≤ B)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ s, ContDiff ℝ ∞ (X s))
    (hJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ioo 0 G.lifetime ×ˢ univ))
    (hdefect : ContinuousOn (fun p : ℝ × StandardCapSpace =>
      ((G.flow.metric p.1).tensorNorm
        (killingDefectTensor (G.flow.connection p.1) (X p.1)) p.2) ^ 2)
      (Icc 0 T ×ˢ univ))
    (hinit : ∀ x u v, DeTurckNative.metricLieDerivative (G.flow.connection 0) (X 0) x u v = 0)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x,
      ((G.flow.metric t).tensorNorm ((G.flow.connection t).covariantTensorDerivative
        (killingCovector (G.flow.metric t) (X t))) x) ^ 2 ≤ B)
    (hheat : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => X s x)
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) x
          ((G.flow.metric t).orthonormalBasis x i)
          ((G.flow.metric t).orthonormalBasis x i))
        (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (Ico 0 G.lifetime) t) :
    ∀ t ∈ Icc 0 T, ∀ x u v,
      DeTurckNative.metricLieDerivative (G.flow.connection t) (X t) x u v = 0 := by
  have hz := bounded_lichnerowicz_zero P G hT hTlt
    (show 0 ≤ 4 * B from mul_nonneg (by norm_num) hB)
    (fun s => killingDefectTensor (G.flow.connection s) (X s))
    (fun s => isSmoothCovariantTensor_killingDefectTensor _ _ (hX s)) hdefect
    (fun x v => hinit x (v 0) (v 1))
    (fun t ht x => (killingDefectTensor_normSq_le (G.flow.connection t) (X t) (hX t) x).trans
      (mul_le_mul_of_nonneg_left (hbound t ht x) (by norm_num)))
    (fun t ht x v => killingDefectTensor_heat_hasDerivAt_positive G
      ⟨ht.1, ht.2.trans_lt hTlt⟩ X hX hJoint (hheat t ht) x v)
  exact fun t ht x u v => hz t ht x ![u, v]

private theorem constant_of_positive_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T : ℝ} (hT : 0 < T) (f : ℝ → E)
    (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt f 0 t) :
    ∀ t ∈ Icc 0 T, f t = f 0 := by
  have hm : T / 2 ∈ Ioo 0 T := ⟨by linarith, by linarith⟩
  have he : EqOn f (fun _ => f (T / 2)) (Ioo 0 T) := by
    intro t ht
    have hn := (convex_Ioo (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (C := 0) (fun s hs => (hd s hs).hasDerivWithinAt) (fun _ _ => by simp) hm ht
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hn
  have hec := he.of_subset_closure hc continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hT.ne])
  exact fun t ht => (hec ht).trans (hec ⟨le_rfl, hT.le⟩).symm

theorem positive_vector_heat_initial_killing_stationary
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB : 0 ≤ B)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ s, ContDiff ℝ ∞ (X s))
    (hJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ioo 0 G.lifetime ×ˢ univ))
    (hcont : ∀ x, ContinuousOn (fun t => X t x) (Icc 0 T))
    (hdefect : ContinuousOn (fun p : ℝ × StandardCapSpace =>
      ((G.flow.metric p.1).tensorNorm
        (killingDefectTensor (G.flow.connection p.1) (X p.1)) p.2) ^ 2)
      (Icc 0 T ×ˢ univ))
    (hinit : ∀ x u v, DeTurckNative.metricLieDerivative (G.flow.connection 0) (X 0) x u v = 0)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x,
      ((G.flow.metric t).tensorNorm ((G.flow.connection t).covariantTensorDerivative
        (killingCovector (G.flow.metric t) (X t))) x) ^ 2 ≤ B)
    (hheat : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => X s x)
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) x
          ((G.flow.metric t).orthonormalBasis x i)
          ((G.flow.metric t).orthonormalBasis x i))
        (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (Ico 0 G.lifetime) t) :
    (∀ t ∈ Icc 0 T, ∀ x, X t x = X 0 x) ∧
      ∀ t ∈ Icc 0 T, ∀ x u v,
        DeTurckNative.metricLieDerivative (G.flow.connection t) (X 0) x u v = 0 := by
  have hk := positive_vector_heat_preserves_killing P G hT hTlt hB X hX hJoint
    hdefect hinit hbound hheat
  have he (x : StandardCapSpace) : ∀ t ∈ Icc 0 T, X t x = X 0 x := by
    apply constant_of_positive_derivative hT (fun t => X t x) (hcont x)
    intro t ht
    have hz := killing_hessian_trace_add_ricciSharp_eq_zero
      (G.flow.connection t) (X t) (hX t) (hk t ⟨ht.1.le, ht.2.le⟩) x
    have hd := (hheat t ⟨ht.1, ht.2.le⟩ x).hasDerivAt
      (mem_of_superset (isOpen_Ioo.mem_nhds
        (show t ∈ Ioo 0 G.lifetime from ⟨ht.1, ht.2.trans hTlt⟩)) Ioo_subset_Ico_self)
    simpa only [hz] using hd
  refine ⟨fun t ht x => he x t ht, ?_⟩
  intro t ht x u v
  have hf : X t = X 0 := funext (fun y => he y t ht)
  rw [← hf]
  exact hk t ht x u v

end PoincareConjecture.M35.Uniqueness
