import PoincareConjecture.Proofs.M35.Uniqueness.KillingLichnerowicz
import PoincareConjecture.Proofs.M35.Uniqueness.KillingDefectRegularity
import PoincareConjecture.Proofs.M35.Uniqueness.BoundedLichnerowicz

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem bounded_vector_heat_preserves_killing
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB : 0 ≤ B)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ s, ContDiff ℝ ∞ (X s))
    (hJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ico 0 G.lifetime ×ˢ univ))
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
  have hsub : Icc 0 T ⊆ Ico 0 G.lifetime :=
    fun _ hs => ⟨hs.1, hs.2.trans_lt hTlt⟩
  have hcont := (killingDefectTensor_normSq_joint G X hX hJoint).continuousOn.mono
    (prod_mono hsub Subset.rfl)
  have hz := bounded_lichnerowicz_zero P G hT hTlt
    (show 0 ≤ 4 * B from mul_nonneg (by norm_num) hB)
    (fun s => killingDefectTensor (G.flow.connection s) (X s))
    (fun s => isSmoothCovariantTensor_killingDefectTensor _ _ (hX s))
    hcont (fun x v => hinit x (v 0) (v 1))
    (fun t ht x => (killingDefectTensor_normSq_le (G.flow.connection t) (X t) (hX t) x).trans
      (mul_le_mul_of_nonneg_left (hbound t ht x) (by norm_num)))
    (fun t ht x v => killingDefectTensor_heat_hasDerivAt G
      ⟨ht.1, ht.2.trans_lt hTlt⟩ X hX hJoint (hheat t ht) x v)
  intro t ht x u v
  exact hz t ht x ![u, v]

theorem bounded_vector_heat_initial_killing_stationary
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB : 0 ≤ B)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ s, ContDiff ℝ ∞ (X s))
    (hJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ico 0 G.lifetime ×ˢ univ))
    (hinit : ∀ x u v, DeTurckNative.metricLieDerivative (G.flow.connection 0) (X 0) x u v = 0)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x,
      ((G.flow.metric t).tensorNorm ((G.flow.connection t).covariantTensorDerivative
        (killingCovector (G.flow.metric t) (X t))) x) ^ 2 ≤ B)
    (hheat : ∀ t ∈ Icc 0 T, ∀ x, HasDerivWithinAt (fun s => X s x)
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) x
          ((G.flow.metric t).orthonormalBasis x i)
          ((G.flow.metric t).orthonormalBasis x i))
        (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (Ico 0 G.lifetime) t) :
    (∀ t ∈ Icc 0 T, ∀ x, X t x = X 0 x) ∧
      ∀ t ∈ Icc 0 T, ∀ x u v,
        DeTurckNative.metricLieDerivative (G.flow.connection t) (X 0) x u v = 0 := by
  have hk := bounded_vector_heat_preserves_killing P G hT hTlt hB X hX hJoint hinit hbound
    (fun t ht => hheat t ⟨ht.1.le, ht.2⟩)
  have hsub : Icc 0 T ⊆ Ico 0 G.lifetime :=
    fun _ hs => ⟨hs.1, hs.2.trans_lt hTlt⟩
  have heq (t) (ht : t ∈ Icc 0 T) (x) : X t x = X 0 x :=
    evolving_killing_field_stationary G hT.le X (fun t _ => hX t) hk
      (fun t ht x => (hheat t ht x).mono hsub) ht x
  refine ⟨heq, ?_⟩
  intro t ht x u v
  have hf : X t = X 0 := funext (heq t ht)
  rw [← hf]
  exact hk t ht x u v

end PoincareConjecture.M35.Uniqueness
