import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Bernstein.UniformGradient
import PoincareConjecture.Proofs.M35.Uniqueness.LocalLichnerowiczSmall
import PoincareConjecture.Proofs.M35.Uniqueness.KillingPreservation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem exists_raw_local_killing_defect_small
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B J δ : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hδ : 0 < δ) {C₀ : Set StandardCapSpace} (hC₀ : IsCompact C₀) :
    ∃ E : Set StandardCapSpace, IsCompact E ∧ C₀ ⊆ interior E ∧
      ∀ X : ℝ → StandardCapSpace → StandardCapSpace,
      (∀ s, ContDiff ℝ ∞ (X s)) →
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
        (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
          (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ioo 0 G.lifetime ×ˢ univ) →
      ContinuousOn (Function.uncurry (vectorHeatJetEnergy G X 0)) (Icc 0 T ×ˢ E) →
      ContinuousOn (Function.uncurry (vectorHeatJetEnergy G X 1)) (Icc 0 T ×ˢ E) →
      ContinuousOn (fun p : ℝ × StandardCapSpace =>
        ((G.flow.metric p.1).tensorNorm
          (killingDefectTensor (G.flow.connection p.1) (X p.1)) p.2) ^ 2) (Icc 0 T ×ˢ E) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ E, (G.flow.metric t).inner x (X t x) (X t x) ≤ B) →
      (∀ x ∈ E, vectorHeatJetEnergy G X 1 0 x ≤ J) →
      (∀ x ∈ E, ∀ u v, DeTurckNative.metricLieDerivative (G.flow.connection 0) (X 0) x u v = 0) →
      (∀ t ∈ Ioc 0 T, ∀ x ∈ E, ∀ᶠ y in 𝓝 x,
        HasDerivWithinAt (fun s => X s y)
          (@Add.add StandardCapSpace inferInstance
            (∑ i, fieldHessian (G.flow.connection t) (X t) y
              ((G.flow.metric t).orthonormalBasis y i)
              ((G.flow.metric t).orthonormalBasis y i))
            (RicciFlow.ricciSharp (G.flow.connection t) y (X t y))) (Ico 0 G.lifetime) t) →
      ∀ t ∈ Icc 0 T, ∀ x ∈ C₀,
        ((G.flow.metric t).tensorNorm
          (killingDefectTensor (G.flow.connection t) (X t)) x) ^ 2 ≤ δ := by
  obtain ⟨C, hC, hgradient⟩ :=
    exists_uniform_local_vector_heat_gradient_bound P G hT hTlt hB hJ
  obtain ⟨S, hS, hCS, hsmall⟩ := exists_raw_local_lichnerowicz_small P G hT hTlt
    (show 0 ≤ 4 * C from mul_nonneg (by norm_num) hC) hδ hC₀
  obtain ⟨E, hE, hSE, hgradE⟩ := hgradient S hS
  have hSE' : S ⊆ E := hSE.trans interior_subset
  refine ⟨E, hE, hCS.trans hSE, ?_⟩
  intro X hX hJoint hcont0 hcont1 hdefect hbound hinit hkill hheat
  have hg := hgradE X hX hJoint hcont0 hcont1 hbound hinit hheat
  let H := fun s => killingDefectTensor (G.flow.connection s) (X s)
  refine hsmall H (fun s => isSmoothCovariantTensor_killingDefectTensor _ _ (hX s))
    (hdefect.mono (prod_mono Subset.rfl hSE'))
    (fun x hx v => hkill x (hSE' hx) (v 0) (v 1)) ?_ ?_
  · intro t ht x hx
    have hgrad : vectorHeatJetEnergy G X 1 t x ≤ C := by
      have henergy := vectorHeatJetEnergy_nonneg G X 1 t x
      have hgx := hg t ht x hx
      nlinarith only [henergy, hgx, ht.1]
    exact (killingDefectTensor_normSq_le (G.flow.connection t) (X t) (hX t) x).trans
      (mul_le_mul_of_nonneg_left hgrad (by norm_num))
  · intro t ht x hx v
    exact killingDefectTensor_heat_hasDerivAt_of_eventually_heat G
      ⟨ht.1, ht.2.trans_lt hTlt⟩ X hX hJoint x (hheat t ht x (hSE' hx)) v

end PoincareConjecture.M35.Uniqueness
