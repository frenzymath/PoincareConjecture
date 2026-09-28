import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.LimitReference
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.LimitInverse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

include B in
theorem terminal_nonempty_of_core_nonempty (Q : SingularLimitConclusion H)
    (hcore : I.controlled_core.Nonempty) : Nonempty (Q.extension.extended.slice T).carrier := by
  obtain ⟨y, hy, _⟩ := B.core_status_iff.mp hcore
  have hy' : y ∈ range Q.terminal_source := Q.terminal_source_image.symm ▸ hy
  obtain ⟨z, _⟩ := hy'
  exact ⟨z⟩

theorem reference_surgeryMetricCoefficient (σ t : Ico H.reference.tMinus T)
    (q : (F.slice σ.1).carrier) (a b : Fin 3) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt (𝓡 3) q).target) :
    surgeryMetricCoefficient (H.reference.flow.metric t.1)
      (B.reference_identify σ ∘ (extChartAt (𝓡 3) q).symm) a b z =
      singularMetricCoefficient ((I.last_slab.rebaseFlow (B.referenceRebaseTime σ)).metric t.1)
        q a b z := by
  have hc := ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds hz)).mdifferentiableAt (by simp)
  change (H.reference.flow.metric t.1).inner
    (B.reference_identify σ ((extChartAt (𝓡 3) q).symm z))
    (mfderiv (𝓡 3) (𝓡 3) (B.reference_identify σ ∘ (extChartAt (𝓡 3) q).symm) z _)
    (mfderiv (𝓡 3) (𝓡 3) (B.reference_identify σ ∘ (extChartAt (𝓡 3) q).symm) z _) = _
  rw [mfderiv_comp z ((B.reference_identify σ).contMDiff.mdifferentiable (by simp) _) hc]
  exact B.reference_metric_rebase σ t ((extChartAt (𝓡 3) q).symm z) _ _

theorem reference_surgeryMetricLimitOn (Q : SingularLimitConclusion H)
    [Nonempty (Q.extension.extended.slice T).carrier] (σ : Ico H.reference.tMinus T) :
    SurgeryMetricLimitOn (F.slice σ.1) (Q.extension.extended.slice T)
      (I.last_slab.rebaseFlow (B.referenceRebaseTime σ)).metric Q.terminal_metric
      (B.referenceLimitIdentify Q σ).map
      (B.reference_identify σ ⁻¹' H.reference.regularLimitSet) T := by
  intro q _ K hK hKt hKU k a b ε hε
  let c := extChartAt (𝓡 3) q
  let p := B.reference_identify σ ∘ c.symm
  have hp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ p c.target :=
    (B.reference_identify σ).contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm (n := ∞) q)
  let V := c.target ∩ p ⁻¹' H.reference.regularLimitSet
  have hV : IsOpen V := hp.continuousOn.isOpen_inter_preimage
    (isOpen_extChartAt_target q) Q.regular_open
  have hKV : K ⊆ V := fun x hx => ⟨hKt hx, hKU ⟨x, hx, rfl⟩⟩
  have hconv := Q.sourceInverseCoordinate_scalar_tendstoUniformlyOn hV
    (hp.mono inter_subset_left) (fun _ hx => hx.2) k a b K hK hKV
  have hconv' : TendstoUniformlyOn
      (fun t => iteratedFDeriv ℝ k
        (singularMetricCoefficient ((I.last_slab.rebaseFlow (B.referenceRebaseTime σ)).metric t)
          q a b))
      (iteratedFDeriv ℝ k
        (surgeryMetricCoefficient Q.terminal_metric (Q.sourceInverse ∘ p) a b)) (𝓝[<] T) K := by
    apply hconv.congr
    filter_upwards [Ico_mem_nhdsLT H.reference.tMinus_lt] with t ht
    intro z hz
    have heq : surgeryMetricCoefficient (H.reference.flow.metric t) p a b =ᶠ[𝓝 z]
        singularMetricCoefficient ((I.last_slab.rebaseFlow (B.referenceRebaseTime σ)).metric t)
          q a b := by
      filter_upwards [(isOpen_extChartAt_target q).mem_nhds (hKt hz)] with y hy
      exact B.reference_surgeryMetricCoefficient σ ⟨t, ht⟩ q a b hy
    exact (heq.iteratedFDeriv ℝ k).self_of_nhds
  obtain ⟨t₀, ht₀, hbound⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    (Metric.tendstoUniformlyOn_iff.mp hconv' ε hε)
  refine ⟨T - t₀, sub_pos.mpr ht₀, fun t ht htT x hx => ?_⟩
  have h := hbound ⟨by linarith, htT⟩ x hx
  simpa only [dist_eq_norm, norm_sub_rev, p, c, referenceLimitIdentify, Function.comp_def] using h

end PoincareConjecture.RepairedContinuationLimitBridge
