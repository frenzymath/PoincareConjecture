import PoincareConjecture.Proofs.M08.ContinuationEnvelope
import PoincareConjecture.Proofs.M08.ContinuationPastEndpoint
import PoincareConjecture.Proofs.M08.ContinuationRecovery
import PoincareConjecture.Proofs.M08.ContinuationBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

theorem exists_continuation_to_zero {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax : ℝ) {a₀ c b : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₀c : a₀ < c) (hcb : c < b) (hcm : c ^ 2 < τmax)
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (htime : ∀ s ∈ Ioo 0 b, T - s ^ 2 ∈ interior J) (α₀ : ℝ → M)
    (hα₀ : IsContinuationCurve F T α₀ (Ioo a₀ b)) :
    ∃ β : ℝ → M, IsContinuationCurve F T β (Ioo 0 b) ∧
      ContMDiffWithinAt (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β (Ici 0) 0 ∧
      EqOn β α₀ (Ioo c b) := by
  have hc : 0 < c := ha₀.trans_lt ha₀c
  obtain ⟨a, ha, hac, α, hα, hαtail, hmin⟩ := exists_continuation_envelope F hM04 T
    ha₀ ha₀c hcb (fun s hs ↦ interior_subset (htime s hs)) α₀ hα₀
  have htimeU (s : ℝ) (hs : s ∈ Ioo a b) : T - s ^ 2 ∈ interior J :=
    htime s ⟨ha.trans_lt hs.1, hs.2⟩
  obtain ⟨E, hE⟩ := continuationCurve_regularizedEuler F hM04 T isOpen_Ioo hα htimeU
  obtain ⟨D, hD, hbound⟩ := exists_uniform_continuation_referenceSpeedSq_bound
    F hM04 T τmax c hc hcm hwindow hcurvature
  let L := D * (continuationSpeedSq F T α (Ioo a b) c + 1)
  have hL : 0 ≤ L := mul_nonneg hD.le
    (by linarith [continuationSpeedSq_nonneg F T α (Ioo a b) c])
  have hspeed (s : ℝ) (hs : s ∈ Ioc a c) : referenceSpeedSq (F.metric T) α s ≤ L :=
    hbound a b α ha hac hcb hα.smooth (fun r hr ↦ interior_subset (htimeU r hr)) E hE s hs
  have hg : MetricComplete (F.metric T) := hcurvature.1 T
    ⟨sub_le_self T ((sq_nonneg c).trans_lt hcm).le, le_rfl⟩
  have htimeC (s : ℝ) (hs : s ∈ Icc a c) : T - s ^ 2 ∈ J := by
    apply hwindow
    have hs0 : 0 ≤ s := ha.trans hs.1
    have hs2 : s ^ 2 ≤ c ^ 2 := (sq_le_sq₀ hs0 hc.le).mpr hs.2
    exact ⟨by linarith, sub_le_self T (sq_nonneg s)⟩
  obtain ⟨β, d, Pbar, hβc, hβα, hβsmooth, had, hdc, hsrc, hphaseSmooth,
      hmomentum, hphase⟩ := exists_continuation_endpoint_phase F hM04 T (F.metric T) hg
        hac hcb hL α hα hspeed htimeC
  have ha0 : a = 0 := by
    by_contra hne
    have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
    obtain ⟨e, he, hea, δ, hδ, hδα⟩ := exists_continuation_past_positive_endpoint
      F hM04 T ha' had (hdc.trans hcb) htime α β hα hβα (β a) hsrc Pbar hphase
    have hδtail : EqOn δ α₀ (Ioo c b) := by
      intro r hr
      exact (hδα ⟨hac.trans hr.1, hr.2⟩).trans (hαtail hr)
    exact (not_le_of_gt hea) (hmin e he (hea.trans hac) δ hδ hδtail)
  subst a
  refine ⟨β, hα.congr isOpen_Ioo (fun s hs ↦ hβα hs.1), ?_, ?_⟩
  · exact (hβsmooth 0 ⟨le_rfl, hc.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hc)
  · intro s hs
    exact (hβα (hc.trans hs.1)).trans (hαtail hs)

end PoincareConjecture.M08
