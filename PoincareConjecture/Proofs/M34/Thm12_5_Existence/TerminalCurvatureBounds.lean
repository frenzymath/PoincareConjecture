import PoincareConjecture.Proofs.M34.Thm12_5_Existence.TerminalClosedFlow
import PoincareConjecture.Proofs.M34.Standard.FlowCurvatureContinuity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.PartialFlowTerminalJets

variable {g0 : StandardInitialMetric} {F : PartialStandardCapFlow g0} {S : ℝ}
  (L : PartialFlowTerminalJets F S) (P : RicciFlowCurvatureTheory.{0})
  (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hB : 0 < B)
  (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
    (F.flow.connection t).curvatureTensorNorm x ≤ B)



theorem closedFlow_curvatureDerivative_le (m : ℕ) {C : ℝ}
    (hbound : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureDerivativeNorm m x ≤ C)
    {t : ℝ} (ht : t ∈ Icc 0 S) (x : StandardCapSpace) :
    ((L.closedFlow P E0 hS hSF hB hfull).connection t).curvatureDerivativeNorm m x ≤ C := by
  let H := L.closedFlow P E0 hS hSF hB hfull
  have hold (s : ℝ) (hs : s ∈ Ico 0 S) :
      (H.connection s).curvatureDerivativeNorm m x ≤ C := by
    have heq := congrArg (fun data : Σ g : RiemannianMetric 3 StandardCapSpace,
      LeviCivitaData g => data.2.curvatureDerivativeNorm m x)
      (L.closedMetricConnection_of_lt P E0 hS hSF hB hfull hs.2)
    exact heq.le.trans (hbound s hs x)
  rcases ht.2.eq_or_lt with heq | hlt
  · subst t
    have hc : ContinuousOn (fun s => (H.connection s).curvatureDerivativeNorm m x)
        (Icc 0 S) := by
      apply (H.continuousOn_curvatureDerivativeNorm m).comp
        (continuous_id.prodMk continuous_const).continuousOn
      exact fun _ hs => ⟨hs, mem_univ x⟩
    have hleft : Tendsto (fun s : ℝ => s) (𝓝[<] S) (𝓝[Icc 0 S] S) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_id.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [Ico_mem_nhdsLT hS] with s hs
      exact ⟨hs.1, hs.2.le⟩
    apply le_of_tendsto ((hc S ⟨hS.le, le_rfl⟩).tendsto.comp hleft)
    filter_upwards [Ico_mem_nhdsLT hS] with s hs
    exact hold s hs
  · exact hold t ⟨ht.1, hlt⟩



theorem closedFlow_curvatureTensorNorm_le {t : ℝ} (ht : t ∈ Icc 0 S)
    (x : StandardCapSpace) :
    ((L.closedFlow P E0 hS hSF hB hfull).connection t).curvatureTensorNorm x ≤ B := by
  have h := L.closedFlow_curvatureDerivative_le P E0 hS hSF hB hfull 0
    (C := B) (fun s hs y => by
      rw [LeviCivitaData.curvatureDerivativeNorm_zero]
      exact hfull s hs y) ht x
  simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using h



theorem closedFlow_curvatureDerivative_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 S, ∀ x : StandardCapSpace,
      ((L.closedFlow P E0 hS hSF hB hfull).connection t).curvatureDerivativeNorm m x ≤ C := by
  obtain ⟨C, hC, hbound⟩ := partialFlow_curvatureDerivative_bound P E0 F hS hSF hB hfull m
  exact ⟨C, hC, fun _ ht x => L.closedFlow_curvatureDerivative_le P E0 hS hSF hB hfull
    m hbound ht x⟩

end PoincareConjecture.M34.PartialFlowTerminalJets
