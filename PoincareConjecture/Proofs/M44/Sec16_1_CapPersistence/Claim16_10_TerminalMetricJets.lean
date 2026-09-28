import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RetainedBilinearLimit
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_TwoJetModulus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance terminalJetCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance terminalJetCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance terminalTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance terminalTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

theorem tendsto_twoJet_of_surgeryMetricLimitOn
    {A B : GeneralizedSliceCarrier.{u}}
    {g : ℝ → RiemannianMetric 3 A.carrier} {gT : RiemannianMetric 3 B.carrier}
    {f : A.carrier → B.carrier} {V : Set A.carrier} {T : ℝ}
    (hlim : SurgeryMetricLimitOn A B g gT f V T)
    (q : A.carrier) (hq : q ∈ V) {U : Set E} (hU : IsOpen U)
    (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hV : (extChartAt (𝓡 3) q).symm '' U ⊆ V)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f ∘ (extChartAt (𝓡 3) q).symm) U)
    {x : E} (hx : x ∈ U) :
    Tendsto (fun t => metricTwoJet
      ((g t).pullbackCoefficients (extChartAt (𝓡 3) q).symm) x) (𝓝[<] T)
      (𝓝 (metricTwoJet (gT.pullbackCoefficients
        (f ∘ (extChartAt (𝓡 3) q).symm)) x)) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  have hj (j : ℕ) : ∀ᶠ t in 𝓝[<] T,
      ‖iteratedFDeriv ℝ j ((g t).pullbackCoefficients (extChartAt (𝓡 3) q).symm) x -
        iteratedFDeriv ℝ j (gT.pullbackCoefficients
          (f ∘ (extChartAt (𝓡 3) q).symm)) x‖ ≤ eta / 2 := by
    obtain ⟨d, hd, hbound⟩ := bilinear_jets_of_surgeryMetricLimitOn hlim q hq hU
      hchart hV hf j (isCompact_singleton (x := x)) (singleton_subset_iff.mpr hx)
      (half_pos heta)
    filter_upwards [Ioo_mem_nhdsLT (by linarith : T - d < T)] with t ht
    exact (hbound t ht.1 ht.2 x (mem_singleton x)).le
  filter_upwards [hj 0, hj 1, hj 2] with t h0 h1 h2
  rw [dist_eq_norm]
  apply (norm_metricTwoJet_sub_le _ _ x ?_).trans_lt (half_lt_self heta)
  intro j hj
  interval_cases j <;> assumption

end PoincareConjecture.M44
