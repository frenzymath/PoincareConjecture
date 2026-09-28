import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.UniformScalarJets
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.ChartBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.RegularPointedMetricConvergence

open SpacetimeBounds

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)]
  {g : ∀ k, RiemannianMetric 3 (M k)} {p : ∀ k, M k}




theorem jetScalarCurvature_chart_eq_of_mem_exhaustion
    (G : RegularPointedMetricConvergence g p) (D : ∀ k, LeviCivitaData (g k)) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : G.limitCarrier.carrier) (k : ℕ) (x : EuclideanSpace ℝ (Fin 3)),
      x ∈ (extChartAt (𝓡 3) q).target →
      (extChartAt (𝓡 3) q).symm x ∈ G.exhaustion k →
      tube.jetScalarCurvature (metricTwoJet ((g (G.subsequence k)).pullbackCoefficients
        (G.embedding k ∘ (extChartAt (𝓡 3) q).symm)) x) =
        (D (G.subsequence k)).scalarCurvature
          (G.embedding k ((extChartAt (𝓡 3) q).symm x)) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q k x hx hstage
  let c := extChartAt (𝓡 3) q
  let U := c.target ∩ c.symm ⁻¹' G.exhaustion k
  have hU : IsOpen U :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) (G.exhaustion_open k)
  have hchart (y) (hy : y ∈ U) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm y :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds hy.1)
  have hmap (y) (hy : y ∈ U) :
      IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (G.embedding k) (c.symm y) :=
    G.embedding_smooth k ⟨c.symm y, hy.2⟩
  have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (G.embedding k ∘ c.symm) U :=
    fun y hy => ((hmap y hy).contMDiffAt.comp y (hchart y hy)).contMDiffWithinAt
  have hinvertible (y) (hy : y ∈ U) :
      (mfderiv (𝓡 3) (𝓡 3) (G.embedding k ∘ c.symm) y).IsInvertible := by
    rw [mfderiv_comp y ((hmap y hy).mdifferentiableAt (by simp))
      ((hchart y hy).mdifferentiableAt (by simp))]
    have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm hy.1
    exact (show (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) (c.symm y)).IsInvertible from
      ⟨(hmap y hy).mfderivToContinuousLinearEquiv (by simp), rfl⟩).comp hi
  exact tube.jetScalarCurvature_metricTwoJet_pullback (D (G.subsequence k))
    hU hsmooth hinvertible ⟨hx, hstage⟩




theorem tendstoUniformlyOn_chart_scalarCurvature
    (G : RegularPointedMetricConvergence g p) (D : ∀ k, LeviCivitaData (g k)) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (D0 : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier)
      (K : Set (EuclideanSpace ℝ (Fin 3))), IsCompact K →
      K ⊆ (extChartAt (𝓡 3) q).target →
      TendstoUniformlyOn
        (fun k x => (D (G.subsequence k)).scalarCurvature
          (G.embedding k ((extChartAt (𝓡 3) q).symm x)))
        (fun x => D0.scalarCurvature ((extChartAt (𝓡 3) q).symm x)) atTop K := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q K hK htarget
  let c := extChartAt (𝓡 3) q
  let B0 := G.limitMetric.pullbackCoefficients c.symm
  have hcontinuous : ContinuousOn (metricTwoJet B0) K := by
    intro x hx
    have hB : ContDiffAt ℝ ∞ B0 x :=
      (G.limitMetric.contDiffOn_chartCoefficients q).contDiffAt
        ((isOpen_extChartAt_target q).mem_nhds (htarget hx))
    have hD : ContDiffAt ℝ ∞ (fderiv ℝ B0) x := hB.fderiv_right (by simp)
    have hJ := hB.continuousAt.prodMk
      (hD.continuousAt.prodMk (hD.fderiv_right (m := ∞) (by simp)).continuousAt)
    exact hJ.continuousWithinAt
  have hjets := tendstoUniformlyOn_metricTwoJet_of_uniform_bilinear_jets
    (fun m _ => G.metric_jets q m K hK htarget)
  have hscalar := tendstoUniformlyOn_jetScalarCurvature_of_metricTwoJet hK hcontinuous
    (fun x hx => G.limitMetric.isInvertible_chartCoefficients q (htarget hx)) hjets
  have himage : IsCompact (c.symm '' K) := hK.image_of_continuousOn
    ((contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono htarget)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun j => subset_closure.trans (G.exhaustion_step j))
  obtain ⟨j, hj⟩ := himage.elim_directed_cover G.exhaustion G.exhaustion_open
    (by rw [G.exhaustion_covers]; exact subset_univ _) hmono.directed_le
  have hlimit (x) (hx : x ∈ K) : tube.jetScalarCurvature (metricTwoJet B0 x) =
      D0.scalarCurvature (c.symm x) :=
    tube.jetScalarCurvature_metricTwoJet_pullback D0
      (isOpen_extChartAt_target q) (contMDiffOn_extChartAt_symm q)
      (fun y hy => by
        simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
          isInvertible_mfderivWithin_extChartAt_symm hy) (htarget hx)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro delta hdelta
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hscalar delta hdelta,
    eventually_ge_atTop j] with k hk hjk
  intro x hx
  have hsource := G.jetScalarCurvature_chart_eq_of_mem_exhaustion D q k x
    (htarget hx) (hmono hjk (hj (mem_image_of_mem _ hx)))
  simpa only [hlimit x hx, hsource] using hk x hx

end PoincareConjecture.M28.RegularPointedMetricConvergence
