import PoincareConjecture.Proofs.M35.Thm12_28.TerminalMetricConvergence
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderMetricComparison
import PoincareConjecture.Proofs.M03.MetricCompactBounds

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

private theorem chartCoefficients_pos
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (q : M) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ (extChartAt (𝓡 3) q).target)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : v ≠ 0) :
    0 < g.pullbackCoefficients (extChartAt (𝓡 3) q).symm p v v := by
  apply g.pos
  intro hzero
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hp
  have hleft := congrArg
    (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => A v) hcomp
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hleft
  have hmap := congrArg (fun w : EuclideanSpace ℝ (Fin 3) =>
    mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q)
      ((extChartAt (𝓡 3) q).symm p) w) hzero
  exact hv (hleft.symm.trans (hmap.trans (map_zero _)))

theorem blowupSequence_terminal_metric_comparison (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (q : L.limit.sliceCarrier.carrier) (j : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (hKU : K ⊆ {p | p ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm p ∈ L.exhaustion.space j})
    (eta : ℝ) (heta : 0 < eta) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ p ∈ K, ∀ v : EuclideanSpace ℝ (Fin 3),
      |(blowupSequence P E t x ht hR).scale (L.subsequence k) *
        (E.flow.metric (t (L.subsequence k))).pullbackCoefficients
          ((fun y => ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val) ∘
            (extChartAt (𝓡 3) q).symm) p v v -
        (L.limit.flow.metric 0).pullbackCoefficients (extChartAt (𝓡 3) q).symm p v v| ≤
      eta * (L.limit.flow.metric 0).pullbackCoefficients
        (extChartAt (𝓡 3) q).symm p v v := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  let G := (L.limit.flow.metric 0).pullbackCoefficients (extChartAt (𝓡 3) q).symm
  have hGreg : ContinuousOn G K :=
    ((L.limit.flow.metric 0).contDiffOn_chartCoefficients q).continuousOn.mono
      (fun _ hp => (hKU hp).1)
  obtain ⟨c, _, hc, _, hG⟩ := Proofs.M03.exists_pos_uniform_bilinear_bounds hK hGreg
    (fun p hp _ hv => chartCoefficients_pos (L.limit.flow.metric 0) q (hKU hp).1 hv)
  have hdelta : 0 < eta * c / 3 := div_pos (mul_pos heta hc) (by norm_num)
  obtain ⟨N, hjN, hN⟩ := blowupSequence_terminal_spatial_CInfinity P E t x ht hR L q j 0
    K hK hKU (eta * c / 3) hdelta
  refine ⟨N, hjN, ?_⟩
  intro k hk p hp v
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  let f : L.limit.sliceCarrier.carrier → StandardCapSpace :=
    fun y => ((L.embedding k).forward 0 hzero y).val
  let B := Q • (E.flow.metric (t (L.subsequence k))).pullbackCoefficients
    (f ∘ (extChartAt (𝓡 3) q).symm) p
  have hpoint := L.exhaustion.space_increasing (hjN.trans hk) (hKU hp).2
  have htime := ((L.embedding k).forward 0 hzero L.limit.base).property
  have hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f ((extChartAt (𝓡 3) q).symm p) :=
    ((sliceDiffeomorph htime).contMDiff.comp_contMDiffOn
      ((L.embedding k).forward_smooth 0 hzero)).contMDiffAt
        ((L.exhaustion.space_open k).mem_nhds hpoint)
  have hcomp (a b : Fin 3) :
      |(B - G p) (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)| ≤ eta * c / 3 := by
    have he := hN k hk a b p hp
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map, Real.norm_eq_abs] at he
    have hco := fixedCylinderMetricCoefficient_eq_pullback E.flow.base.flow
      L.limit.sliceCarrier (t (L.subsequence k)) Q f q a b (0, p) (hKU hp).1 hf
    simp only [zero_div, add_zero] at hco
    exact (congrArg (fun z => |z - G p (EuclideanSpace.basisFun (Fin 3) ℝ a)
      (EuclideanSpace.basisFun (Fin 3) ℝ b)|) hco).symm.trans_le he.le
  have herr := M35.abs_bilinear_le_of_components (B - G p) hdelta.le hcomp v
  have hmodel := mul_le_mul_of_nonneg_left (hG p hp v).1 heta.le
  change |B v v - G p v v| ≤ eta * G p v v
  change |B v v - G p v v| ≤ 3 * (eta * c / 3) * ‖v‖ ^ 2 at herr
  nlinarith

end PoincareConjecture.M35.OrdinaryRealization
