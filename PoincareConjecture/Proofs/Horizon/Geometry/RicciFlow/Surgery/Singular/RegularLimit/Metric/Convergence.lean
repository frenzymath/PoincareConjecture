import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.CompactConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Terminal









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter Manifold
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem regularRegion_chart_target_regular
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : H.regularRegion P04) :
    (extChartAt (𝓡 3) q).target ⊆ H.regularCoordinateDomain q := by
  intro z hz
  refine ⟨H.regularRegion_chart_target_subset P04 q hz, ?_⟩
  change (extChartAt (𝓡 3) (q : M)).symm z ∈ H.reference.regularLimitSet
  rw [H.regularRegion_chart_inverse P04 q hz]
  exact ((extChartAt (𝓡 3) q).symm z).property


theorem tendstoUniformlyOn_terminalMetric_jets
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : H.regularRegion P04) (m : ℕ)
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hsub : K ⊆ (extChartAt (𝓡 3) q).target) :
    TendstoUniformlyOn
      (fun t => iteratedFDeriv ℝ m ((H.reference.flow.metric t).pullbackCoefficients
        (extChartAt (𝓡 3) (q : M)).symm))
      (iteratedFDeriv ℝ m ((H.terminalMetric P04).pullbackCoefficients
        (extChartAt (𝓡 3) q).symm)) (𝓝[<] T) K := by
  have h := (H.smooth_terminal_coordinate_limit_on_compacts P04 (q : M)).2 m K hK
    (hsub.trans (H.regularRegion_chart_target_regular P04 q))
  apply h.congr_right
  intro z hz
  have hnear := Filter.eventuallyEq_of_mem
    ((isOpen_extChartAt_target q).mem_nhds (hsub hz))
    (H.regularRegion_chartCoefficients_eqOn P04 q)
  exact ((hnear.iteratedFDeriv ℝ m).self_of_nhds).symm

private theorem source_scalar_chart_coefficient
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : H.regularRegion P04) (t : ℝ) (a b : Fin 3)
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ (extChartAt (𝓡 3) q).target) :
    singularTensorCoefficient
      (singularMetricPullback (H.reference.flow.metric t) (Subtype.val : H.regularRegion P04 → M))
      q a b z =
    (H.reference.flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) (q : M)).symm z
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) := by
  dsimp only [singularTensorCoefficient, singularMetricPullback]
  rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
  change (H.reference.flow.metric t).inner ((extChartAt (𝓡 3) q).symm z : M)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z
        (EuclideanSpace.basisFun (Fin 3) ℝ a))
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) = _
  change _ = (H.reference.flow.metric t).inner ((extChartAt (𝓡 3) (q : M)).symm z)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q : M)).symm z
        (EuclideanSpace.basisFun (Fin 3) ℝ a))
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q : M)).symm z
        (EuclideanSpace.basisFun (Fin 3) ℝ b))
  rw [H.regularRegion_chart_inverse P04 q hz, H.regularRegion_chart_mfderiv P04 q hz]
  rfl



theorem compactSingularMetricLimit_terminalMetric
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) :
    CompactSingularMetricLimit H.reference (H.terminalMetric P04)
      (Subtype.val : H.regularRegion P04 → M) := by
  intro q a b m K hK hsub ε hε
  let E := EuclideanSpace ℝ (Fin 3)
  let ev : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ b)).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ a))
  let J := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m => E)
    (E →L[ℝ] E →L[ℝ] ℝ) ℝ ev
  have h := J.uniformContinuous.comp_tendstoUniformlyOn
    (H.tendstoUniformlyOn_terminalMetric_jets P04 q m hK hsub)
  have hm : (m : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  have hsource (t : ℝ) (z : E) (hz : z ∈ K) :
      J (iteratedFDeriv ℝ m ((H.reference.flow.metric t).pullbackCoefficients
        (extChartAt (𝓡 3) (q : M)).symm) z) =
      iteratedFDeriv ℝ m (singularTensorCoefficient
        (singularMetricPullback (H.reference.flow.metric t)
          (Subtype.val : H.regularRegion P04 → M)) q a b) z := by
    have hsm := ((H.reference.flow.metric t).contDiffOn_chartCoefficients (q : M)).contDiffAt
      ((isOpen_extChartAt_target (q : M)).mem_nhds
        (H.regularRegion_chart_target_subset P04 q (hsub hz)))
    rw [show J (iteratedFDeriv ℝ m _ z) =
      iteratedFDeriv ℝ m (ev ∘ (H.reference.flow.metric t).pullbackCoefficients
        (extChartAt (𝓡 3) (q : M)).symm) z from
      (ev.iteratedFDeriv_comp_left hsm hm).symm]
    have heq := Filter.eventuallyEq_of_mem
      ((isOpen_extChartAt_target q).mem_nhds (hsub hz))
      (fun y hy => (H.source_scalar_chart_coefficient P04 q t a b hy).symm)
    exact (heq.iteratedFDeriv ℝ m).self_of_nhds
  have hterminal (z : E) (hz : z ∈ K) :
      J (iteratedFDeriv ℝ m ((H.terminalMetric P04).pullbackCoefficients
        (extChartAt (𝓡 3) q).symm) z) =
      iteratedFDeriv ℝ m (singularMetricCoefficient (H.terminalMetric P04) q a b) z :=
    (ev.iteratedFDeriv_comp_left
      (((H.terminalMetric P04).contDiffOn_chartCoefficients q).contDiffAt
        ((isOpen_extChartAt_target q).mem_nhds (hsub hz))) hm).symm
  have hscalar := (h.congr (Eventually.of_forall fun t z hz => hsource t z hz)).congr_right hterminal
  obtain ⟨s, hsT, hs⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    (Metric.tendstoUniformlyOn_iff.mp hscalar ε hε)
  refine ⟨max s H.reference.tMinus, le_max_right _ _, max_lt hsT H.reference.tMinus_lt, ?_⟩
  intro t ht htT z hz
  have hd := hs ⟨(le_max_left _ _).trans_lt ht, htT⟩ z hz
  simpa only [dist_eq_norm, norm_sub_rev] using hd

end PoincareConjecture.SingularTimeAssumptions
