import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalMetricJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_PhysicalCollar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance terminalScalarCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance terminalScalarCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem jetScalarCurvature_pullbackCoefficients
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    {x : E} (hx : x ∈ U) :
    jetScalarCurvature (metricTwoJet (g.pullbackCoefficients f) x) =
      D.scalarCurvature (f x) := by
  obtain ⟨gE, DE, V, hV, hxV, hVU, hmetric⟩ :=
    RiemannianMetric.exists_local_realization hU hx (g.pullbackCoefficients f)
      (fun y hy => (g.contDiffAt_pullbackCoefficients
        (hf.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt)
      (fun y _ a b => g.symm (f y) _ _)
      (fun y hy a ha => by
        apply g.pos (f y)
        intro hz
        apply ha
        apply (hinv y hy).injective
        rw [map_zero]
        exact hz)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients f :=
    eventually_of_mem (hV.mem_nhds hxV) hmetric
  have htwo : metricTwoJet gE.euclideanCoefficients x =
      metricTwoJet (g.pullbackCoefficients f) x := by
    simp only [metricTwoJet, heq.eq_of_nhds, heq.fderiv_eq,
      (heq.fderiv (𝕜 := ℝ)).fderiv_eq]
  rw [← htwo, jetScalarCurvature_metricTwoJet DE]
  exact (scalar_ricciNormSq_eq_of_metric_pullback DE D
    (hf.contMDiffAt (hU.mem_nhds hx))
    (eventually_of_mem (hV.mem_nhds hxV) (fun y hy => hinv y (hVU hy)))
    (eventually_of_mem (hV.mem_nhds hxV)
      (fun y hy a b => congrArg (fun B => B a b) (hmetric y hy)))).1.symm

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

theorem tendsto_preterminal_scalar
    (event : SurgeryEventData g0 K P slice metric T)
    {q : (slice event.tMinus).carrier} (hq : q ∈ event.regular_limit) :
    Tendsto (fun t => (event.pre_flow.connection t).scalarCurvature q) (𝓝[<] T)
      (𝓝 (event.limit_connection.scalarCurvature (event.limit_identify.map q))) := by
  let c := extChartAt (𝓡 3) q
  let U := c.target ∩ c.symm ⁻¹' event.regular_limit
  have hU : IsOpen U :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) event.regular_limit_open
  have hchart : U ⊆ c.target := inter_subset_left
  have hregular : c.symm '' U ⊆ event.regular_limit := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm U :=
    (contMDiffOn_extChartAt_symm q).mono hchart
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (event.limit_identify.map ∘ c.symm) U :=
    event.limit_identify.map_smooth.comp hc (fun x hx => hx.2)
  have hi (x : E) (hx : x ∈ U) :
      (mfderiv (𝓡 3) (𝓡 3) c.symm x).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm (hchart hx)
  have hj (x : E) (hx : x ∈ U) :
      (mfderiv (𝓡 3) (𝓡 3) (event.limit_identify.map ∘ c.symm) x).IsInvertible := by
    have hreg : c.symm x ∈ interior event.regular_limit :=
      event.regular_limit_open.interior_eq.symm ▸ hx.2
    have hl := (regionEquivalenceInteriorChart event.limit_identify).isLocalDiffeomorphAt
      (𝓡 3) (𝓡 3) ∞ hreg
    have hli : (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.map (c.symm x)).IsInvertible :=
      ⟨hl.mfderivToContinuousLinearEquiv (by simp), rfl⟩
    have hd := event.limit_identify.map_smooth.contMDiffAt
      (event.regular_limit_open.mem_nhds hx.2)
    rw [mfderiv_comp x (hd.mdifferentiableAt (by simp))
      ((hc.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact hli.comp (hi x hx)
  have hcx : c.symm (c q) = q := c.left_inv (mem_extChartAt_source q)
  have hx : c q ∈ U := ⟨c.map_source (mem_extChartAt_source q), by
    change c.symm (c q) ∈ event.regular_limit
    rwa [hcx]⟩
  have hconv := tendsto_twoJet_of_surgeryMetricLimitOn event.metric_converges q hq
    hU hchart hregular hf hx
  have hscalar := (contDiffAt_jetScalarCurvature
    (event.limit_metric.isInvertible_pullbackCoefficients (hj (c q) hx).injective)).continuousAt
      |>.tendsto.comp hconv
  have hread (t : ℝ) := jetScalarCurvature_pullbackCoefficients
    (event.pre_flow.metric t) (event.pre_flow.connection t) hU hc hi hx
  have hreadT := jetScalarCurvature_pullbackCoefficients
    event.limit_metric event.limit_connection hU hf hj hx
  change Tendsto (fun t => jetScalarCurvature
    (metricTwoJet ((event.pre_flow.metric t).pullbackCoefficients c.symm) (c q)))
    (𝓝[<] T) (𝓝 (jetScalarCurvature (metricTwoJet
      (event.limit_metric.pullbackCoefficients (event.limit_identify.map ∘ c.symm))
      (c q)))) at hscalar
  simpa only [hread, hreadT, Function.comp_apply, hcx] using hscalar

theorem terminal_scalar_le_of_preterminal
    (event : SurgeryEventData g0 K P slice metric T)
    {q : (slice event.tMinus).carrier} (hq : q ∈ event.regular_limit)
    {L : ℝ} (hbound : ∀ᶠ t in 𝓝[<] T,
      (event.pre_flow.connection t).scalarCurvature q ≤ L) :
    event.limit_connection.scalarCurvature (event.limit_identify.map q) ≤ L :=
  le_of_tendsto (tendsto_preterminal_scalar event hq) hbound

end PoincareConjecture.M44
