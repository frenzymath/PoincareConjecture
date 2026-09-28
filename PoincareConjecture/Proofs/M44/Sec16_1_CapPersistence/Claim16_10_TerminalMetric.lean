import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalMetricJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance terminalMetricCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance terminalMetricCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

theorem tendsto_preterminal_twoJet
    (event : SurgeryEventData g0 K P slice metric T)
    {q : (slice event.tMinus).carrier} (hq : q ∈ event.regular_limit) :
    Tendsto (fun t => metricTwoJet
      ((event.pre_flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm)
        (extChartAt (𝓡 3) q q)) (𝓝[<] T)
      (𝓝 (metricTwoJet (event.limit_metric.pullbackCoefficients
        (event.limit_identify.map ∘ (extChartAt (𝓡 3) q).symm)) (extChartAt (𝓡 3) q q))) := by
  let c := extChartAt (𝓡 3) q
  let U := c.target ∩ c.symm ⁻¹' event.regular_limit
  have hU : IsOpen U :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) event.regular_limit_open
  have hchart : U ⊆ c.target := inter_subset_left
  have hregular : c.symm '' U ⊆ event.regular_limit := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).mono hchart
  have hf := event.limit_identify.map_smooth.comp hc (fun x hx => hx.2)
  have hx : c q ∈ U := ⟨c.map_source (mem_extChartAt_source q), by
    change c.symm (c q) ∈ event.regular_limit
    rwa [c.left_inv (mem_extChartAt_source q)]⟩
  exact tendsto_twoJet_of_surgeryMetricLimitOn event.metric_converges q hq
    hU hchart hregular hf hx

theorem tendsto_preterminal_metric_inner
    (event : SurgeryEventData g0 K P slice metric T)
    {q : (slice event.tMinus).carrier} (hq : q ∈ event.regular_limit)
    (v w : TangentSpace (𝓡 3) q) :
    Tendsto (fun t => (event.pre_flow.metric t).inner q v w) (𝓝[<] T)
      (𝓝 (event.limit_metric.inner (event.limit_identify.map q)
        (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.map q v)
        (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.map q w))) := by
  let c := extChartAt (𝓡 3) q
  let p := c q
  have hp : p ∈ c.target := c.map_source (mem_extChartAt_source q)
  have hcp : c.symm p = q := c.left_inv (mem_extChartAt_source q)
  have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm p).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hp
  obtain ⟨a, ha⟩ := hi.surjective v
  obtain ⟨b, hb⟩ := hi.surjective w
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds hp)
  have hl := event.limit_identify.map_smooth.contMDiffAt
    (event.regular_limit_open.mem_nhds (show c.symm p ∈ event.regular_limit by rwa [hcp]))
  have hderiv := mfderiv_comp p (hl.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))
  have hread (t : ℝ) : (event.pre_flow.metric t).pullbackCoefficients c.symm p a b =
      (event.pre_flow.metric t).inner q v w := by
    change (event.pre_flow.metric t).inner (c.symm p)
      (mfderiv (𝓡 3) (𝓡 3) c.symm p a) (mfderiv (𝓡 3) (𝓡 3) c.symm p b) = _
    rw [ha, hb, hcp]
  have hreadT : event.limit_metric.pullbackCoefficients
      (event.limit_identify.map ∘ c.symm) p a b =
      event.limit_metric.inner (event.limit_identify.map q)
        (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.map q v)
        (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.map q w) := by
    change event.limit_metric.inner (event.limit_identify.map (c.symm p))
      (mfderiv (𝓡 3) (𝓡 3) (event.limit_identify.map ∘ c.symm) p a)
      (mfderiv (𝓡 3) (𝓡 3) (event.limit_identify.map ∘ c.symm) p b) = _
    rw [hderiv]
    change event.limit_metric.inner (event.limit_identify.map (c.symm p))
      (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.map (c.symm p)
        (mfderiv (𝓡 3) (𝓡 3) c.symm p a))
      (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.map (c.symm p)
        (mfderiv (𝓡 3) (𝓡 3) c.symm p b)) = _
    rw [ha, hb, hcp]
  have hconv : Tendsto (fun t => (event.pre_flow.metric t).pullbackCoefficients c.symm p)
      (𝓝[<] T) (𝓝 (event.limit_metric.pullbackCoefficients
        (event.limit_identify.map ∘ c.symm) p)) :=
    continuous_fst.continuousAt.tendsto.comp (tendsto_preterminal_twoJet event hq)
  have heval := (ContinuousLinearMap.apply ℝ ℝ b).continuous.continuousAt.tendsto.comp
    ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) a).continuous.continuousAt.tendsto.comp hconv)
  change Tendsto (fun t => (event.pre_flow.metric t).pullbackCoefficients c.symm p a b)
    (𝓝[<] T) (𝓝 (event.limit_metric.pullbackCoefficients
      (event.limit_identify.map ∘ c.symm) p a b)) at heval
  simpa only [hread, hreadT] using heval

theorem tendsto_preterminal_pullback_inner
    (event : SurgeryEventData g0 K P slice metric T)
    {f : E → (slice event.tMinus).carrier} {x : E}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x) (hx : f x ∈ event.regular_limit)
    (v w : E) :
    Tendsto (fun t => (event.pre_flow.metric t).pullbackCoefficients f x v w) (𝓝[<] T)
      (𝓝 (event.limit_metric.pullbackCoefficients (event.limit_identify.map ∘ f) x v w)) := by
  have hl := event.limit_identify.map_smooth.contMDiffAt (event.regular_limit_open.mem_nhds hx)
  have hd := mfderiv_comp x (hl.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
  have h := tendsto_preterminal_metric_inner event hx
    (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)
  change Tendsto (fun t => (event.pre_flow.metric t).inner (f x)
    (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)) (𝓝[<] T)
      (𝓝 (event.limit_metric.inner (event.limit_identify.map (f x))
        (mfderiv (𝓡 3) (𝓡 3) (event.limit_identify.map ∘ f) x v)
        (mfderiv (𝓡 3) (𝓡 3) (event.limit_identify.map ∘ f) x w)))
  rw [hd]
  exact h

theorem terminal_pullback_quadratic_le
    (event : SurgeryEventData g0 K P slice metric T)
    {f : E → (slice event.tMinus).carrier} {x : E}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x) (hx : f x ∈ event.regular_limit)
    (v : E) {L : ℝ} (hbound : ∀ᶠ t in 𝓝[<] T,
      (event.pre_flow.metric t).pullbackCoefficients f x v v ≤ L) :
    event.limit_metric.pullbackCoefficients (event.limit_identify.map ∘ f) x v v ≤ L :=
  le_of_tendsto (tendsto_preterminal_pullback_inner event hf hx v v) hbound

end PoincareConjecture.M44
