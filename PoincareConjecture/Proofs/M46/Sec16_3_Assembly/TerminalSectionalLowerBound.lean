import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveSectionalContinuation
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalMetricJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_PullbackPlane









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open SpacetimeBounds M04 M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance terminalSectionalCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance terminalSectionalCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance terminalSectionalJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance terminalSectionalJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

set_option maxHeartbeats 1800000 in



theorem terminal_sectional_lower_of_preterminal
    (event : SurgeryEventData g0 K P slice metric T)
    {q : (slice event.tMinus).carrier} (hq : q ∈ event.regular_limit)
    {k : ℝ} (hbound : ∀ᶠ t in 𝓝[<] T,
      ∀ u v : TangentSpace (𝓡 3) q,
        k * metricGram (event.pre_flow.metric t) q u v ≤
          (event.pre_flow.connection t).curvatureTensor q u v u v) :
    ∀ u v : TangentSpace (𝓡 3) (event.limit_identify.map q),
      k * metricGram event.limit_metric (event.limit_identify.map q) u v ≤
        event.limit_connection.curvatureTensor (event.limit_identify.map q) u v u v := by
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
  let f := event.limit_identify.map ∘ c.symm
  let JT := metricTwoJet (event.limit_metric.pullbackCoefficients f) (c q)
  have hinv : JT.1.IsInvertible :=
    event.limit_metric.isInvertible_pullbackCoefficients (hj (c q) hx).injective
  have hcoordinate (u v : E) :
      k * collarJetGram u v JT ≤ jetCurvature JT u v u v := by
    have hleft : Tendsto (fun t => k * collarJetGram u v
        (metricTwoJet ((event.pre_flow.metric t).pullbackCoefficients c.symm) (c q)))
        (𝓝[<] T) (𝓝 (k * collarJetGram u v JT)) :=
      ((continuous_const.mul (continuous_collarJetGram u v)).continuousAt.tendsto).comp hconv
    have hright : Tendsto (fun t => jetCurvature
        (metricTwoJet ((event.pre_flow.metric t).pullbackCoefficients c.symm) (c q)) u v u v)
        (𝓝[<] T) (𝓝 (jetCurvature JT u v u v)) :=
      (contDiffAt_jetCurvature hinv u v u v).continuousAt.tendsto.comp hconv
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [hbound] with t ht
    rw [jetCurvature_pullbackCoefficients (event.pre_flow.metric t)
      (event.pre_flow.connection t) hU hc hi hx]
    change k * metricGram (event.pre_flow.metric t) (c.symm (c q))
        (mfderiv (𝓡 3) (𝓡 3) c.symm (c q) u)
        (mfderiv (𝓡 3) (𝓡 3) c.symm (c q) v) ≤ _
    have hforall : ∀ z : (slice event.tMinus).carrier, z = q →
        ∀ a b : TangentSpace (𝓡 3) z,
          k * metricGram (event.pre_flow.metric t) z a b ≤
            (event.pre_flow.connection t).curvatureTensor z a b a b := by
      intro z hz
      subst z
      exact ht
    exact hforall _ hcx _ _
  have hall : ∀ u v : TangentSpace (𝓡 3) (f (c q)),
      k * metricGram event.limit_metric (f (c q)) u v ≤
        event.limit_connection.curvatureTensor (f (c q)) u v u v := by
    intro u v
    obtain ⟨a, ha⟩ := (hj (c q) hx).surjective u
    obtain ⟨b, hb⟩ := (hj (c q) hx).surjective v
    have h := hcoordinate a b
    rw [jetCurvature_pullbackCoefficients event.limit_metric event.limit_connection
      hU hf hj hx] at h
    change k * metricGram event.limit_metric (f (c q))
      (mfderiv (𝓡 3) (𝓡 3) f (c q) a) (mfderiv (𝓡 3) (𝓡 3) f (c q) b) ≤ _ at h
    have ha' : mfderiv (𝓡 3) (𝓡 3) f (c q) a = u := ha
    have hb' : mfderiv (𝓡 3) (𝓡 3) f (c q) b = v := hb
    rw [ha', hb'] at h
    simpa only [ha, hb] using h
  have hfq : f (c q) = event.limit_identify.map q := congrArg event.limit_identify.map hcx
  exact hfq ▸ hall



theorem terminal_sectional_positive_of_preterminal
    (event : SurgeryEventData g0 K P slice metric T)
    {q : (slice event.tMinus).carrier} (hq : q ∈ event.regular_limit)
    {k : ℝ} (hk : 0 < k) (hbound : ∀ᶠ t in 𝓝[<] T,
      ∀ u v : TangentSpace (𝓡 3) q,
        k * metricGram (event.pre_flow.metric t) q u v ≤
          (event.pre_flow.connection t).curvatureTensor q u v u v)
    (u v : TangentSpace (𝓡 3) (event.limit_identify.map q))
    (hpair : LeviCivitaData.IsOrthonormalPair event.limit_metric
      (event.limit_identify.map q) u v) :
    0 < event.limit_connection.sectionalCurvature (event.limit_identify.map q) u v := by
  have h := terminal_sectional_lower_of_preterminal event hq hbound u v
  simp only [metricGram, hpair.1, hpair.2.1, hpair.2.2,
    zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one] at h
  simpa only [LeviCivitaData.sectionalCurvature, hpair.1, hpair.2.1, hpair.2.2, one_mul,
    zero_pow (by decide : 2 ≠ 0), sub_zero, div_one] using hk.trans_le h

end PoincareConjecture.Proofs.M46
