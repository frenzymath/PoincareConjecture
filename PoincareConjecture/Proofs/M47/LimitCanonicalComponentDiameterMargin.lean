import PoincareConjecture.Proofs.M47.LimitCanonicalComponentScalarMargin
import PoincareConjecture.Proofs.M47.LimitCanonicalComponentExtrema
import PoincareConjecture.Proofs.M47.LimitCanonicalComponentDiameterComparison
import PoincareConjecture.Proofs.M47.LimitCanonicalIntrinsicDiameter










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture.M47



theorem limitCanonical_strict_diameter_parameters {C L0 U0 d : ℝ}
    (hlower : C⁻¹ * L0 < d) (hupper : d < C * U0) :
    ∃ L eta : ℝ, 1 < L ∧ 0 < eta ∧
      L * (C⁻¹ * (L0 + eta)) < d ∧ L * d < C * (U0 - eta) := by
  have hcont : Continuous (fun t : ℝ => (1 + t) * (C⁻¹ * (L0 + t))) := by fun_prop
  have hcont' : Continuous (fun t : ℝ => (1 + t) * d - C * (U0 - t)) := by fun_prop
  have hlow : ∀ᶠ t : ℝ in 𝓝 0, (1 + t) * (C⁻¹ * (L0 + t)) < d :=
    (hcont.tendsto 0).eventually (gt_mem_nhds (by simpa using hlower))
  have hupp : ∀ᶠ t : ℝ in 𝓝 0, (1 + t) * d - C * (U0 - t) < 0 :=
    (hcont'.tendsto 0).eventually (gt_mem_nhds (by simpa using sub_neg.mpr hupper))
  have hpositive : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 < t ∧ (1 + t) * (C⁻¹ * (L0 + t)) < d ∧
        (1 + t) * d - C * (U0 - t) < 0 :=
    hpositive.and ((hlow.and hupp).filter_mono nhdsWithin_le_nhds)
  obtain ⟨t, ht, hlt, hut⟩ := hsmall.exists
  exact ⟨1 + t, t, by linarith, ht, hlt, by linarith⟩

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}}
  (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤))

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold



theorem limitCanonical_component_eventually_strict_diameters
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    {kappa C : ℝ} (hkappa : 0 < kappa)
    (hnc : BlowupLimitNoncollapsed G.limit kappa) :
    letI : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
    let K : AncientKappaSolution 3 G.limit.sliceCarrier.carrier :=
      (limitAncientIdentification P.m04 G.limit kappa hkappa hnc).certificate.solution
    ∀ _N : M27CanonicalComponent K 0 C,
      ∀ᶠ k in atTop,
        let f := limitCanonicalPhysicalTerminalChart G F R k
        let g := M13.scaleSmoothMetric
          ((F (G.subsequence k)).metric
            ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
          (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
        let D := M13.scaleLeviCivitaData
          ((F (G.subsequence k)).connection
            ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
          (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
        let radii := range (fun y : f.target => D.scalarCurvature y.val ^ (-1 / 2 : ℝ))
        G.exhaustion.space k = univ ∧
          f.target = connectedComponent (f G.limit.base) ∧
          ENNReal.ofReal (C⁻¹ * sSup radii) < intrinsicDiameter g f.target ∧
          intrinsicDiameter g f.target < ENNReal.ofReal (C * sInf radii) := by
  let : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  dsimp only
  intro N
  let : CompactSpace G.limit.carrier.carrier := isCompact_univ_iff.mp N.compact
  obtain ⟨a, ha, hsec, _hsectional⟩ :=
    limitCanonical_component_eventually_sectional_fields G P F R hkappa hnc N
  let d := metricDiameter (G.limit.flow.metric 0) univ
  let old := range (fun x : G.limit.sliceCarrier.carrier =>
    (G.limit.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ))
  have hC := N.constant_pos
  have hnonnegative : 0 ≤ sSup old := by
    apply Real.sSup_nonneg
    rintro z ⟨x, rfl⟩
    apply Real.rpow_nonneg
    exact ((mul_pos (by norm_num : (0 : ℝ) < 6) ha).trans
      (six_mul_lt_scalar_of_sectional_lower (G.limit.flow.connection 0) x a (hsec x))).le
  have hdpos : 0 < d :=
    (mul_nonneg (inv_pos.mpr hC).le hnonnegative).trans_lt N.diameter_lower
  have hdiam0 := limitCanonical_intrinsicDiameter_univ (G.limit.flow.metric 0)
  obtain ⟨L, eta, hL, heta, hlower, hupper⟩ :=
    limitCanonical_strict_diameter_parameters N.diameter_lower N.diameter_upper
  have hLpos : 0 < L := zero_lt_one.trans hL
  filter_upwards [limitCanonical_component_eventually_diameter_comparison G F R N.compact hL,
    limitCanonical_component_eventually_radius_extrema G P F R N.compact ha hsec heta]
    with k hd he
  let f := limitCanonicalPhysicalTerminalChart G F R k
  let D := M13.scaleLeviCivitaData
    ((F (G.subsequence k)).connection
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
    (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  let radii := range (fun y : f.target => D.scalarCurvature y.val ^ (-1 / 2 : ℝ))
  have hsup : sSup radii ≤ sSup old + eta := by
    have herror : |sSup radii - sSup old| ≤ eta := he.2.2.2.2.1
    linarith [(abs_le.mp herror).2]
  have hinf : sInf old - eta ≤ sInf radii := by
    have herror : |sInf radii - sInf old| ≤ eta := he.2.2.2.2.2
    linarith [(abs_le.mp herror).1]
  have hlow : ENNReal.ofReal L * ENNReal.ofReal (C⁻¹ * sSup radii) <
      ENNReal.ofReal d := by
    rw [← ENNReal.ofReal_mul hLpos.le]
    apply (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsup (inv_pos.mpr hC).le) hLpos.le)).trans_lt
    exact (ENNReal.ofReal_lt_ofReal_iff hdpos).mpr hlower
  have huppos : 0 < C * (sInf old - eta) :=
    (mul_nonneg hLpos.le hdpos.le).trans_lt hupper
  refine ⟨hd.1, hd.2.1, ?_, ?_⟩
  · by_contra hnot
    have hreverse := hd.2.2.2
    rw [hdiam0.2.1] at hreverse
    have hbound := le_of_not_gt hnot
    exact (not_lt_of_ge (hreverse.trans (by gcongr))) hlow
  · calc
      _ ≤ ENNReal.ofReal L * intrinsicDiameter (G.limit.flow.metric 0) univ := hd.2.2.1
      _ = ENNReal.ofReal (L * d) := by
        rw [hdiam0.2.1, ← ENNReal.ofReal_mul hLpos.le]
      _ < ENNReal.ofReal (C * (sInf old - eta)) :=
        (ENNReal.ofReal_lt_ofReal_iff huppos).mpr hupper
      _ ≤ ENNReal.ofReal (C * sInf radii) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hinf hC.le)

end PoincareConjecture.M47
