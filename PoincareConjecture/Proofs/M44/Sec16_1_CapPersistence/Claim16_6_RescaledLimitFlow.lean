import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CoordinateFlow
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RescaledLimitCurvature













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance rescaledLimitFlowCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rescaledLimitFlowCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem exists_metric_of_standard_coefficients
    (B : E → MetricCoefficient 3) (hsmooth : ContDiff ℝ ∞ B)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < B x v v) :
    ∃ g : RiemannianMetric 3 E, g.euclideanCoefficients = B := by
  obtain ⟨g, hg⟩ := RiemannianMetric.exists_of_constant_chart_limit
    (M := E) (fun _ _ => rfl) (fun _ => B) B hsmooth.contMDiff
    (fun _ => hsymm) (fun _ _ _ => tendsto_const_nhds) (fun x => by
      obtain ⟨c, hc, hbound⟩ := exists_uniform_bilinear_lower_bound
        (isCompact_singleton (x := x)) hsmooth.continuous.continuousOn
        (fun y _ => hpos y)
      exact ⟨c, hc, Eventually.of_forall fun _ => hbound x (mem_singleton x)⟩)
  refine ⟨g, ?_⟩
  funext x
  exact ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => hg x v w




theorem ricciFlowOperator_standard_coefficients
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g) (x v w : E) :
    ricciFlowOperator 3 (metricTwoJet g.euclideanCoefficients x) v w =
      -2 * D.ricci x v w := by
  let R := (show E →ₗ[ℝ] E →ₗ[ℝ] ℝ from M13.ricciLinear D x).toContinuousBilinearMap
  have hR := bilinear_eq_sum_dual (EuclideanSpace.basisFun (Fin 3) ℝ) ((-2 : ℝ) • R)
  have hop : ricciFlowOperator 3 (metricTwoJet g.euclideanCoefficients x) =
      (-2 : ℝ) • R := by
    rw [hR]
    unfold ricciFlowOperator
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [jetRicci_metricTwoJet D]
    rfl
  rw [hop]
  rfl






theorem exists_rescaled_limit_flow_of_coefficients
    (g0 : StandardInitialMetric) {lifetime : ℝ} (hlife : 0 < lifetime)
    (B : ℝ × E → MetricCoefficient 3)
    (hspace : ∀ t ∈ Ico 0 lifetime, ContDiff ℝ ∞ (fun x => B (t, x)))
    (hsymm : ∀ t ∈ Ico 0 lifetime, ∀ x v w, B (t, x) v w = B (t, x) w v)
    (hpos : ∀ t ∈ Ico 0 lifetime, ∀ x v, v ≠ 0 → 0 < B (t, x) v v)
    (hsmooth : ContDiffOn ℝ ∞ B (Ico 0 lifetime ×ˢ univ))
    (hbirth : ∀ x, B (0, x) = g0.metric.euclideanCoefficients x)
    (hevol : ∀ t ∈ Ico 0 lifetime, ∀ x : E,
      HasDerivWithinAt (fun s => B (s, x))
        (ricciFlowOperator 3 (metricTwoJet (fun y => B (t, y)) x))
        (Ico 0 lifetime) t) :
    ∃ F : RicciFlow 3 E (Ico 0 lifetime),
      F.metric 0 = g0.metric ∧ HEq (F.connection 0) g0.connection ∧
      ∀ t ∈ Ico 0 lifetime, (F.metric t).euclideanCoefficients = fun x => B (t, x) := by
  classical
  choose g hg using fun t (ht : t ∈ Ico 0 lifetime) =>
    exists_metric_of_standard_coefficients (fun x => B (t, x))
      (hspace t ht) (hsymm t ht) (hpos t ht)
  let G (t : ℝ) : RiemannianMetric 3 E :=
    if t = 0 then g0.metric else if ht : t ∈ Ico 0 lifetime then g t ht else g0.metric
  have hG0 : G 0 = g0.metric := by simp only [G, if_pos rfl]
  have hcoeff (t : ℝ) (ht : t ∈ Ico 0 lifetime) :
      (G t).euclideanCoefficients = fun x => B (t, x) := by
    by_cases ht0 : t = 0
    · subst t
      rw [hG0]
      exact funext fun x => (hbirth x).symm
    · simpa only [G, if_neg ht0, dif_pos ht] using hg t ht
  let D0 : LeviCivitaData (G 0) := hG0.symm ▸ g0.connection
  let D (t : ℝ) : LeviCivitaData (G t) :=
    if ht0 : t = 0 then ht0.symm ▸ D0 else (G t).euclideanLeviCivitaData
  have hD0 : HEq (D 0) g0.connection := by
    simp only [D, dif_pos rfl]
    exact eqRec_heq _ _
  have hmetric_smooth : RiemannianMetric.IsSmoothFamilyOn G (Ico 0 lifetime) := by
    apply RiemannianMetric.isSmoothFamilyOn_of_constant_chart
      (fun _ _ : E => rfl) G B _ (fun t ht x v w =>
        congrArg (fun C => C x v w) (hcoeff t ht))
    have hid : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ × E) ∞
        (fun p : ℝ × E => (p.1, p.2)) := contMDiff_fst.prodMk_space contMDiff_snd
    exact hsmooth.contMDiffOn.comp hid.contMDiffOn (fun _ hp => hp)
  refine ⟨{
    metric := G
    connection := D
    interval := ordConnected_Ico
    nontrivial := (Ico_infinite hlife).nontrivial
    smooth := hmetric_smooth
    equation := ?_ }, hG0, hD0, hcoeff⟩
  intro t ht x v w
  have hd : HasDerivWithinAt (fun s => B (s, x) v w)
      (ricciFlowOperator 3 (metricTwoJet (fun y => B (t, y)) x) v w)
      (Ico 0 lifetime) t := by
    simpa using ((hevol t ht x).clm_apply
      (hasDerivWithinAt_const t (Ico 0 lifetime) (show E from v))).clm_apply
        (hasDerivWithinAt_const t (Ico 0 lifetime) (show E from w))
  rw [← hcoeff t ht, ricciFlowOperator_standard_coefficients (D t)] at hd
  apply hd.congr_of_mem _ ht
  intro s hs
  exact congrArg (fun C => C x v w) (hcoeff s hs)






theorem exists_rescaled_partial_flow_of_coefficients
    (g0 : StandardInitialMetric) {lifetime : ℝ} (hlife : 0 < lifetime)
    (B : ℝ × E → MetricCoefficient 3)
    (hspace : ∀ t ∈ Ico 0 lifetime, ContDiff ℝ ∞ (fun x => B (t, x)))
    (hsymm : ∀ t ∈ Ico 0 lifetime, ∀ x v w, B (t, x) v w = B (t, x) w v)
    (hpos : ∀ t ∈ Ico 0 lifetime, ∀ x v, v ≠ 0 → 0 < B (t, x) v v)
    (hsmooth : ContDiffOn ℝ ∞ B (Ico 0 lifetime ×ˢ univ))
    (hbirth : ∀ x, B (0, x) = g0.metric.euclideanCoefficients x)
    (hevol : ∀ t ∈ Ico 0 lifetime, ∀ x : E,
      HasDerivWithinAt (fun s => B (s, x))
        (ricciFlowOperator 3 (metricTwoJet (fun y => B (t, y)) x))
        (Ico 0 lifetime) t)
    (hbound : ∀ T0 : ℝ, 0 ≤ T0 → T0 < lifetime →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∀ t ∈ Icc 0 T0,
        ∀ x ∈ g0.metric.ball 0 R,
          standardJetCurvatureNorm (metricTwoJet (fun y => B (t, y)) x) ≤ K) :
    ∃ S : PartialStandardCapFlow g0, S.lifetime = lifetime ∧
      ∀ t ∈ Ico 0 lifetime,
        (S.flow.metric t).euclideanCoefficients = fun x => B (t, x) := by
  obtain ⟨F, hF0, hD0, hcoeff⟩ := exists_rescaled_limit_flow_of_coefficients g0 hlife B
    hspace hsymm hpos hsmooth hbirth hevol
  refine ⟨{
    lifetime := lifetime
    lifetime_pos := hlife
    flow := F
    initial_metric := hF0
    initial_connection := hD0
    curvature_locally_bounded := ?_ }, rfl, hcoeff⟩
  apply curvature_locally_bounded_of_standard_exhaustion g0 F
  intro T0 hT0 hTlife
  obtain ⟨K, hK, hR⟩ := hbound T0 hT0 hTlife
  refine ⟨K, hK, ?_⟩
  intro R hRpos t ht x hx
  rw [← standardJetCurvatureNorm_metricTwoJet (F.connection t) x,
    hcoeff t ⟨ht.1, ht.2.trans_lt hTlife⟩]
  exact hR R hRpos t ht x hx

end PoincareConjecture.M44
