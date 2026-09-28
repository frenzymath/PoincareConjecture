import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialTipTolerance
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialTipReadout
import PoincareConjecture.Proofs.M47.BlowupControlsCapJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open SpacetimeBounds Proofs.M46

noncomputable local instance tipComparisonCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tipComparisonCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance tipComparisonTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance tipComparisonTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace



theorem exists_source_cap_tip_ricci_tolerance {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {theta : ℝ} (htheta : theta < 1) :
    ∃ mu : ℝ, 0 < mu ∧ ∀ A : ℝ, 0 < A →
      ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 / 2 ∧
        ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
          (S : MaximalStandardCapFlow F.standard_initial), HEq S P.standard_cap.flow →
          ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
            (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
            (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
            (initial : SurgeryCapInitialComparison F t hT i A)
            (eta : ℝ), 0 < eta → eta ≤ eta0 →
          SurgeryCapFamilyComparison F S A eta e initial.chart →
          ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
          ∀ w : TangentSpace (𝓡 3) (e.forward s hs ((F.event t hT).caps i).tip),
            (mu / (F.parameters.h t) ^ 2) *
                (F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2))).inner
                  (e.forward s hs ((F.event t hT).caps i).tip) w w ≤
              (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).ricci
                (e.forward s hs ((F.event t hT).caps i).tip) w w := by
  obtain ⟨mu, hmu, delta, hdelta, hmodel⟩ :=
    exists_source_standard_tip_ricci_tolerance P htheta
  refine ⟨mu, hmu, ?_⟩
  intro A hA
  obtain ⟨C, hC, hjets⟩ := exists_actualCap_twoJet_bound P.standard_cap htheta hA
  let eta0 := min (1 / 2 : ℝ) (delta / C)
  have heta0 : 0 < eta0 := lt_min (by norm_num) (div_pos hdelta hC)
  refine ⟨eta0, heta0, min_le_left _ _, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetaBound comparison s hs hst
  have hetaHalf : eta ≤ 1 / 2 := hetaBound.trans (min_le_left _ _)
  have herror : C * eta ≤ delta := by
    have h := (le_div_iff₀ hC).mp (hetaBound.trans (min_le_right _ _))
    nlinarith only [h]
  have hzero : (0 : StandardCapSpace) ∈ F.standard_initial.metric.ball 0 A := by
    change F.standard_initial.metric.edist 0 0 < ENNReal.ofReal A
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hA
  have hnear := (hjets F hinitial S hS t hT hn i J U e initial eta
    heta hetaHalf comparison s hs hst 0 hzero).trans herror
  have htime : s ∈ Icc (0 : ℝ) theta :=
    ⟨(comparison.choose_spec.2.2.1 s hs).1, hst⟩
  have hlower : ∀ v : StandardCapSpace,
      mu * capComparisonCoefficients e initial.chart s hs 0 v v ≤
        M44.jetRicciBilinear
          (metricTwoJet (capComparisonCoefficients e initial.chart s hs) 0) v v := by
    cases hinitial
    cases hS
    exact (hmodel s htime _ hnear).2
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hread := source_capComparison_ricci_lower e initial comparison hh s hs hzero hlower
  have hpoint : e.forward s hs (initial.chart 0) =
      e.forward s hs ((F.event t hT).caps i).tip :=
    congrArg (e.forward s hs) initial.tip_eq
  exact hpoint ▸ hread

end PoincareConjecture.M47
