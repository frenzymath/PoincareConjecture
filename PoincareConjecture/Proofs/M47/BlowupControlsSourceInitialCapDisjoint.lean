import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialCapObstruction
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialTipComparison
import PoincareConjecture.Proofs.M47.BlowupControlsCapScalarUpper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open M45

theorem exists_source_initial_cap_disjoint_tolerance {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {R : ℝ} (hR : 0 ≤ R) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 / 1200 ∧
      ∀ A : ℝ, 2 * (g0.cylindrical_end.radius + 5) < A →
      ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 / 1000 ∧
        ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
          (S : MaximalStandardCapFlow F.standard_initial), HEq S P.standard_cap.flow →
        ∀ {C : GeneralizedSliceCarrier.{u}} {g : RiemannianMetric 3 C.carrier}
          (N : EpsilonNeck g) {origin scale : ℝ} {I : Set ℝ}
          (old : SurgeryFlowCylinder F C origin scale I N.carrier),
          N.epsilon ≤ delta0 →
        ∀ (u : ℝ) (hu : u ∈ I), u ∈ Ioo (-1 : ℝ) 0 →
          RoundCylinderClose N.epsilon u (surgeryCylinderPullback old N.coordinate_map u) →
        ∀ (t : ℝ) (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier]
          (i : Fin (F.event t hT).cap_count) (J : Set ℝ)
          (cap : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
            ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
          (initial : SurgeryCapInitialComparison F t hT i A)
          (eta : ℝ), 0 < eta → eta ≤ eta0 →
          SurgeryCapFamilyComparison F S A eta cap initial.chart →
        ∀ hzero : (0 : ℝ) ∈ J,
          (∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
            HEq (cap.forward 0 hzero y) y) →
        ∀ (sigma : ℝ) (hsigma : sigma ∈ J), sigma ≤ 1 / 2 →
        ∀ (y : (F.slice t).carrier), y ∈ ((F.event t hT).caps i).carrier →
        ∀ (x : C.carrier), x ∈ N.region (-R) R →
          (⟨t + sigma / ((F.parameters.h t)⁻¹ ^ 2), cap.forward sigma hsigma y⟩ :
            Σ r, (F.slice r).carrier) = ⟨origin + u / scale, old.forward u hu x⟩ → False := by
  obtain ⟨mu, hmu, tipTolerance⟩ :=
    exists_source_cap_tip_ricci_tolerance P (theta := (1 / 2 : ℝ)) (by norm_num)
  obtain ⟨K, hK, scalarTolerance⟩ :=
    exists_actualCap_scalar_upper.{u} P.standard_cap (theta := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)
  let D := 4 * (g0.cylindrical_end.radius + 5)
  let delta0 := min (1 / 1200 : ℝ)
    (min (1 / (R + 2 + 4 * D * Real.sqrt K)) (mu / (1024 * (K + 1))))
  have hD : 0 < D := by
    have hA0 := g0.cylindrical_end.radius_pos
    dsimp only [D]
    positivity
  have hdelta : 0 < delta0 := by
    dsimp only [delta0]
    positivity
  refine ⟨delta0, hdelta, min_le_left _ _, ?_⟩
  intro A hA
  have hApos : 0 < A := by linarith [g0.cylindrical_end.radius_pos]
  obtain ⟨etaTip, hEtaTip, _hTipHalf, hTip⟩ := tipTolerance A hApos
  obtain ⟨etaScalar, hEtaScalar, _hScalarHalf, hScalar⟩ := scalarTolerance A hApos
  let eta0 := min (1 / 1000 : ℝ) (min etaTip etaScalar)
  have hEta0 : 0 < eta0 := lt_min (by norm_num) (lt_min hEtaTip hEtaScalar)
  refine ⟨eta0, hEta0, min_le_left _ _, ?_⟩
  intro F hinitial S hS C g N origin scale I old hsmall u hu hutime hclose
    t hT hn i J cap initial eta heta heta0 comparison hzero hbase sigma hsigma
    hSigmaHalf y hy x hx hcontact
  have hetaSmall : eta ≤ 1 / 1000 := heta0.trans (min_le_left _ _)
  have hetaTip : eta ≤ etaTip :=
    heta0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hetaScalar : eta ≤ etaScalar :=
    heta0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall' : N.epsilon ≤ 1 / 1200 := hsmall.trans (min_le_left _ _)
  have hcapture : N.epsilon ≤ 1 / (R + 2 + 4 * D * Real.sqrt K) :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hricci : N.epsilon ≤ mu / (1024 * (K + 1)) :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hAactual : 2 * (F.standard_initial.cylindrical_end.radius + 5) < A :=
    hinitial.symm ▸ hA
  have hySource : y ∈ (F.metric t).ball ((F.event t hT).caps i).tip
      (A * F.parameters.h t) :=
    inserted_cap_subset_persistence_ball hT i
      (by linarith [F.standard_initial.cylindrical_end.radius_pos]) hy
  have hupper := hScalar F hinitial S hS t hT hn i J _ cap initial
    eta heta hetaScalar comparison hh sigma hsigma hSigmaHalf y hySource
  have htip := hTip F hinitial S hS t hT hn i J _ cap initial
    eta heta hetaTip comparison sigma hsigma hSigmaHalf
  cases hinitial
  cases hS
  exact source_initial_compared_cap_no_contact P.standard_cap N old hsmall'
    u hu hutime hclose hR hmu hK hcapture hricci hAactual cap initial comparison
    hzero hbase hh heta hetaSmall sigma hsigma hy hx hcontact hupper htip

end PoincareConjecture.M47
