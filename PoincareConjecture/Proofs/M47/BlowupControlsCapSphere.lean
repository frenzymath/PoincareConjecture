import PoincareConjecture.Proofs.M47.BlowupControlsCapCoefficients
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalMovingModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open SpacetimeBounds Proofs.M46

noncomputable local instance capSphereCoefficientNorm : NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capSphereCoefficientSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance capSphereTwoJetNorm : NormedAddCommGroup (MetricTwoJet 3) :=
  Prod.normedAddCommGroup

noncomputable local instance capSphereTwoJetSpace : NormedSpace ℝ (MetricTwoJet 3) :=
  Prod.normedSpace

theorem exists_cap_sphere_buffer {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1) (A0 : ℝ) :
    ∃ A : ℝ, 0 < A ∧ A0 < A ∧ ∃ length : ℝ, ∃ center : StandardCapSpace,
      ∃ N : StandardCylinderPatch length center, ∃ delta : ℝ, 0 < delta ∧
        (∀ z : UnitTwoSphere, M44.StandardCylinderPatch.sphereMap N z ∈ g0.metric.ball 0 A) ∧
        ∀ s ∈ Icc 0 theta, ∀ z : UnitTwoSphere, ∀ J : MetricTwoJet 3,
          ‖J - metricTwoJet (standard.flow.metric s).euclideanCoefficients
            (M44.StandardCylinderPatch.sphereMap N z)‖ ≤ delta →
          (z, J) ∈ M44.sphereSectionalJetRegion
            (M44.StandardCylinderPatch.sphereMap N) (1 / 4) := by
  obtain ⟨length, center, N, delta, hdelta, hmargin⟩ :=
    M44.exists_standard_sphere_margin standard htheta0 htheta
  obtain ⟨A, hA, hA0, hball⟩ := M44.StandardCylinderPatch.exists_sphere_ball N g0 A0
  exact ⟨A, hA, hA0, length, center, N, delta, hdelta, hball, hmargin⟩

theorem exists_actualCap_sphere_twoJet_tail {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A : ℝ}
    (htheta : theta < 1) (hA : 0 < A)
    {length : ℝ} {center : StandardCapSpace} (N : StandardCylinderPatch length center)
    (hball : ∀ z : UnitTwoSphere, M44.StandardCylinderPatch.sphereMap N z ∈ g0.metric.ball 0 A)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 / 2 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial),
      HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (c : ℝ), 0 < c → c ≤ theta →
      ∀ (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) (Ico 0 c) U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      SurgeryCapFamilyComparison F S A eta e initial.chart →
      ∀ G : M44.CylinderRicciFlow e (capInitialPartialDiffeomorph initial),
      ∀ p : (⟨(capInitialPartialDiffeomorph initial).target,
        (capInitialPartialDiffeomorph initial).open_target⟩ : Opens (F.slice t).carrier),
      ∃ s0 : ℝ, s0 < c ∧ ∀ s ∈ Ico 0 c, s0 ≤ s → ∀ z : UnitTwoSphere,
        ‖metricTwoJet ((G.flow.metric s).pullbackCoefficients
            (M44.targetChart (capInitialPartialDiffeomorph initial) p))
            (M44.StandardCylinderPatch.sphereMap N z) -
          metricTwoJet (S.metric c).euclideanCoefficients
            (M44.StandardCylinderPatch.sphereMap N z)‖ ≤ delta := by
  obtain ⟨C, hC, htwo⟩ := exists_actualCap_twoJet_bound.{u} standard htheta hA
  let eta0 : ℝ := min (1 / 2) (delta / (2 * C))
  have heta0 : 0 < eta0 := lt_min (by norm_num) (div_pos hdelta (by positivity))
  refine ⟨eta0, heta0, min_le_left _ _, ?_⟩
  intro F hinitial S hS t hT hn i c hc hctheta U e initial eta heta hetaSmall comparison G p
  have hetaHalf : eta ≤ 1 / 2 := hetaSmall.trans (min_le_left _ _)
  have hCeta : C * eta ≤ delta / 2 := by
    have := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp
      (hetaSmall.trans (min_le_right _ _))
    nlinarith
  have hmap : (capInitialPartialDiffeomorph initial).target ⊆ U := by
    change initial.chart '' F.standard_initial.metric.ball 0 A ⊆ U
    rw [comparison.choose_spec.2.2.2.1]
  have hnear (s : ℝ) (hs : s ∈ Ico 0 c) (z : UnitTwoSphere) :
      ‖metricTwoJet ((G.flow.metric s).pullbackCoefficients
          (M44.targetChart (capInitialPartialDiffeomorph initial) p))
          (M44.StandardCylinderPatch.sphereMap N z) -
        metricTwoJet (S.metric s).euclideanCoefficients
          (M44.StandardCylinderPatch.sphereMap N z)‖ ≤ delta / 2 := by
    have hz : M44.StandardCylinderPatch.sphereMap N z ∈ F.standard_initial.metric.ball 0 A := by
      rw [hinitial]
      exact hball z
    rw [cap_ordinary_twoJet_eq e initial G hmap p s hs hz]
    exact (htwo F hinitial S hS t hT hn i (Ico 0 c) U e initial eta heta hetaHalf comparison
      s hs (hs.2.le.trans hctheta) _ hz).trans hCeta
  cases hinitial
  cases hS
  exact M44.exists_terminal_sphere_twoJet_tail standard htheta N hdelta hc hctheta
    (fun s => (G.flow.metric s).pullbackCoefficients
      (M44.targetChart (capInitialPartialDiffeomorph initial) p)) hnear

end PoincareConjecture.M47
