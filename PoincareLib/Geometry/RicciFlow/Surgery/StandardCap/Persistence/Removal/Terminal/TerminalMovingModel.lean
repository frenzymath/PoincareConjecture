import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Analysis.Compactness.CompactTimeModulus
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Removal.Sphere.StandardSphereMargin

/-!
# Freezing the moving sphere model at a stopping time

The actual standard flow has a uniform sphere time modulus. A
half-tolerance comparison with its moving two-jet gives the full
closed tolerance on one common terminal tail. Morgan--Tian,
Corollary 16.9 and Claim 16.10, pp. 373-375; M44 derivation 89.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The native two-jet has nested coefficient derivative slots.
set_option maxSynthPendingDepth 16

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance movingSphereCoefficientNorm : NormedAddCommGroup
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance movingSphereCoefficientSpace : NormedSpace ℝ
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance movingSphereTwoJetNorm : NormedAddCommGroup
    (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance movingSphereTwoJetSpace : NormedSpace ℝ
    (MetricTwoJet 3) := Prod.normedSpace

/-- On one late-time interval, comparison to the moving standard
two-jet implies comparison to the fixed endpoint two-jet, uniformly
on the whole sphere. Source: Claim 16.10, pp. 374-375; derivation 89. -/
theorem exists_terminal_sphere_twoJet_tail
    {g0 : StandardInitialMetric} (S : RepairedStandardCapExistenceData g0)
    {theta : ℝ} (htheta : theta < 1)
    {length : ℝ} {center : E} (N : StandardCylinderPatch length center)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (hctheta : c ≤ theta)
    (B : ℝ → E → MetricCoefficient 3)
    (hnear : ∀ s ∈ Ico (0 : ℝ) c, ∀ z : UnitTwoSphere,
      ‖metricTwoJet (B s) (StandardCylinderPatch.sphereMap N z) -
        metricTwoJet (S.flow.metric s).euclideanCoefficients
          (StandardCylinderPatch.sphereMap N z)‖ ≤ d / 2) :
    ∃ s0 : ℝ, s0 < c ∧ ∀ s ∈ Ico (0 : ℝ) c, s0 ≤ s → ∀ z : UnitTwoSphere,
      ‖metricTwoJet (B s) (StandardCylinderPatch.sphereMap N z) -
        metricTwoJet (S.flow.metric c).euclideanCoefficients
          (StandardCylinderPatch.sphereMap N z)‖ ≤ d := by
  have hsub : Icc (0 : ℝ) theta ⊆ Ico (0 : ℝ) S.flow.base.lifetime := by
    rw [S.lifetime_one]
    exact fun _ ht => ⟨ht.1, ht.2.trans_lt htheta⟩
  have hcont : ContinuousOn (fun p : ℝ × UnitTwoSphere =>
      metricTwoJet (S.flow.metric p.1).euclideanCoefficients
        (StandardCylinderPatch.sphereMap N p.2)) (Icc (0 : ℝ) theta ×ˢ univ) :=
    (continuousOn_euclidean_twoJet (uniqueDiffOn_Ico 0 S.flow.base.lifetime)
      S.flow.base.flow).comp
        (continuous_fst.prodMk
          ((StandardCylinderPatch.sphereMap N).continuous.comp continuous_snd)).continuousOn
        (fun _ hp => ⟨hsub hp.1, mem_univ _⟩)
  obtain ⟨delta, hdelta, hmod⟩ := hcont.exists_uniform_time_delta
    isCompact_Icc isCompact_univ (half_pos hd)
  refine ⟨c - delta / 2, sub_lt_self c (half_pos hdelta), ?_⟩
  intro s hs htail z
  have hsc : |s - c| < delta := by
    rw [abs_of_neg (sub_neg.mpr hs.2)]
    linarith
  have hmodel := hmod s ⟨hs.1, hs.2.le.trans hctheta⟩ c ⟨hc.le, hctheta⟩ hsc z
    (mem_univ z)
  rw [dist_eq_norm] at hmodel
  calc
    _ ≤ ‖metricTwoJet (B s) (StandardCylinderPatch.sphereMap N z) -
        metricTwoJet (S.flow.metric s).euclideanCoefficients
          (StandardCylinderPatch.sphereMap N z)‖ +
      ‖metricTwoJet (S.flow.metric s).euclideanCoefficients
          (StandardCylinderPatch.sphereMap N z) -
        metricTwoJet (S.flow.metric c).euclideanCoefficients
          (StandardCylinderPatch.sphereMap N z)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ d / 2 + d / 2 := add_le_add (hnear s hs z) hmodel.le
    _ = d := by ring

end PoincareMT.M44
