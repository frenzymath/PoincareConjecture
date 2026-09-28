import PoincareConjecture.Proofs.M47.LimitCanonicalFamilyMetricJets
import PoincareConjecture.Proofs.M47.CanonicalNeckFamilyMargin
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckPullbackSmooth
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCovariantDifference









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open M34 Proofs.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E₃ G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold



theorem limitCanonical_eventually_neck_family_comparison
    (P : M47Predecessors.{u}) (hJI : Icc (-1 : ℝ) 0 ⊆ J)
    (N : EpsilonNeck (G.limit.flow.metric 0))
    {K : Set G.limit.sliceCarrier.carrier} (hK : IsCompact K) (hNK : N.carrier ⊆ K)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun s => roundCylinderPullback (G.limit.flow.metric s) N.coordinate_map)) :
    ∀ᶠ k in atTop, Icc (-1 : ℝ) 0 ⊆ Icc (-G.exhaustion.time k) 0 ∧
      K ⊆ G.exhaustion.space k ∧
      RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
        (generalizedCylinderPullback (G.embedding k) N.coordinate_map) := by
  let D := fun s => roundCylinderPullback (G.limit.flow.metric s) N.coordinate_map
  obtain ⟨eta, heta, hperturb⟩ := exists_same_epsilon_neck_family_perturbation_tolerance
    N.epsilon_pos (fun _ hs => hs.2) D hfamily
  let K0 : Set RoundCylinderCoordinates :=
    ({0} : Set E₂) ×ˢ Icc (-N.epsilon⁻¹) N.epsilon⁻¹
  obtain ⟨A, hA, hcov⟩ := exists_roundCylinder_covariant_difference_component_bound
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 0))
    (fun _ hs => hs.2.trans_lt zero_lt_one)
    (isCompact_singleton.prod isCompact_Icc : IsCompact K0) (Nat.floor N.epsilon⁻¹)
  let rho := eta / (A + 1)
  have hrho : 0 < rho := div_pos heta (by positivity)
  have hsmall : A * rho ≤ eta := by
    have heq : (A + 1) * rho = eta := by dsimp only [rho]; field_simp
    nlinarith only [heq, hrho]
  filter_upwards [limitCanonical_eventually_neck_family_metric_jets G P N
    (Nat.floor N.epsilon⁻¹) le_rfl isCompact_Icc hJI hK hNK hrho] with k hk
  let B := generalizedCylinderPullback (G.embedding k) N.coordinate_map
  have hB (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) :
      RoundCylinderTensorSmoothOn N.epsilon (B s) :=
    generalizedCylinderPullback_roundCylinderTensorSmoothOn (G.embedding k)
      (G.exhaustion.space_open k) N.coordinate_map_smooth
      (fun z hz => hk.2.1 (hNK (N.coordinate_map_mem_of_axial_mem hz.2)))
      (hk.1 (Ioc_subset_Icc_self hs))
  refine ⟨hk.1, hk.2.1, hperturb B hB ?_⟩
  intro s hs z hz j hj v
  have hcenter : (0, z.2) ∈ (chartAt E₂ z.1).target ×ˢ
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    refine ⟨?_, hz⟩
    simpa only [sphere_chart_center_zero] using
      (chartAt E₂ z.1).map_source (mem_chart_source E₂ z.1)
  have h := hcov s (Ioc_subset_Icc_self hs) z.1 (B s) (D s) N.epsilon (hB s hs)
    (hfamily.1 s hs) (0, z.2) ⟨mem_singleton 0, hz.1.le, hz.2.le⟩ hcenter rho hrho.le
    (fun r hr i l => (hk.2.2 s (Ioc_subset_Icc_self hs) z.1 z.2 hz r hr i l).le) j hj v
  simpa only [sphere_chart_center_zero] using h.trans hsmall

end PoincareConjecture.M47
