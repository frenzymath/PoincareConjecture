import PoincareConjecture.Proofs.M47.CanonicalNeckCoefficientBounds
import PoincareConjecture.Proofs.M47.CanonicalNeckMetricJets
import PoincareConjecture.Proofs.M47.CanonicalNeckStrictMargin
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCovariantDifference










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M]




theorem eventually_weighted_neck_metric_jets
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    (t : Icc a b) (N : EpsilonNeck (F.metric t.val))
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹)
    {K : Set M} (hK : IsCompact K) (hNK : N.carrier ⊆ K)
    (lambda : Icc a b → ℝ) (hlambda : ContinuousAt lambda t)
    {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ s : Icc a b in 𝓝 t, ∀ (q : UnitTwoSphere) (z : ℝ),
      z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → ∀ j ≤ m, ∀ i l : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (fun z v w =>
              lambda s * roundCylinderPullback (F.metric s.val) N.coordinate_map z v w)
              (chartAt E₂ q) y i l -
            roundCylinderTensorCoefficient (fun z v w =>
              lambda t * roundCylinderPullback (F.metric t.val) N.coordinate_map z v w)
              (chartAt E₂ q) y i l) (0, z)‖ < rho := by
  obtain ⟨D, hD, hDbound⟩ := exists_neck_metric_coefficient_jet_bound N m hm
  let L := |lambda t| + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  let eta := min 1 (rho / (2 * (L + D + 1)))
  have hden : 0 < 2 * (L + D + 1) := by linarith
  have heta : 0 < eta := lt_min zero_lt_one (div_pos hrho hden)
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hsmall : (L + D) * eta < rho := by
    have h := (le_div_iff₀ hden).mp
      (min_le_right (1 : ℝ) (rho / (2 * (L + D + 1))))
    change eta * (2 * (L + D + 1)) ≤ rho at h
    nlinarith
  have hweight : ∀ᶠ s in 𝓝 t, |lambda s - lambda t| < eta :=
    (hlambda.sub continuousAt_const).abs.eventually
      (Iio_mem_nhds (by
        change |lambda t - lambda t| < eta
        simpa only [sub_self, abs_zero] using heta))
  filter_upwards [eventually_neck_metric_jets hab F t N m hm hK hNK heta, hweight]
    with s hs hweight q z hz j hj i l
  have hweight' : |lambda s| ≤ L := by
    have h := abs_sub_abs_le_abs_sub (lambda s) (lambda t)
    dsimp only [L]
    linarith
  have hcenter : (0, z) ∈ (chartAt E₂ q).target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    refine ⟨?_, hz⟩
    simpa only [sphere_chart_center_zero] using (chartAt E₂ q).map_source (mem_chart_source E₂ q)
  have hnew := (capPersistence_roundCylinderTensorSmoothOn_pullback
    (F.metric s.val) N.coordinate_map_smooth q i l).contDiffAt
      (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hcenter)
  have hold := (capPersistence_roundCylinderTensorSmoothOn_pullback
    (F.metric t.val) N.coordinate_map_smooth q i l).contDiffAt
      (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hcenter)
  change ‖iteratedFDeriv ℝ j (fun y =>
    lambda s * roundCylinderTensorCoefficient (roundCylinderPullback (F.metric s.val)
        N.coordinate_map) (chartAt E₂ q) y i l -
      lambda t * roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t.val)
        N.coordinate_map) (chartAt E₂ q) y i l) (0, z)‖ < rho
  apply (norm_iteratedFDeriv_weighted_sub_le hnew hold (lambda s) (lambda t) j).trans_lt
  calc
    _ ≤ L * eta + eta * D := add_le_add
      (mul_le_mul hweight' (hs q z hz j hj i l).le (norm_nonneg _) hL.le)
      (mul_le_mul hweight.le (hDbound q z hz j hj i l) (norm_nonneg _) heta.le)
    _ = (L + D) * eta := by ring
    _ < rho := hsmall




theorem eventually_normalized_neck_comparison
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    (t : Icc a b) (N : EpsilonNeck (F.metric t.val))
    {K : Set M} (hK : IsCompact K) (hNK : N.carrier ⊆ K)
    (lambda : Icc a b → ℝ) (hlambda : ContinuousAt lambda t)
    (hvalue : lambda t = N.scale⁻¹ ^ 2) :
    ∀ᶠ s : Icc a b in 𝓝 t, RoundCylinderClose N.epsilon 0
      (fun z v w => lambda s *
        roundCylinderPullback (F.metric s.val) N.coordinate_map z v w) := by
  let D : RoundCylinderTwoTensor := fun z v w => N.scale⁻¹ ^ 2 *
    roundCylinderPullback (F.metric t.val) N.coordinate_map z v w
  obtain ⟨eta, heta, hperturb⟩ := exists_same_epsilon_neck_perturbation_tolerance
    N.epsilon_pos D N.metric_comparison.close
  let K0 : Set RoundCylinderCoordinates := ({0} : Set E₂) ×ˢ Icc (-N.epsilon⁻¹) N.epsilon⁻¹
  obtain ⟨A, hA, hAbound⟩ := exists_roundCylinder_covariant_difference_component_bound
    (isCompact_singleton (x := (0 : ℝ)))
    (by rintro u rfl; norm_num : ({0} : Set ℝ) ⊆ Iio 1)
    (isCompact_singleton.prod isCompact_Icc : IsCompact K0) (Nat.floor N.epsilon⁻¹)
  let rho := eta / (A + 1)
  have hrho : 0 < rho := div_pos heta (by positivity)
  have hsmall : A * rho ≤ eta := by
    have heq : (A + 1) * rho = eta := by dsimp only [rho]; field_simp
    nlinarith
  filter_upwards [eventually_weighted_neck_metric_jets hab F t N
    (Nat.floor N.epsilon⁻¹) le_rfl hK hNK lambda hlambda hrho] with s hs
  let B : RoundCylinderTwoTensor := fun z v w => lambda s *
    roundCylinderPullback (F.metric s.val) N.coordinate_map z v w
  have hB : RoundCylinderTensorSmoothOn N.epsilon B :=
    (capPersistence_roundCylinderTensorSmoothOn_pullback
      (F.metric s.val) N.coordinate_map_smooth).const_mul
  apply hperturb B hB
  intro z hz k hk a
  have hcenter : (0, z.2) ∈ (chartAt E₂ z.1).target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    refine ⟨?_, hz⟩
    simpa only [sphere_chart_center_zero] using
      (chartAt E₂ z.1).map_source (mem_chart_source E₂ z.1)
  have h := hAbound 0 (mem_singleton 0) z.1 B D N.epsilon hB
    N.metric_comparison.close.1 (0, z.2) ⟨mem_singleton 0, hz.1.le, hz.2.le⟩
    hcenter rho hrho.le (fun j hj i l => ?_) k hk a
  · simpa only [sphere_chart_center_zero] using h.trans hsmall
  · simpa only [hvalue] using (hs z.1 z.2 hz j hj i l).le

end PoincareConjecture.Proofs.M47
