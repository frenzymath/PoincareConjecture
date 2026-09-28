import PoincareConjecture.Proofs.M47.CanonicalNeckCompressedMetricJets
import PoincareConjecture.Proofs.M47.CanonicalNeckSpatialModulus
import PoincareConjecture.Proofs.M47.CanonicalNeckClockBuffer
import PoincareConjecture.Proofs.M47.CanonicalNeckCoefficientBounds
import PoincareConjecture.Proofs.M47.CanonicalNeckAxialCompression

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates

private theorem norm_iteratedFDeriv_sub_triangle
    {f k g : V → ℝ} {x : V} (hf : ContDiffAt ℝ ∞ f x)
    (hk : ContDiffAt ℝ ∞ k x) (hg : ContDiffAt ℝ ∞ g x) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => f y - g y) x‖ ≤
      ‖iteratedFDeriv ℝ j (fun y => f y - k y) x‖ +
        ‖iteratedFDeriv ℝ j (fun y => k y - g y) x‖ := by
  change ‖iteratedFDeriv ℝ j (f - g) x‖ ≤
    ‖iteratedFDeriv ℝ j (f - k) x‖ + ‖iteratedFDeriv ℝ j (k - g) x‖
  rw [iteratedFDeriv_sub_apply (hf.of_le (by exact_mod_cast le_top))
      (hg.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_sub_apply (hf.of_le (by exact_mod_cast le_top))
      (hk.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_sub_apply (hk.of_le (by exact_mod_cast le_top))
      (hg.of_le (by exact_mod_cast le_top))]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

theorem eventually_buffered_normalized_neck_jets
    {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    {lambda : ℝ} (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    {X : Type*} [TopologicalSpace X] {T Q c : X → ℝ} {p0 : X}
    (hT : ContinuousAt T p0) (hQ : ContinuousAt Q p0) (hc : ContinuousAt c p0)
    (hc0 : c p0 = 0) (hQ0 : 0 < Q p0)
    (hbottom : a < T p0 - (Q p0)⁻¹) (htop : T p0 < b)
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹) {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ p in 𝓝 p0, 0 < Q p ∧ |c p| < (1 - lambda) * N.epsilon⁻¹ ∧
      ∀ u ∈ Icc (-1 : ℝ) 0, T p + u / Q p ∈ Icc a b ∧
        ∀ q : UnitTwoSphere, ∀ z ∈ Icc (-N.epsilon⁻¹) N.epsilon⁻¹,
          ∀ j ≤ m, ∀ i l : Fin 3,
            ‖iteratedFDeriv ℝ j (fun y =>
              Q p * roundCylinderTensorCoefficient
                  (neckAxialTensorPullback lambda (c p)
                    (roundCylinderPullback (F.metric (T p + u / Q p)) N.coordinate_map))
                  (chartAt E₂ q) y i l -
                Q p0 * roundCylinderTensorCoefficient
                  (neckAxialTensorPullback lambda 0
                    (roundCylinderPullback (F.metric (T p0 + u / Q p0)) N.coordinate_map))
                  (chartAt E₂ q) y i l) (0, z)‖ < rho := by
  have heps : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hwidth : lambda * N.epsilon⁻¹ < N.epsilon⁻¹ := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hlambda.2 heps
  obtain ⟨R, hleft, hR⟩ := exists_between hwidth
  have hlambda' : lambda ∈ Icc (0 : ℝ) 1 := ⟨hlambda.1.le, hlambda.2.le⟩
  obtain ⟨D, hD, habsolute⟩ := compressed_neck_metric_coefficient_jets_bounded
    hab F N hlambda' hleft.le hR m
  let L := |Q p0| + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hden : 0 < 2 * (2 * L + D + 1) := by positivity
  let eta := min 1 (rho / (2 * (2 * L + D + 1)))
  have heta : 0 < eta := lt_min zero_lt_one (div_pos hrho hden)
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hbudget : (2 * L + D) * eta < rho := by
    have h := (le_div_iff₀ hden).mp (min_le_right 1 (rho / (2 * (2 * L + D + 1))))
    change eta * (2 * (2 * L + D + 1)) ≤ rho at h
    nlinarith only [h, heta, mul_nonneg hL.le heta.le, mul_nonneg hD0 heta.le]
  obtain ⟨deltaS, hdeltaS, hspatial⟩ := exists_neck_compressed_metric_translation_modulus
    hab F N hlambda' hleft hR m heta
  obtain ⟨deltaT, hdeltaT, htime⟩ := compressed_neck_metric_jets_uniform_time_delta
    hab F N hlambda' hleft.le hR m hm heta
  have hclock := eventually_normalized_neck_clock_in_buffer hT hQ hQ0 hbottom htop hdeltaT
  have hbase := hclock.self_of_nhds
  have hQsmall : ∀ᶠ p in 𝓝 p0, |Q p - Q p0| < eta :=
    (hQ.sub continuousAt_const).abs.eventually
      (Iio_mem_nhds (by
        change |Q p0 - Q p0| < eta
        simpa only [sub_self, abs_zero] using heta))
  have hcsmall : ∀ᶠ p in 𝓝 p0, |c p| < deltaS :=
    hc.abs.eventually (Iio_mem_nhds (by simpa only [hc0, abs_zero] using hdeltaS))
  filter_upwards [hclock, hQsmall, hcsmall] with p hp hQp hcp
  have hsp := hspatial (c p) hcp
  have hmargin : |c p| < (1 - lambda) * N.epsilon⁻¹ := by
    nlinarith only [hsp.1, hR]
  have hzero : |(0 : ℝ)| < (1 - lambda) * N.epsilon⁻¹ := by
    rw [abs_zero]
    exact mul_pos (sub_pos.mpr hlambda.2) heps
  have hQbound : |Q p| ≤ L := by
    have h := abs_sub_abs_le_abs_sub (Q p) (Q p0)
    dsimp only [L]
    linarith only [h, hQp, heta1]
  refine ⟨hp.1, hmargin, ?_⟩
  intro u hu
  have hs : T p + u / Q p ∈ Icc a b := Ioo_subset_Icc_self (hp.2 u hu).1
  have hs0 : T p0 + u / Q p0 ∈ Icc a b := Ioo_subset_Icc_self (hbase.2 u hu).1
  refine ⟨hs, ?_⟩
  intro q z hz j hj i l
  let f : V → ℝ := fun y => roundCylinderTensorCoefficient
    (neckAxialTensorPullback lambda (c p)
      (roundCylinderPullback (F.metric (T p + u / Q p)) N.coordinate_map)) (chartAt E₂ q) y i l
  let k : V → ℝ := fun y => roundCylinderTensorCoefficient
    (neckAxialTensorPullback lambda 0
      (roundCylinderPullback (F.metric (T p + u / Q p)) N.coordinate_map)) (chartAt E₂ q) y i l
  let g : V → ℝ := fun y => roundCylinderTensorCoefficient
    (neckAxialTensorPullback lambda 0
      (roundCylinderPullback (F.metric (T p0 + u / Q p0)) N.coordinate_map)) (chartAt E₂ q) y i l
  have hf : ContDiffAt ℝ ∞ f (0, z) := compressed_neck_metric_coefficient_contDiffAt
    N _ lambda (c p) q z i l
      (neckAxialCoordinate_mem_open_interval N.epsilon_pos hlambda hmargin hz)
  have hk : ContDiffAt ℝ ∞ k (0, z) := compressed_neck_metric_coefficient_contDiffAt
    N _ lambda 0 q z i l (neckAxialCoordinate_mem_open_interval N.epsilon_pos hlambda hzero hz)
  have hg : ContDiffAt ℝ ∞ g (0, z) := compressed_neck_metric_coefficient_contDiffAt
    N _ lambda 0 q z i l (neckAxialCoordinate_mem_open_interval N.epsilon_pos hlambda hzero hz)
  have hfk : ‖iteratedFDeriv ℝ j (fun y => f y - k y) (0, z)‖ < eta :=
    hsp.2 _ hs q z hz j hj i l
  have hkg : ‖iteratedFDeriv ℝ j (fun y => k y - g y) (0, z)‖ < eta :=
    htime _ hs _ hs0 (hp.2 u hu).2 q z hz j hj i l
  have hfg : ‖iteratedFDeriv ℝ j (fun y => f y - g y) (0, z)‖ ≤ 2 * eta :=
    (norm_iteratedFDeriv_sub_triangle hf hk hg j).trans
      (by linarith only [hfk, hkg])
  have hgD : ‖iteratedFDeriv ℝ j g (0, z)‖ ≤ D := habsolute _ hs0 q z hz j hj i l
  change ‖iteratedFDeriv ℝ j (fun y => Q p * f y - Q p0 * g y) (0, z)‖ < rho
  apply (norm_iteratedFDeriv_weighted_sub_le hf hg (Q p) (Q p0) j).trans_lt
  calc
    _ ≤ L * (2 * eta) + eta * D := add_le_add
      (mul_le_mul hQbound hfg (norm_nonneg _) hL.le)
      (mul_le_mul hQp.le hgD (norm_nonneg _) heta.le)
    _ = (2 * L + D) * eta := by ring
    _ < rho := hbudget

end PoincareConjecture.Proofs.M47
