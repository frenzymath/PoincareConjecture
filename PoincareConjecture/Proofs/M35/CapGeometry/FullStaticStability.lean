import PoincareConjecture.Proofs.M35.CapGeometry.FullNeckJetDifference
import PoincareConjecture.Proofs.M35.Thm12_28.NeckStrictMargin
import PoincareConjecture.Proofs.M35.Thm12_28.NeckFiniteMetricJets










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "E2" => EuclideanSpace ℝ (Fin 2)



theorem full_neck_rescaled_coefficient_jets_uniform
    {epsilon : ℝ} {C : RoundCylinderTwoTensor}
    (he : 0 < epsilon) (hC : RoundCylinderClose epsilon 0 C)
    (B : ℕ → RoundCylinderTwoTensor) (hB : ∀ k, RoundCylinderTensorSmoothOn epsilon (B k))
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 1))
    (hjet : ∀ r ≤ ⌊epsilon⁻¹⌋₊, ∀ i j : Fin 3, ∀ eta : ℝ, 0 < eta →
      ∃ K : ℕ, ∀ k ≥ K, ∀ q : UnitTwoSphere, ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
        ‖iteratedFDeriv ℝ r (fun y => roundCylinderTensorCoefficient (B k)
          (chartAt E2 q) y i j - roundCylinderTensorCoefficient C
            (chartAt E2 q) y i j) (0, s)‖ < eta)
    (r : ℕ) (hr : r ≤ ⌊epsilon⁻¹⌋₊) (i j : Fin 3) (eta : ℝ) (heta : 0 < eta) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ q : UnitTwoSphere, ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      ‖iteratedFDeriv ℝ r (fun y => roundCylinderTensorCoefficient
        (fun z v w => a k * B k z v w) (chartAt E2 q) y i j -
        roundCylinderTensorCoefficient C (chartAt E2 q) y i j) (0, s)‖ < eta := by
  classical
  by_contra hn
  push Not at hn
  choose sigma hsigma q s hs hbad using hn
  have hsig : Tendsto sigma atTop atTop := tendsto_atTop_mono hsigma tendsto_id
  let f (k : ℕ) (y : RoundCylinderCoordinates) :=
    roundCylinderTensorCoefficient (B (sigma k)) (chartAt E2 (q k)) y i j
  let g (k : ℕ) (y : RoundCylinderCoordinates) :=
    roundCylinderTensorCoefficient C (chartAt E2 (q k)) y i j
  have hf (k : ℕ) : ContDiffAt ℝ ∞ (f k) (0, s k) := by
    apply (hB (sigma k) (q k) i j).contDiffAt
    apply ((chartAt E2 (q k)).open_target.prod isOpen_Ioo).mem_nhds
    exact ⟨by rw [sphere_chart_target]; trivial, hs k⟩
  have hg (k : ℕ) : ContDiffAt ℝ ∞ (g k) (0, s k) :=
    hC.contDiffAt_coefficient (q k) (0, s k) (hs k) i j
  have herr : Tendsto (fun k => iteratedFDeriv ℝ r (fun y => f k y - g k y) (0, s k))
      atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro d hd
    obtain ⟨K, hK⟩ := hjet r hr i j d hd
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hsig.eventually (eventually_ge_atTop K))
    refine ⟨J, ?_⟩
    intro k hk
    simpa only [dist_zero_right] using hK (sigma k) (hJ k hk) (q k) (s k) (hs k)
  obtain ⟨D, _hD, hbound⟩ := full_neck_metric_coefficient_jet_bounds hC he r hr
  have hsmall : Tendsto (fun k => (a (sigma k) - 1) •
      iteratedFDeriv ℝ r (g k) (0, s k)) atTop (𝓝 0) := by
    have hb : ∀ᶠ k in atTop, ‖(a (sigma k) - 1) •
        iteratedFDeriv ℝ r (g k) (0, s k)‖ ≤ ‖a (sigma k) - 1‖ * D := by
      filter_upwards [] with k
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hbound (q k) (s k) (hs k) i j) (norm_nonneg _)
    apply squeeze_zero_norm' hb
    simpa only [Function.comp_apply, sub_self, norm_zero, zero_mul] using
      (((ha.comp hsig).sub (tendsto_const_nhds (x := (1 : ℝ)))).norm.mul_const D)
  have hmain : Tendsto (fun k => a (sigma k) •
      iteratedFDeriv ℝ r (fun y => f k y - g k y) (0, s k)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, smul_zero] using (ha.comp hsig).smul herr
  have hlim : Tendsto (fun k => iteratedFDeriv ℝ r
      (fun y => a (sigma k) * f k y - g k y) (0, s k)) atTop (𝓝 0) := by
    have hh := hmain.add hsmall
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards [] with k
    have hr' : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
    symm
    change iteratedFDeriv ℝ r (fun y => a (sigma k) • f k y - g k y) (0, s k) = _
    rw [fun_iteratedFDeriv_sub_apply (((hf k).const_smul (a (sigma k))).of_le hr')
      ((hg k).of_le hr')]
    change iteratedFDeriv ℝ r (a (sigma k) • f k) (0, s k) - _ = _
    rw [iteratedFDeriv_const_smul_apply ((hf k).of_le hr'),
      fun_iteratedFDeriv_sub_apply ((hf k).of_le hr') ((hg k).of_le hr')]
    simp only [smul_sub, sub_smul, one_smul]
    abel
  have hnorm := hlim.norm
  rw [norm_zero] at hnorm
  exact (not_le.mpr heta) (ge_of_tendsto hnorm (Eventually.of_forall (fun k => hbad k)))



theorem eventually_full_static_close_of_rescaled_coefficients
    {epsilon : ℝ} {C : RoundCylinderTwoTensor}
    (he : 0 < epsilon) (hC : RoundCylinderClose epsilon 0 C)
    (B : ℕ → RoundCylinderTwoTensor) (hB : ∀ k, RoundCylinderTensorSmoothOn epsilon (B k))
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 1))
    (hjet : ∀ r ≤ ⌊epsilon⁻¹⌋₊, ∀ i j : Fin 3, ∀ eta : ℝ, 0 < eta →
      ∃ K : ℕ, ∀ k ≥ K, ∀ q : UnitTwoSphere, ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
        ‖iteratedFDeriv ℝ r (fun y => roundCylinderTensorCoefficient (B k)
          (chartAt E2 q) y i j - roundCylinderTensorCoefficient C
            (chartAt E2 q) y i j) (0, s)‖ < eta) :
    ∀ᶠ k in atTop, RoundCylinderClose epsilon 0 (fun z v w => a k * B k z v w) := by
  let B' (k : ℕ) : RoundCylinderTwoTensor := fun z v w => a k * B k z v w
  have hB' (k : ℕ) : RoundCylinderTensorSmoothOn epsilon (B' k) :=
    fun q i j => (hB k q i j).const_smul (a k)
  have hfamily : RoundCylinderFamilyClose epsilon {0} (fun _ => C) := by
    refine ⟨fun _ _ => hC.1, hC.2.choose, hC.2.choose_spec.1, ?_⟩
    intro u hu z hz
    have hu0 : u = 0 := mem_singleton_iff.mp hu
    simpa only [hu0] using hC.2.choose_spec.2 z hz
  obtain ⟨eta, heta, hmargin⟩ := hfamily.exists_same_epsilon_perturbation_margin
    (fun u hu => by simpa only [mem_singleton_iff.mp hu] using zero_lt_one)
  have hAt (D : RoundCylinderTwoTensor) (hD : RoundCylinderTensorSmoothOn epsilon D)
      (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) (i j : Fin 3) :
      ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient D (chartAt E2 q) y i j)
        (0, s) := by
    apply (hD q i j).contDiffAt
    apply ((chartAt E2 q).open_target.prod isOpen_Ioo).mem_nhds
    exact ⟨by rw [sphere_chart_target]; trivial, hs⟩
  obtain ⟨K, hK⟩ := full_cylinder_jet_difference_uniform ⌊epsilon⁻¹⌋₊ {0}
    isCompact_singleton (fun u hu => by simpa only [mem_singleton_iff.mp hu] using zero_lt_one)
    epsilon⁻¹ (fun k _ => B' k) (fun _ _ => C)
    (fun k _ _ => hAt _ (hB' k)) (fun _ _ _ => hAt _ hC.1) (by
      intro r hr i j d hd
      obtain ⟨J, hJ⟩ := full_neck_rescaled_coefficient_jets_uniform
        he hC B hB a ha hjet r hr i j d hd
      exact ⟨J, fun k hk _ _ => hJ k hk⟩) eta heta
  filter_upwards [eventually_ge_atTop K] with k hk
  have hh := hmargin (fun _ => B' k) (fun _ _ => hB' k)
    (fun u hu z hz => (hK k hk u hu z hz).le)
  exact ⟨hh.1 0 (mem_singleton 0), hh.2.choose, hh.2.choose_spec.1,
    hh.2.choose_spec.2 0 (mem_singleton 0)⟩

end PoincareConjecture.M35
