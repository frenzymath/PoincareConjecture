import PoincareConjecture.Proofs.M35.CapGeometry.InitialSlabScalar
import PoincareConjecture.Proofs.M35.RawFlow.ArclengthSlabContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

local notation "V" => StandardCapSpace

theorem initial_intrinsic_axis_escapes_compact
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta : ℝ}
    (htheta : theta ∈ Ico 0 E.flow.base.lifetime)
    {K : Set V} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Icc 0 theta, ∀ s ≥ R,
      rawInverseRadius P E.flow.base E.rotation_invariant t s •
        EuclideanSpace.single (2 : Fin 3) (1 : ℝ) ∉ K := by
  let F (p : ℝ × V) := radialArclength (E.flow.metric p.1) ‖p.2‖
  have hF : ContinuousOn F (Icc 0 theta ×ˢ K) :=
    (raw_radialArclength_continuousOn_slab E.flow.base htheta.1 htheta.2).comp
      (continuousOn_fst.prodMk continuousOn_snd.norm)
      (fun _ hp => ⟨hp.1, mem_univ _⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hF
  refine ⟨max 1 (C + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht s hs hinside
  have hspos : 0 < s := (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).trans_le hs
  have htG : t ∈ Ico 0 E.flow.base.lifetime := ⟨ht.1, ht.2.trans_lt htheta.2⟩
  have hr := rawInverseRadius_pos P E.flow.base E.rotation_invariant htG hspos
  have hnorm : ‖rawInverseRadius P E.flow.base E.rotation_invariant t s •
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ =
        rawInverseRadius P E.flow.base E.rotation_invariant t s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simp
  have h := hC (t, rawInverseRadius P E.flow.base E.rotation_invariant t s •
    EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) ⟨ht, hinside⟩
  change |radialArclength (E.flow.metric t) ‖_‖| ≤ C at h
  have hinverse : radialArclength (E.flow.metric t)
      (rawInverseRadius P E.flow.base E.rotation_invariant t s) = s := by
    convert! radialArclength_rawInverseRadius P E.flow.base E.rotation_invariant htG s using 1
  rw [hnorm, hinverse, abs_of_pos hspos] at h
  have hlarge := (le_max_right 1 (C + 1)).trans hs
  linarith only [h, hlarge]

theorem exists_initial_intrinsic_scalar_control
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta eta : ℝ}
    (htheta : theta ∈ Ico 0 E.flow.base.lifetime) (heta : 0 < eta) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Icc 0 theta, ∀ s ≥ R,
      |(1 - t) * (E.flow.connection t).scalarCurvature
        (rawInverseRadius P E.flow.base E.rotation_invariant t s •
          EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) - 1| < eta := by
  obtain ⟨K, hK, hscalar⟩ := exists_initial_slab_scalar_control E htheta heta
  obtain ⟨R, hR, hescape⟩ := initial_intrinsic_axis_escapes_compact P E htheta hK
  exact ⟨R, hR, fun t ht s hs => hscalar _ (hescape t ht s hs) t ht⟩

theorem initial_intrinsic_axis_scalar_tendsto
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta : ℝ}
    (htheta : theta ∈ Ico 0 E.flow.base.lifetime)
    (t s : ℕ → ℝ) (ht : ∀ k, t k ∈ Icc 0 theta)
    {t₀ : ℝ} (ht₀ : t₀ < 1) (htlim : Tendsto t atTop (𝓝 t₀))
    (hslim : Tendsto s atTop atTop) :
    Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature
      (rawInverseRadius P E.flow.base E.rotation_invariant (t k) (s k) •
        EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) atTop (𝓝 (1 / (1 - t₀))) := by
  let S k := (E.flow.connection (t k)).scalarCurvature
    (rawInverseRadius P E.flow.base E.rotation_invariant (t k) (s k) •
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
  have hnormalize : Tendsto (fun k => (1 - t k) * S k) atTop (𝓝 1) := by
    apply Metric.tendsto_atTop.mpr
    intro eta heta
    obtain ⟨R, _hR, hcontrol⟩ := exists_initial_intrinsic_scalar_control P E htheta heta
    obtain ⟨n, hn⟩ := eventually_atTop.mp (hslim.eventually_ge_atTop R)
    exact ⟨n, fun k hk => by
      simpa only [Real.dist_eq, S] using hcontrol (t k) (ht k) (s k) (hn k hk)⟩
  have hdiv := hnormalize.div ((tendsto_const_nhds (x := (1 : ℝ))).sub htlim)
    (sub_pos.mpr ht₀).ne'
  apply hdiv.congr'
  apply Eventually.of_forall
  intro k
  have hkone : t k < 1 := (ht k).2.trans_lt (E.lifetime_one ▸ htheta.2)
  exact mul_div_cancel_left₀ (S k) (sub_pos.mpr hkone).ne'

end PoincareConjecture.M35.Uniqueness
