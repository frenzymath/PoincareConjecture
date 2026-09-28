import PoincareConjecture.Proofs.M35.CapGeometry.InitialNormalizedProfile
import PoincareConjecture.Proofs.M35.Thm12_28.CompactScalarConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

def InitialRadialComparison (P : RicciFlowCurvatureTheory.{0})
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t a epsilon : ℝ) : Prop :=
  let Q := (E.flow.connection t).scalarCurvature
    (rawInverseRadius P E.flow.base E.rotation_invariant t a •
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
  let b := (Real.sqrt Q)⁻¹
  0 < a - b * epsilon⁻¹ ∧ RoundCylinderClose epsilon 0 (radialCylinderTensor
    (fun u => Q * rawWarpingRadius P E.flow.base E.rotation_invariant t (a + b * u) ^ 2) 1)

theorem initial_radial_comparison_eventually
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta epsilon : ℝ}
    (htheta : 0 < theta) (hthetalt : theta < E.flow.base.lifetime) (he : 0 < epsilon)
    (t a : ℕ → ℝ) (ht : ∀ k, t k ∈ Icc 0 theta)
    {t₀ : ℝ} (ht₀ : t₀ < 1) (htlim : Tendsto t atTop (𝓝 t₀))
    (halim : Tendsto a atTop atTop) :
    ∀ᶠ k in atTop, InitialRadialComparison P E (t k) (a k) epsilon := by
  let Q k := (E.flow.connection (t k)).scalarCurvature
    (rawInverseRadius P E.flow.base E.rotation_invariant (t k) (a k) •
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
  let b k := (Real.sqrt (Q k))⁻¹
  let B k := radialCylinderTensor (fun u => Q k *
    rawWarpingRadius P E.flow.base E.rotation_invariant (t k) (a k + b k * u) ^ 2) 1
  let K : Set RoundCylinderSpace := univ ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  have hseq : ∀ (idx : ℕ → ℕ), Tendsto idx atTop atTop →
      ∀ (z : ℕ → RoundCylinderSpace), (∀ k, z k ∈ K) →
      ∀ z₀ ∈ K, Tendsto z atTop (𝓝 z₀) →
        Tendsto (fun k => roundCylinderJetErrorSquared 0 (B (idx k))
          ⌊epsilon⁻¹⌋₊ (z k)) atTop (𝓝 0) := by
    intro idx hidx z _hz z₀ _hz₀ hlim
    exact initial_normalized_radial_jetError_tendsto_zero P E htheta hthetalt
      (t ∘ idx) (a ∘ idx) (fun k => (z k).2) (fun k => ht (idx k)) ht₀
      (htlim.comp hidx) (halim.comp hidx)
      ((continuous_snd.tendsto z₀).comp hlim) (fun k => (z k).1) ⌊epsilon⁻¹⌋₊
  obtain ⟨n, hn⟩ := OrdinaryRealization.uniform_of_moving_point_limits
    (F := fun k z => roundCylinderJetErrorSquared 0 (B k) ⌊epsilon⁻¹⌋₊ z)
    (G := fun _ => 0) hK continuousOn_const hseq (by positivity : 0 < epsilon ^ 2 / 2)
  have hQlim : Tendsto Q atTop (𝓝 (1 / (1 - t₀))) :=
    initial_intrinsic_axis_scalar_tendsto P E ⟨htheta.le, hthetalt⟩ t a ht ht₀ htlim halim
  have hb : Tendsto b atTop (𝓝 ((Real.sqrt (1 / (1 - t₀)))⁻¹)) :=
    ((Real.continuous_sqrt.tendsto _).comp hQlim).inv₀
      (Real.sqrt_pos.mpr (one_div_pos.mpr (sub_pos.mpr ht₀))).ne'
  have hinnerlim : Tendsto (fun k => a k - b k * epsilon⁻¹) atTop atTop := by
    simpa only [sub_eq_add_neg] using halim.atTop_add (hb.mul_const epsilon⁻¹).neg
  filter_upwards [eventually_ge_atTop n, hinnerlim.eventually_gt_atTop 0] with k hk hinner
  refine ⟨hinner, ?_, epsilon ^ 2 / 2, by nlinarith only [sq_pos_of_pos he], ?_⟩
  · intro q i j p _hp
    apply (radialCylinderTensor_coefficient_contDiffAt 1 q ?_ i j).contDiffWithinAt
    have htime : t k ∈ Ico 0 E.flow.base.lifetime :=
      ⟨(ht k).1, (ht k).2.trans_lt hthetalt⟩
    have hf : ContDiff ℝ ∞ (rawWarpingRadius P E.flow.base E.rotation_invariant (t k)) := by
      rw [rawWarpingRadius_eq P E.flow.base E.rotation_invariant htime]
      exact intrinsicWarpingRadius_contDiff _ _ _
    exact (contDiff_const.mul ((hf.pow 2).comp
      (contDiff_const.add (contDiff_const.mul contDiff_id)))).contDiffAt
  · intro z hz
    have hh := hn k hk z ⟨mem_univ _, ⟨hz.1.le, hz.2.le⟩⟩
    rw [sub_zero] at hh
    exact le_of_lt ((le_abs_self _).trans_lt hh)

theorem exists_initial_radial_comparison_threshold
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta epsilon : ℝ}
    (htheta : 0 < theta) (hthetalt : theta < E.flow.base.lifetime) (he : 0 < epsilon) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Icc 0 theta, ∀ a ≥ R,
      InitialRadialComparison P E t a epsilon := by
  classical
  by_contra h
  push Not at h
  choose t ht a ha hbad using fun n : ℕ => h ((n : ℝ) + 1) (by positivity)
  have halim : Tendsto a atTop atTop := by
    refine tendsto_atTop.2 fun B => ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop B] with k hk
    linarith only [ha k, hk]
  obtain ⟨t₀, ht₀, phi, hphi, hlim⟩ := isCompact_Icc.tendsto_subseq ht
  have hgood := initial_radial_comparison_eventually P E htheta hthetalt he
    (t ∘ phi) (a ∘ phi) (fun k => ht (phi k))
    (ht₀.2.trans_lt (E.lifetime_one ▸ hthetalt)) hlim (halim.comp hphi.tendsto_atTop)
  obtain ⟨k, hk⟩ := hgood.exists
  exact hbad (phi k) hk

end PoincareConjecture.M35.Uniqueness
