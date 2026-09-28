import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeMetric
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_MinimizingSequence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  (j : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
    G.gaugeCover.spatial j) (x0 : G.gaugeCover.spatial j)

include x0 in



theorem compact_gauge_square_velocity_bound {U K : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel 3) (spacetimeModel 3) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder j).toSpacetime (lift q) = q)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ c : ℝ, 0 < c ∧ ∀ {T tau : ℝ} {x y : G.Point}
      (p : M14BackwardPath G T 0 tau x y) {a b D : ℝ},
      0 ≤ a → b ≤ Real.sqrt tau → a ≤ b →
      IntervalIntegrable (M14.pathSquareKinetic p) volume 0 (Real.sqrt tau) →
      (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic p s) ≤ D →
      (∀ s ∈ Icc a b, p.curve (s ^ 2) ∈ K) →
      ∃ hLp : MemLp (deriv (fun s => (lift (p.curve (s ^ 2))).2.val)) 2
          (volume.restrict (Icc a b)),
        ‖hLp.toLp (deriv (fun s => (lift (p.curve (s ^ 2))).2.val))‖ ≤
          Real.sqrt (c⁻¹ * D) := by
  obtain ⟨c, hc, hcoercive⟩ := compact_gaugeLiftMetric_coercive j lift x0 hlift hK hKU
  refine ⟨c, hc, ?_⟩
  intro T tau x y p a b D ha hb hab henergy hbound hsrc
  let d := deriv (fun s => (lift (p.curve (s ^ 2))).2.val)
  have hd : AEStronglyMeasurable d (volume.restrict (Icc a b)) :=
    aestronglyMeasurable_deriv _ _
  have hint := henergy.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le (Real.sqrt_nonneg tau)]
    exact Icc_subset_Icc ha hb)
  have hq : IntegrableOn (M14.pathSquareKinetic p) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hint
  have hpoint : ∀ᵐ s ∂volume.restrict (Icc a b),
      ‖d s‖ ^ 2 ≤ c⁻¹ * M14.pathSquareKinetic p s := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have h := hcoercive (p.curve (s ^ 2)) (hsrc s (Ioo_subset_Icc_self hs)) (d s)
    rw [squarePath_gaugeLiftMetric_eq j lift x0 p hlift hright ha hb hs
      (fun r hr => hKU (hsrc r hr))] at h
    calc
      ‖d s‖ ^ 2 = c⁻¹ * (c * ‖d s‖ ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ c⁻¹ * M14.pathSquareKinetic p s :=
        mul_le_mul_of_nonneg_left h (inv_pos.mpr hc).le
  have hd2 : Integrable (fun s => ‖d s‖ ^ 2) (volume.restrict (Icc a b)) := by
    apply (hq.const_mul c⁻¹).mono' (hd.norm.pow 2)
    filter_upwards [hpoint] with s hs
    change |‖d s‖ ^ 2| ≤ c⁻¹ * M14.pathSquareKinetic p s
    simpa only [abs_of_nonneg (sq_nonneg ‖d s‖)] using hs
  have hLp : MemLp d 2 (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq_norm hd).mpr hd2
  refine ⟨hLp, Real.le_sqrt_of_sq_le ?_⟩
  have hnorm : ‖hLp.toLp d‖ ^ 2 = ∫ s in Icc a b, ‖d s‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hLp.coeFn_toLp] with s hs
    rw [hs, real_inner_self_eq_norm_sq]
  rw [hnorm]
  calc
    _ ≤ ∫ s in Icc a b, c⁻¹ * M14.pathSquareKinetic p s :=
      integral_mono_ae hd2 (hq.const_mul c⁻¹) hpoint
    _ = c⁻¹ * ∫ s in a..b, M14.pathSquareKinetic p s := by
      rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab]
    _ ≤ c⁻¹ * D := mul_le_mul_of_nonneg_left
      ((intervalIntegral.integral_mono_interval ha hab hb
        (ae_of_all _ (pathSquareKinetic_nonneg p)) henergy).trans hbound) (inv_pos.mpr hc).le

omit x0 in



theorem squarePath_gauge_coordinates_regular {T tau : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T 0 tau x y) {U : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel 3) (spacetimeModel 3) ∞ lift U)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.sqrt tau)
    (hsrc : ∀ s ∈ Icc a b, p.curve (s ^ 2) ∈ U) :
    let u := fun s => (lift (p.curve (s ^ 2))).2.val
    ContinuousOn u (Icc a b) ∧ ∀ s ∈ Ioo a b, HasDerivAt u (deriv u s) s := by
  have hsub : Icc a b ⊆ M14SqrtParameterInterval 0 tau := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using Icc_subset_Icc ha hb
  have hsubo : Ioo a b ⊆ Ioo (Real.sqrt 0) (Real.sqrt tau) := by
    simpa only [Real.sqrt_zero] using Ioo_subset_Ioo ha hb
  have hL := hlift.continuousOn.comp ((M14.squarePath_continuousOn p).mono hsub) hsrc
  refine ⟨continuous_subtype_val.comp_continuousOn hL.snd, ?_⟩
  have hLreg := (hlift.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp
    ((M14.squarePath_contMDiffOn p).mono hsubo) (fun s hs => hsrc s (Ioo_subset_Icc_self hs))
  have hu : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1
      (fun s => (lift (p.curve (s ^ 2))).2) (Ioo a b) := fun s hs => (hLreg s hs).snd
  have hval : ContMDiff (𝓡 3) (𝓡 3) 1
      (Subtype.val : G.gaugeCover.spatial j → EuclideanSpace ℝ (Fin 3)) := contMDiff_subtype_val
  have hvreg := (hval.comp_contMDiffOn hu).contDiffOn
  intro s hs
  exact ((hvreg s hs).contDiffAt (isOpen_Ioo.mem_nhds hs)).differentiableAt
    (by simp) |>.hasDerivAt

end PoincareConjecture.Proofs.M46
