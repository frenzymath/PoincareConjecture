import PoincareConjecture.Proofs.M36.RadialDifferential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.Compact











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open MeasureTheory

namespace PoincareConjecture.M36

theorem radialArclength_le_pathELength (g₀ : StandardInitialMetric)
    {gamma : ℝ → StandardCapSpace}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma) (hzero : gamma 0 = 0) :
    ENNReal.ofReal (radialArclength g₀ ‖gamma 1‖) ≤
      g₀.metric.pathELength gamma 0 1 := by
  let Z : Set ℝ := Set.Icc 0 1 ∩ gamma ⁻¹' {0}
  have hcompact : IsCompact Z :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hgamma.continuous)
  have hZ : Z.Nonempty := ⟨0, ⟨⟨le_rfl, zero_le_one⟩, hzero⟩⟩
  obtain ⟨a, ha, hmax⟩ := hcompact.exists_isGreatest hZ
  have ha0 : 0 ≤ a := ha.1.1
  have ha1 : a ≤ 1 := ha.1.2
  have hga : gamma a = 0 := ha.2
  have haway : ∀ t ∈ Set.Ioo a 1, gamma t ≠ 0 := by
    intro t ht heq
    have hta : t ≤ a := hmax ⟨⟨ha0.trans ht.1.le, ht.2.le⟩, heq⟩
    exact (not_lt_of_ge hta) ht.1
  have hdiff : Differentiable ℝ gamma := hgamma.contDiff.differentiable one_ne_zero
  have hbound := norm_sub_le_integral_of_norm_deriv_le_of_le ha1
    (((radialArclength_contDiff g₀).continuous.comp hgamma.continuous.norm).continuousOn)
    (show DifferentiableOn ℝ (fun t => radialArclength g₀ ‖gamma t‖)
        (Set.Ioo a 1) from fun t ht =>
      (radial_path_hasDerivAt g₀ (hdiff t).hasDerivAt (haway t ht)).differentiableAt
        |>.differentiableWithinAt)
    (Filter.Eventually.of_forall fun t ht =>
      radial_path_deriv_bound g₀ (hdiff t) (haway t ht))
    ((metricPathSpeed_continuous g₀.metric hgamma).intervalIntegrable a 1)
  have hnonneg : 0 ≤ radialArclength g₀ ‖gamma 1‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g₀).monotone (norm_nonneg (gamma 1))
  simp only [Function.comp_apply, hga, norm_zero, radialArclength_zero, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg hnonneg] at hbound
  calc
    _ ≤ ENNReal.ofReal (∫ t in a..1, metricPathSpeed g₀.metric gamma t) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = g₀.metric.pathELength gamma a 1 :=
      (pathELength_eq_integral_speed g₀.metric hgamma ha1).symm
    _ ≤ g₀.metric.pathELength gamma 0 1 := by
      let : Bundle.RiemannianBundle
          (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
        ⟨g₀.metric.toRiemannianMetric⟩
      exact Manifold.pathELength_mono ha0 le_rfl

theorem radialArclength_le_edist (g₀ : StandardInitialMetric) (x : StandardCapSpace) :
    ENNReal.ofReal (radialArclength g₀ ‖x‖) ≤ g₀.metric.edist 0 x := by
  by_contra h
  have hlt := lt_of_not_ge h
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g₀.metric.toRiemannianMetric⟩
  obtain ⟨gamma, hzero, hx, hgamma, hlen, _, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hlt zero_lt_one
  have hlow := radialArclength_le_pathELength g₀ hgamma hzero
  rw [hx] at hlow
  exact (not_lt_of_ge hlow) hlen

theorem unit_ray_metric (g₀ : StandardInitialMetric)
    (u : StandardCapSpace) (hu : ‖u‖ = 1) (t : ℝ) :
    g₀.metric.inner (t • u) u u = axisRadialCoefficient g₀ t := by
  obtain ⟨L, hdet, hLu⟩ := exists_axis_isometry u hu
  have hp : L (axisPoint t) = t • u := by rw [axisPoint_eq_smul, map_smul, hLu]
  have h := standardInitialMetric_isometry_inner g₀ L hdet
    (axisPoint t) (axisBasis 0) (axisBasis 0)
  rw [hp, hLu] at h
  exact h

theorem metricPathSpeed_unit_ray (g₀ : StandardInitialMetric)
    (u : StandardCapSpace) (hu : ‖u‖ = 1) (t : ℝ) :
    metricPathSpeed g₀.metric (fun s : ℝ => s • u) t = radialSpeed g₀ t := by
  have hd : HasDerivAt (fun s : ℝ => s • u) u t := by
    convert! (hasDerivAt_id t).smul_const u using 1
    simp
  have hm : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s : ℝ => s • u) t 1 = u := by
    rw [mfderiv_eq_fderiv]
    exact hd.deriv
  unfold metricPathSpeed RiemannianMetric.tangentNorm
  rw [hm, unit_ray_metric g₀ u hu]
  rfl

theorem edist_le_radialArclength (g₀ : StandardInitialMetric) (x : StandardCapSpace) :
    g₀.metric.edist 0 x ≤ ENNReal.ofReal (radialArclength g₀ ‖x‖) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g₀.metric.toRiemannianMetric⟩
  by_cases hx : x = 0
  · subst x
    change Manifold.riemannianEDist (𝓡 3) 0 0 ≤ _
    rw [Manifold.riemannianEDist_self]
    exact bot_le
  let u : StandardCapSpace := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, norm_ne_zero_iff.mpr hx]
  have hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (fun t : ℝ => t • u) :=
    (contDiff_id.smul contDiff_const).contMDiff
  have hxend : ‖x‖ • u = x := by simp [u, smul_smul, norm_ne_zero_iff.mpr hx]
  have hle : g₀.metric.edist 0 x ≤
      g₀.metric.pathELength (fun t : ℝ => t • u) 0 ‖x‖ :=
    Manifold.riemannianEDist_le_pathELength hgamma.contMDiffOn
      (zero_smul ℝ u) hxend (norm_nonneg x)
  apply hle.trans_eq
  rw [pathELength_eq_integral_speed g₀.metric hgamma (norm_nonneg x)]
  simp_rw [metricPathSpeed_unit_ray g₀ u hu]
  rfl

theorem standard_edist_zero (g₀ : StandardInitialMetric) (x : StandardCapSpace) :
    g₀.metric.edist 0 x = ENNReal.ofReal (radialArclength g₀ ‖x‖) :=
  le_antisymm (edist_le_radialArclength g₀ x) (radialArclength_le_edist g₀ x)

end PoincareConjecture.M36
