import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_FirstExitCompletion










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T3Space M]

omit [T3Space M] in



theorem birthEnergy_integrable_of_action_bound (g : RiemannianMetric n M)
    {gamma : ℝ → M} {a b mu : ℝ} (hab : a ≤ b) (hmu : 0 < mu)
    (hregular : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma (Ioo a b))
    (density : ℝ → ℝ) (hint : IntervalIntegrable density volume a b)
    (hbound : ∀ t ∈ Ioo a b, mu * M08.referenceSpeedSq g gamma t ≤ density t) :
    IntervalIntegrable (M08.referenceSpeedSq g gamma) volume a b ∧
      mu * (∫ t in a..b, M08.referenceSpeedSq g gamma t) ≤ ∫ t in a..b, density t := by
  have hmeas : AEStronglyMeasurable (M08.referenceSpeedSq g gamma)
      (volume.restrict (uIoc a b)) := by
    rw [uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
    have hcont := M08.referenceSpeedSq_continuousOn g isOpen_Ioo hregular
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  have henergy : IntervalIntegrable (M08.referenceSpeedSq g gamma) volume a b := by
    apply (hint.const_mul mu⁻¹).mono_fun' hmeas
    rw [uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (M08.referenceSpeedSq_nonneg g gamma t)]
    have h := mul_le_mul_of_nonneg_left (hbound t ht) (inv_nonneg.mpr hmu.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hmu.ne', one_mul] using h
  refine ⟨henergy, ?_⟩
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hab (henergy.const_mul mu) hint hbound
  rwa [intervalIntegral.integral_const_mul] at h

omit [T3Space M] in


theorem half_radius_le_exit_edist (g : RiemannianMetric n M)
    {center x y : M} {R : ℝ} (hR : 0 < R)
    (hx : x ∈ g.ball center (R / 2)) (hy : y ∉ g.ball center R) :
    ENNReal.ofReal (R / 2) ≤ g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have houter : ENNReal.ofReal R ≤ g.edist center y := le_of_not_gt hy
  by_contra hnot
  have hinner : g.edist center x < ENNReal.ofReal (R / 2) := hx
  have hshort : g.edist x y < ENNReal.ofReal (R / 2) := lt_of_not_ge hnot
  have hsum : g.edist center x + g.edist x y < ENNReal.ofReal R := by
    have h := ENNReal.add_lt_add hinner hshort
    simpa only [← ENNReal.ofReal_add (p := R / 2) (q := R / 2)
      (by positivity) (by positivity),
      add_halves] using h
  exact (not_lt_of_ge houter) ((Manifold.riemannianEDist_triangle (I := 𝓡 n)
    (x := center) (y := x) (z := y)).trans_lt hsum)

private theorem capAction_lower_of_separation (g : RiemannianMetric n M)
    {gamma : ℝ → M} {a b mu A h : ℝ} (hab : a < b)
    (hmu : 0 < mu) (hA : 0 < A) (hh : 0 < h) (hduration : b - a ≤ h ^ 2)
    (hcont : ContinuousOn gamma (Icc a b))
    (hregular : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma (Ioo a b))
    (density : ℝ → ℝ) (hint : IntervalIntegrable density volume a b)
    (hbound : ∀ t ∈ Ioo a b, mu * M08.referenceSpeedSq g gamma t ≤ density t)
    (hsep : ENNReal.ofReal (A * h / 2) ≤ g.edist (gamma a) (gamma b)) :
    mu * A ^ 2 / 4 ≤ ∫ t in a..b, density t := by
  obtain ⟨henergy, haction⟩ :=
    birthEnergy_integrable_of_action_bound g hab.le hmu hregular density hint hbound
  have hdistance := sq_distance_le_duration_mul_energy g hab (by positivity)
    hcont hregular henergy hsep
  have hE : 0 ≤ ∫ t in a..b, M08.referenceSpeedSq g gamma t :=
    intervalIntegral.integral_nonneg hab.le (fun t _ => M08.referenceSpeedSq_nonneg g gamma t)
  have hscale : h ^ 2 * (mu * A ^ 2 / 4) ≤ h ^ 2 * ∫ t in a..b, density t := by
    calc
      _ = mu * (A * h / 2) ^ 2 := by ring
      _ ≤ mu * ((b - a) * ∫ t in a..b, M08.referenceSpeedSq g gamma t) :=
        mul_le_mul_of_nonneg_left hdistance hmu.le
      _ ≤ mu * (h ^ 2 * ∫ t in a..b, M08.referenceSpeedSq g gamma t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hduration hE) hmu.le
      _ = h ^ 2 * (mu * ∫ t in a..b, M08.referenceSpeedSq g gamma t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left haction (sq_nonneg h)
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hh)).mp hscale




theorem capSideAction_lower (g : RiemannianMetric n M)
    {gamma : ℝ → M} {a b mu A h : ℝ} (hab : a < b)
    (hmu : 0 < mu) (hA : 0 < A) (hh : 0 < h) (hduration : b - a ≤ h ^ 2)
    (hcont : ContinuousOn gamma (Icc a b))
    (hregular : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma (Ioo a b))
    (density : ℝ → ℝ) (hint : IntervalIntegrable density volume a b)
    (hbound : ∀ t ∈ Ioo a b, mu * M08.referenceSpeedSq g gamma t ≤ density t)
    (center : M) (hinner : gamma a ∈ g.ball center (A * h / 2))
    (houter : gamma b ∉ g.ball center (A * h)) :
    mu * A ^ 2 / 4 ≤ ∫ t in a..b, density t :=
  capAction_lower_of_separation g hab hmu hA hh hduration hcont hregular density hint
    hbound (half_radius_le_exit_edist g (mul_pos hA hh) hinner houter)




theorem capEntryAction_lower (g : RiemannianMetric n M)
    {gamma : ℝ → M} {a b mu A h : ℝ} (hab : a < b)
    (hmu : 0 < mu) (hA : 0 < A) (hh : 0 < h) (hduration : b - a ≤ h ^ 2)
    (hcont : ContinuousOn gamma (Icc a b))
    (hregular : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma (Ioo a b))
    (density : ℝ → ℝ) (hint : IntervalIntegrable density volume a b)
    (hbound : ∀ t ∈ Ioo a b, mu * M08.referenceSpeedSq g gamma t ≤ density t)
    (center : M) (hinner : gamma b ∈ g.ball center (A * h / 2))
    (houter : gamma a ∉ g.ball center (A * h)) :
    mu * A ^ 2 / 4 ≤ ∫ t in a..b, density t := by
  apply capAction_lower_of_separation g hab hmu hA hh hduration hcont hregular density
    hint hbound
  have hsep := half_radius_le_exit_edist g (mul_pos hA hh) hinner houter
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcomm : g.edist (gamma b) (gamma a) = g.edist (gamma a) (gamma b) :=
    Manifold.riemannianEDist_comm
  rwa [hcomm] at hsep

end PoincareConjecture.Proofs.M46
