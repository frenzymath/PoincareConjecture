import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.Link












noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X}



theorem tendsto_rescaled_ray_distance_cosine (hcomparison : RayComparison p)
    (γ η : basedMinimizingRays p) (r s : ℝ≥0) :
    Tendsto (fun L : ℝ => dist (rayExtension γ (r * L)) (rayExtension η (s * L)) / L)
      atTop (𝓝 (Real.sqrt (((r : ℝ) - s) ^ 2 + r * s * asymptoticRayDistance γ η ^ 2))) := by
  by_cases hr : r = 0
  · subst r
    have heq : (fun L : ℝ =>
        dist (rayExtension γ ((0 : ℝ≥0) * L)) (rayExtension η (s * L)) / L) =ᶠ[atTop]
        fun _ => (s : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      simp only [NNReal.coe_zero, zero_mul, rayExtension_zero]
      have hd := rayExtension_dist η le_rfl (mul_nonneg s.coe_nonneg hL.le)
      rw [rayExtension_zero, zero_sub, abs_neg,
        abs_of_nonneg (mul_nonneg s.coe_nonneg hL.le)] at hd
      rw [hd]
      exact mul_div_cancel_right₀ (s : ℝ) hL.ne'
    simpa only [NNReal.coe_zero, zero_sub, neg_sq, zero_mul, add_zero,
      Real.sqrt_sq s.coe_nonneg] using (tendsto_const_nhds.congr' heq.symm)
  by_cases hs : s = 0
  · subst s
    have heq : (fun L : ℝ =>
        dist (rayExtension γ (r * L)) (rayExtension η ((0 : ℝ≥0) * L)) / L) =ᶠ[atTop]
        fun _ => (r : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      simp only [NNReal.coe_zero, zero_mul, rayExtension_zero]
      have hd := rayExtension_dist γ (mul_nonneg r.coe_nonneg hL.le) le_rfl
      rw [rayExtension_zero, sub_zero, abs_of_nonneg (mul_nonneg r.coe_nonneg hL.le)] at hd
      rw [hd]
      exact mul_div_cancel_right₀ (r : ℝ) hL.ne'
    simpa only [NNReal.coe_zero, sub_zero, mul_zero, zero_mul, add_zero,
      Real.sqrt_sq r.coe_nonneg] using (tendsto_const_nhds.congr' heq.symm)
  obtain ⟨q, hq, hlim⟩ := exists_homogeneous_ray_distance_limit
    (rayExtension γ) (rayExtension η)
    ((rayExtension_zero γ).trans (rayExtension_zero η).symm)
    (fun a ha b hb => rayExtension_dist γ ha hb)
    (fun a ha b hb => rayExtension_dist η ha hb) (hcomparison γ η)
  have hunit := (hlim 1 1 zero_lt_one zero_lt_one).2
  simp only [one_mul, mul_one, one_pow] at hunit
  have hD : asymptoticRayDistance γ η = Real.sqrt (1 + 1 - 2 * q) :=
    tendsto_nhds_unique (tendsto_asymptoticRayDistance hcomparison γ η) hunit
  have hDsq : asymptoticRayDistance γ η ^ 2 = 2 - 2 * q := by
    rw [hD, Real.sq_sqrt (by linarith [hq.2])]
    ring
  have hformula : ((r : ℝ) - s) ^ 2 + r * s * asymptoticRayDistance γ η ^ 2 =
      (r : ℝ) ^ 2 + (s : ℝ) ^ 2 - 2 * r * s * q := by rw [hDsq]; ring
  rw [hformula]
  exact (hlim r s (by exact_mod_cast (pos_iff_ne_zero.mpr hr))
    (by exact_mod_cast (pos_iff_ne_zero.mpr hs))).2


def conePairDistance (hcomparison : RayComparison p)
    (a b : ℝ≥0 × AsymptoticLink p hcomparison) : ℝ :=
  Real.sqrt (((a.1 : ℝ) - b.1) ^ 2 + a.1 * b.1 * dist a.2 b.2 ^ 2)

theorem conePairDistance_self (hcomparison : RayComparison p)
    (a : ℝ≥0 × AsymptoticLink p hcomparison) : conePairDistance hcomparison a a = 0 := by
  simp [conePairDistance]

theorem conePairDistance_comm (hcomparison : RayComparison p)
    (a b : ℝ≥0 × AsymptoticLink p hcomparison) :
    conePairDistance hcomparison a b = conePairDistance hcomparison b a := by
  unfold conePairDistance
  rw [dist_comm a.2 b.2]
  congr 1
  ring

theorem tendsto_conePairDistance (hcomparison : RayComparison p)
    (γ η : basedMinimizingRays p) (r s : ℝ≥0) :
    Tendsto (fun L : ℝ => dist (rayExtension γ (r * L)) (rayExtension η (s * L)) / L)
      atTop (𝓝 (conePairDistance hcomparison
        (r, asymptoticLinkProjection hcomparison γ) (s, asymptoticLinkProjection hcomparison η))) := by
  simpa only [conePairDistance, dist_asymptoticLinkProjection] using
    tendsto_rescaled_ray_distance_cosine hcomparison γ η r s


theorem conePairDistance_triangle (hcomparison : RayComparison p)
    (a b c : ℝ≥0 × AsymptoticLink p hcomparison) :
    conePairDistance hcomparison a c ≤
      conePairDistance hcomparison a b + conePairDistance hcomparison b c := by
  obtain ⟨γ, hγ⟩ := surjective_asymptoticLinkProjection hcomparison a.2
  obtain ⟨η, hη⟩ := surjective_asymptoticLinkProjection hcomparison b.2
  obtain ⟨ζ, hζ⟩ := surjective_asymptoticLinkProjection hcomparison c.2
  have hab := tendsto_conePairDistance hcomparison γ η a.1 b.1
  have hbc := tendsto_conePairDistance hcomparison η ζ b.1 c.1
  have hac := tendsto_conePairDistance hcomparison γ ζ a.1 c.1
  simp only [hγ, hη, hζ, Prod.mk.eta] at hab hbc hac
  apply le_of_tendsto_of_tendsto hac (hab.add hbc)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [← add_div]
  exact div_le_div_of_nonneg_right (dist_triangle _ _ _) hL.le

theorem abs_sub_le_conePairDistance (hcomparison : RayComparison p)
    (a b : ℝ≥0 × AsymptoticLink p hcomparison) :
    |(a.1 : ℝ) - b.1| ≤ conePairDistance hcomparison a b := by
  rw [conePairDistance, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg a.1.coe_nonneg b.1.coe_nonneg)
    (sq_nonneg _))


@[instance_reducible] def conePairPseudoMetric (hcomparison : RayComparison p) :
    PseudoMetricSpace (ℝ≥0 × AsymptoticLink p hcomparison) where
  dist := conePairDistance hcomparison
  dist_self := conePairDistance_self hcomparison
  dist_comm := conePairDistance_comm hcomparison
  dist_triangle := conePairDistance_triangle hcomparison


def AsymptoticCone (p : X) (hcomparison : RayComparison p) :=
  @SeparationQuotient (ℝ≥0 × AsymptoticLink p hcomparison)
    (conePairPseudoMetric hcomparison).toUniformSpace.toTopologicalSpace

instance asymptoticCone_metricSpace (hcomparison : RayComparison p) :
    MetricSpace (AsymptoticCone p hcomparison) := by
  letI := conePairPseudoMetric hcomparison
  exact SeparationQuotient.instMetricSpace

def asymptoticConeProjection (hcomparison : RayComparison p)
    (a : ℝ≥0 × AsymptoticLink p hcomparison) : AsymptoticCone p hcomparison :=
  @SeparationQuotient.mk (ℝ≥0 × AsymptoticLink p hcomparison)
    (conePairPseudoMetric hcomparison).toUniformSpace.toTopologicalSpace a

theorem dist_asymptoticConeProjection (hcomparison : RayComparison p)
    (a b : ℝ≥0 × AsymptoticLink p hcomparison) :
    dist (asymptoticConeProjection hcomparison a) (asymptoticConeProjection hcomparison b) =
      Real.sqrt (((a.1 : ℝ) - b.1) ^ 2 + a.1 * b.1 * dist a.2 b.2 ^ 2) := by
  let := conePairPseudoMetric hcomparison
  exact SeparationQuotient.dist_mk a b

theorem surjective_asymptoticConeProjection (hcomparison : RayComparison p) :
    Function.Surjective (asymptoticConeProjection hcomparison) := by
  exact @SeparationQuotient.surjective_mk (ℝ≥0 × AsymptoticLink p hcomparison)
    (conePairPseudoMetric hcomparison).toUniformSpace.toTopologicalSpace


def asymptoticConeRadius (hcomparison : RayComparison p) :
    AsymptoticCone p hcomparison → ℝ≥0 := by
  exact @SeparationQuotient.lift (ℝ≥0 × AsymptoticLink p hcomparison) ℝ≥0
    (conePairPseudoMetric hcomparison).toUniformSpace.toTopologicalSpace Prod.fst (fun a b hab => by
    apply NNReal.coe_injective
    apply sub_eq_zero.mp
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    exact (abs_sub_le_conePairDistance hcomparison a b).trans_eq
      (@Inseparable.dist_eq_zero _ (conePairPseudoMetric hcomparison) a b hab))

theorem asymptoticConeRadius_projection (hcomparison : RayComparison p)
    (a : ℝ≥0 × AsymptoticLink p hcomparison) :
    asymptoticConeRadius hcomparison (asymptoticConeProjection hcomparison a) = a.1 := rfl

theorem lipschitzWith_asymptoticConeRadius (hcomparison : RayComparison p) :
    LipschitzWith 1 (asymptoticConeRadius hcomparison) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  obtain ⟨a, rfl⟩ := surjective_asymptoticConeProjection hcomparison a
  obtain ⟨b, rfl⟩ := surjective_asymptoticConeProjection hcomparison b
  simpa only [asymptoticConeRadius_projection, NNReal.dist_eq, NNReal.coe_one, one_mul,
    dist_asymptoticConeProjection, conePairDistance] using
    abs_sub_le_conePairDistance hcomparison a b

theorem conePairDistance_mul (hcomparison : RayComparison p) (c : ℝ≥0)
    (a b : ℝ≥0 × AsymptoticLink p hcomparison) :
    conePairDistance hcomparison (c * a.1, a.2) (c * b.1, b.2) =
      c * conePairDistance hcomparison a b := by
  unfold conePairDistance
  calc
    _ = Real.sqrt ((c : ℝ) ^ 2 *
        (((a.1 : ℝ) - b.1) ^ 2 + a.1 * b.1 * dist a.2 b.2 ^ 2)) := by
      congr 1
      push_cast
      ring
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq c.coe_nonneg]


def asymptoticConeDilation (hcomparison : RayComparison p) (c : ℝ≥0) :
    AsymptoticCone p hcomparison → AsymptoticCone p hcomparison := by
  exact @SeparationQuotient.lift (ℝ≥0 × AsymptoticLink p hcomparison)
    (AsymptoticCone p hcomparison)
    (conePairPseudoMetric hcomparison).toUniformSpace.toTopologicalSpace
    (fun a => asymptoticConeProjection hcomparison (c * a.1, a.2)) (fun a b hab => by
      apply dist_eq_zero.mp
      change conePairDistance hcomparison (c * a.1, a.2) (c * b.1, b.2) = 0
      rw [conePairDistance_mul]
      rw [show conePairDistance hcomparison a b = 0 from
        @Inseparable.dist_eq_zero _ (conePairPseudoMetric hcomparison) a b hab, mul_zero])

theorem asymptoticConeDilation_projection (hcomparison : RayComparison p) (c : ℝ≥0)
    (a : ℝ≥0 × AsymptoticLink p hcomparison) :
    asymptoticConeDilation hcomparison c (asymptoticConeProjection hcomparison a) =
      asymptoticConeProjection hcomparison (c * a.1, a.2) := rfl

theorem dist_asymptoticConeDilation (hcomparison : RayComparison p) (c : ℝ≥0)
    (a b : AsymptoticCone p hcomparison) :
    dist (asymptoticConeDilation hcomparison c a) (asymptoticConeDilation hcomparison c b) =
      c * dist a b := by
  obtain ⟨a, rfl⟩ := surjective_asymptoticConeProjection hcomparison a
  obtain ⟨b, rfl⟩ := surjective_asymptoticConeProjection hcomparison b
  exact conePairDistance_mul hcomparison c a b

theorem asymptoticConeRadius_dilation (hcomparison : RayComparison p) (c : ℝ≥0)
    (a : AsymptoticCone p hcomparison) :
    asymptoticConeRadius hcomparison (asymptoticConeDilation hcomparison c a) =
      c * asymptoticConeRadius hcomparison a := by
  obtain ⟨a, rfl⟩ := surjective_asymptoticConeProjection hcomparison a
  rfl


theorem tendsto_dist_asymptoticConeProjection (hcomparison : RayComparison p)
    (γ η : basedMinimizingRays p) (r s : ℝ≥0) :
    Tendsto (fun L : ℝ => dist (rayExtension γ (r * L)) (rayExtension η (s * L)) / L)
      atTop (𝓝 (dist
        (asymptoticConeProjection hcomparison (r, asymptoticLinkProjection hcomparison γ))
        (asymptoticConeProjection hcomparison (s, asymptoticLinkProjection hcomparison η)))) := by
  rw [dist_asymptoticConeProjection, dist_asymptoticLinkProjection]
  exact tendsto_rescaled_ray_distance_cosine hcomparison γ η r s

theorem dist_asymptoticConeProjection_zero (hcomparison : RayComparison p)
    (r : ℝ≥0) (l k : AsymptoticLink p hcomparison) :
    dist (asymptoticConeProjection hcomparison (r, l))
      (asymptoticConeProjection hcomparison (0, k)) = r := by
  rw [dist_asymptoticConeProjection]
  simp only [NNReal.coe_zero, sub_zero, mul_zero, zero_mul, add_zero,
    Real.sqrt_sq r.coe_nonneg]

theorem asymptoticConeProjection_zero_eq (hcomparison : RayComparison p)
    (l k : AsymptoticLink p hcomparison) :
    asymptoticConeProjection hcomparison (0, l) =
      asymptoticConeProjection hcomparison (0, k) := by
  apply dist_eq_zero.mp
  exact dist_asymptoticConeProjection_zero hcomparison 0 l k

theorem dist_asymptoticConeProjection_same_link (hcomparison : RayComparison p)
    (r s : ℝ≥0) (l : AsymptoticLink p hcomparison) :
    dist (asymptoticConeProjection hcomparison (r, l))
      (asymptoticConeProjection hcomparison (s, l)) = dist r s := by
  rw [dist_asymptoticConeProjection]
  simp [Real.sqrt_sq_eq_abs, NNReal.dist_eq]


theorem isometry_asymptoticCone_unit_link (hcomparison : RayComparison p) :
    Isometry (fun l : AsymptoticLink p hcomparison => asymptoticConeProjection hcomparison (1, l)) := by
  apply isometry_iff_dist_eq.mpr
  intro l k
  rw [dist_asymptoticConeProjection]
  simp [Real.sqrt_sq, dist_nonneg]


theorem continuous_asymptoticConeProjection (hcomparison : RayComparison p) :
    Continuous (asymptoticConeProjection hcomparison) := by
  apply continuous_iff_continuous_dist.mpr
  simp only [dist_asymptoticConeProjection]
  fun_prop


theorem isCompact_asymptoticConeProjection_radial_interval [ProperSpace X]
    (hcomparison : RayComparison p) (R : ℝ≥0) :
    IsCompact (asymptoticConeProjection hcomparison ''
      (Icc (0 : ℝ≥0) R ×ˢ (univ : Set (AsymptoticLink p hcomparison)))) :=
  (isCompact_Icc.prod isCompact_univ).image (continuous_asymptoticConeProjection hcomparison)


theorem isCompact_asymptoticConeRadius_sublevel [ProperSpace X]
    (hcomparison : RayComparison p) (R : ℝ≥0) :
    IsCompact {a : AsymptoticCone p hcomparison | asymptoticConeRadius hcomparison a ≤ R} := by
  have heq : {a : AsymptoticCone p hcomparison | asymptoticConeRadius hcomparison a ≤ R} =
      asymptoticConeProjection hcomparison ''
        (Icc (0 : ℝ≥0) R ×ˢ (univ : Set (AsymptoticLink p hcomparison))) := by
    ext a
    constructor
    · intro ha
      obtain ⟨b, rfl⟩ := surjective_asymptoticConeProjection hcomparison a
      exact ⟨b, ⟨⟨zero_le, ha⟩, mem_univ _⟩, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact hb.1.2
  rw [heq]
  exact isCompact_asymptoticConeProjection_radial_interval hcomparison R

end Poincare.AncientVolume.ScalarRatio
