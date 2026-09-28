import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.Cone












noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X}

instance asymptoticCone_properSpace [ProperSpace X] (hcomparison : RayComparison p) :
    ProperSpace (AsymptoticCone p hcomparison) where
  isCompact_closedBall a r := by
    apply (isCompact_asymptoticConeRadius_sublevel hcomparison
      (asymptoticConeRadius hcomparison a + r.toNNReal)).of_isClosed_subset
      Metric.isClosed_closedBall
    intro b hb
    have hr := (lipschitzWith_asymptoticConeRadius hcomparison).dist_le_mul b a
    simp only [NNReal.coe_one, one_mul, NNReal.dist_eq] at hr
    have hb' : dist b a ≤ r := hb
    change asymptoticConeRadius hcomparison b ≤ asymptoticConeRadius hcomparison a + r.toNNReal
    rw [← NNReal.coe_le_coe, NNReal.coe_add]
    have hmax : r ≤ (r.toNNReal : ℝ) := Real.le_coe_toNNReal r
    linarith [le_abs_self ((asymptoticConeRadius hcomparison b : ℝ) -
      asymptoticConeRadius hcomparison a)]

theorem asymptoticCone_completeSpace [ProperSpace X] (hcomparison : RayComparison p) :
    CompleteSpace (AsymptoticCone p hcomparison) := inferInstance


def AsymptoticConeUnitSlice (p : X) (hcomparison : RayComparison p) :=
  {a : AsymptoticCone p hcomparison // asymptoticConeRadius hcomparison a = 1}

instance asymptoticConeUnitSlice_metricSpace (hcomparison : RayComparison p) :
    MetricSpace (AsymptoticConeUnitSlice p hcomparison) := inferInstanceAs
      (MetricSpace {a : AsymptoticCone p hcomparison // asymptoticConeRadius hcomparison a = 1})

def asymptoticConeUnitProjection (hcomparison : RayComparison p)
    (l : AsymptoticLink p hcomparison) : AsymptoticConeUnitSlice p hcomparison :=
  ⟨asymptoticConeProjection hcomparison (1, l), rfl⟩

theorem isometry_asymptoticConeUnitProjection (hcomparison : RayComparison p) :
    Isometry (asymptoticConeUnitProjection hcomparison) := by
  apply isometry_iff_dist_eq.mpr
  intro l k
  exact (isometry_asymptoticCone_unit_link hcomparison).dist_eq l k

theorem surjective_asymptoticConeUnitProjection (hcomparison : RayComparison p) :
    Function.Surjective (asymptoticConeUnitProjection hcomparison) := by
  rintro ⟨a, ha⟩
  obtain ⟨⟨r, l⟩, hr⟩ := surjective_asymptoticConeProjection hcomparison a
  have hrone : r = 1 := by
    have h := congrArg (asymptoticConeRadius hcomparison) hr
    simpa only [asymptoticConeRadius_projection, ha] using h
  subst r
  exact ⟨l, Subtype.ext hr⟩



def asymptoticConeUnitIsometry (hcomparison : RayComparison p) :
    AsymptoticLink p hcomparison ≃ᵢ AsymptoticConeUnitSlice p hcomparison :=
  { Equiv.ofBijective (asymptoticConeUnitProjection hcomparison)
      ⟨(isometry_asymptoticConeUnitProjection hcomparison).injective,
        surjective_asymptoticConeUnitProjection hcomparison⟩ with
    isometry_toFun := isometry_asymptoticConeUnitProjection hcomparison }

theorem asymptoticConeUnitIsometry_apply (hcomparison : RayComparison p)
    (l : AsymptoticLink p hcomparison) :
    asymptoticConeUnitIsometry hcomparison l = asymptoticConeUnitProjection hcomparison l := rfl

instance asymptoticConeUnitSlice_compactSpace [ProperSpace X] (hcomparison : RayComparison p) :
    CompactSpace (AsymptoticConeUnitSlice p hcomparison) :=
  (surjective_asymptoticConeUnitProjection hcomparison).compactSpace
    (isometry_asymptoticConeUnitProjection hcomparison).continuous

theorem isCompact_asymptoticCone_unit_slice [ProperSpace X] (hcomparison : RayComparison p) :
    IsCompact {a : AsymptoticCone p hcomparison | asymptoticConeRadius hcomparison a = 1} :=
  isCompact_iff_compactSpace.mpr (asymptoticConeUnitSlice_compactSpace hcomparison)

theorem nonempty_asymptoticConeUnitSlice (hcomparison : RayComparison p)
    (h : Nonempty (basedMinimizingRays p)) : Nonempty (AsymptoticConeUnitSlice p hcomparison) := by
  obtain ⟨γ⟩ := h
  exact ⟨asymptoticConeUnitProjection hcomparison (asymptoticLinkProjection hcomparison γ)⟩

theorem asymptoticConeDilation_one (hcomparison : RayComparison p)
    (a : AsymptoticCone p hcomparison) : asymptoticConeDilation hcomparison 1 a = a := by
  obtain ⟨⟨r, l⟩, rfl⟩ := surjective_asymptoticConeProjection hcomparison a
  simp only [asymptoticConeDilation_projection, one_mul]

theorem asymptoticConeDilation_mul (hcomparison : RayComparison p) (c d : ℝ≥0)
    (a : AsymptoticCone p hcomparison) :
    asymptoticConeDilation hcomparison c (asymptoticConeDilation hcomparison d a) =
      asymptoticConeDilation hcomparison (c * d) a := by
  obtain ⟨⟨r, l⟩, rfl⟩ := surjective_asymptoticConeProjection hcomparison a
  simp only [asymptoticConeDilation_projection, mul_assoc]

theorem dist_asymptoticConeDilation_same_point (hcomparison : RayComparison p) (c d : ℝ≥0)
    (a : AsymptoticCone p hcomparison) :
    dist (asymptoticConeDilation hcomparison c a) (asymptoticConeDilation hcomparison d a) =
      |(c : ℝ) - d| * asymptoticConeRadius hcomparison a := by
  obtain ⟨⟨r, l⟩, rfl⟩ := surjective_asymptoticConeProjection hcomparison a
  rw [asymptoticConeDilation_projection, asymptoticConeDilation_projection,
    dist_asymptoticConeProjection_same_link, asymptoticConeRadius_projection, NNReal.dist_eq]
  simp only [NNReal.coe_mul, ← sub_mul, abs_mul, abs_of_nonneg r.coe_nonneg]

theorem dist_asymptoticConeDilation_le (hcomparison : RayComparison p) (c d : ℝ≥0)
    (a b : AsymptoticCone p hcomparison) :
    dist (asymptoticConeDilation hcomparison c a) (asymptoticConeDilation hcomparison d b) ≤
      c * dist a b + |(c : ℝ) - d| * asymptoticConeRadius hcomparison b := by
  simpa only [dist_asymptoticConeDilation, dist_asymptoticConeDilation_same_point] using
    dist_triangle (asymptoticConeDilation hcomparison c a)
      (asymptoticConeDilation hcomparison c b) (asymptoticConeDilation hcomparison d b)



theorem continuous_asymptoticConeDilation (hcomparison : RayComparison p) :
    Continuous (fun q : ℝ≥0 × AsymptoticCone p hcomparison =>
      asymptoticConeDilation hcomparison q.1 q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound : Continuous (fun a : ℝ≥0 × AsymptoticCone p hcomparison =>
      (a.1 : ℝ) * dist a.2 q.2 + |(a.1 : ℝ) - q.1| * asymptoticConeRadius hcomparison q.2) := by
    fun_prop
  have hboundlim : Tendsto (fun a : ℝ≥0 × AsymptoticCone p hcomparison =>
      (a.1 : ℝ) * dist a.2 q.2 + |(a.1 : ℝ) - q.1| * asymptoticConeRadius hcomparison q.2)
      (𝓝 q) (𝓝 0) := by
    simpa only [dist_self, mul_zero, sub_self, abs_zero, zero_mul, add_zero] using hbound.tendsto q
  exact squeeze_zero
    (fun a : ℝ≥0 × AsymptoticCone p hcomparison =>
      show 0 ≤ dist (asymptoticConeDilation hcomparison a.1 a.2)
        (asymptoticConeDilation hcomparison q.1 q.2) from dist_nonneg)
    (fun a => dist_asymptoticConeDilation_le hcomparison a.1 q.1 a.2 q.2) hboundlim


abbrev AsymptoticConePositive (p : X) (hcomparison : RayComparison p) :=
  {a : AsymptoticCone p hcomparison // 0 < asymptoticConeRadius hcomparison a}

def asymptoticConePositiveProjection (hcomparison : RayComparison p)
    (a : Ioi (0 : ℝ≥0) × AsymptoticLink p hcomparison) : AsymptoticConePositive p hcomparison :=
  ⟨asymptoticConeProjection hcomparison (a.1.1, a.2), a.1.property⟩

theorem continuous_asymptoticConePositiveProjection (hcomparison : RayComparison p) :
    Continuous (asymptoticConePositiveProjection hcomparison) := by
  apply Continuous.subtype_mk
  exact (continuous_asymptoticConeProjection hcomparison).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)


def asymptoticConeNormalize (hcomparison : RayComparison p)
    (a : AsymptoticConePositive p hcomparison) : AsymptoticConeUnitSlice p hcomparison :=
  ⟨asymptoticConeDilation hcomparison (asymptoticConeRadius hcomparison a.1)⁻¹ a.1, by
    rw [asymptoticConeRadius_dilation]
    exact inv_mul_cancel₀ a.property.ne'⟩

theorem continuous_asymptoticConeNormalize (hcomparison : RayComparison p) :
    Continuous (asymptoticConeNormalize hcomparison) := by
  have hr : Continuous (fun a : AsymptoticConePositive p hcomparison =>
      asymptoticConeRadius hcomparison a.1) :=
    (lipschitzWith_asymptoticConeRadius hcomparison).continuous.comp continuous_subtype_val
  have hi : Continuous (fun a : AsymptoticConePositive p hcomparison =>
      (asymptoticConeRadius hcomparison a.1)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    exact hr.continuousAt.inv₀ a.property.ne'
  apply Continuous.subtype_mk
  exact (continuous_asymptoticConeDilation hcomparison).comp (hi.prodMk continuous_subtype_val)

theorem asymptoticConeNormalize_projection (hcomparison : RayComparison p)
    (r : Ioi (0 : ℝ≥0)) (l : AsymptoticLink p hcomparison) :
    asymptoticConeNormalize hcomparison (asymptoticConePositiveProjection hcomparison (r, l)) =
      asymptoticConeUnitProjection hcomparison l := by
  apply Subtype.ext
  change asymptoticConeDilation hcomparison
    (asymptoticConeRadius hcomparison (asymptoticConeProjection hcomparison (r.1, l)))⁻¹
      (asymptoticConeProjection hcomparison (r.1, l)) =
    asymptoticConeProjection hcomparison (1, l)
  rw [asymptoticConeRadius_projection, asymptoticConeDilation_projection,
    inv_mul_cancel₀ r.property.ne']



def asymptoticConeAngle (hcomparison : RayComparison p)
    (a : AsymptoticConePositive p hcomparison) : AsymptoticLink p hcomparison :=
  (asymptoticConeUnitIsometry hcomparison).symm (asymptoticConeNormalize hcomparison a)

theorem continuous_asymptoticConeAngle (hcomparison : RayComparison p) :
    Continuous (asymptoticConeAngle hcomparison) :=
  (asymptoticConeUnitIsometry hcomparison).symm.continuous.comp
    (continuous_asymptoticConeNormalize hcomparison)

theorem asymptoticConeAngle_projection (hcomparison : RayComparison p)
    (r : Ioi (0 : ℝ≥0)) (l : AsymptoticLink p hcomparison) :
    asymptoticConeAngle hcomparison (asymptoticConePositiveProjection hcomparison (r, l)) = l := by
  rw [asymptoticConeAngle, asymptoticConeNormalize_projection,
    ← asymptoticConeUnitIsometry_apply]
  exact (asymptoticConeUnitIsometry hcomparison).symm_apply_apply l

theorem asymptoticConePositiveProjection_radius_angle (hcomparison : RayComparison p)
    (a : AsymptoticConePositive p hcomparison) :
    asymptoticConePositiveProjection hcomparison
      (⟨asymptoticConeRadius hcomparison a.1, a.property⟩, asymptoticConeAngle hcomparison a) = a := by
  apply Subtype.ext
  have hunit : (asymptoticConeUnitProjection hcomparison (asymptoticConeAngle hcomparison a)).1 =
      (asymptoticConeNormalize hcomparison a).1 :=
    congrArg Subtype.val ((asymptoticConeUnitIsometry hcomparison).apply_symm_apply
      (asymptoticConeNormalize hcomparison a))
  change asymptoticConeProjection hcomparison
    (asymptoticConeRadius hcomparison a.1, asymptoticConeAngle hcomparison a) = a.1
  calc
    _ = asymptoticConeDilation hcomparison (asymptoticConeRadius hcomparison a.1)
        (asymptoticConeUnitProjection hcomparison (asymptoticConeAngle hcomparison a)).1 := by
      change _ = asymptoticConeDilation hcomparison _
        (asymptoticConeProjection hcomparison (1, _))
      rw [asymptoticConeDilation_projection, mul_one]
    _ = asymptoticConeDilation hcomparison (asymptoticConeRadius hcomparison a.1)
        (asymptoticConeNormalize hcomparison a).1 := congrArg _ hunit
    _ = a.1 := by
      change asymptoticConeDilation hcomparison (asymptoticConeRadius hcomparison a.1)
        (asymptoticConeDilation hcomparison (asymptoticConeRadius hcomparison a.1)⁻¹ a.1) = a.1
      rw [asymptoticConeDilation_mul, mul_inv_cancel₀ a.property.ne', asymptoticConeDilation_one]



def asymptoticConePositiveHomeomorph (hcomparison : RayComparison p) :
    (Ioi (0 : ℝ≥0) × AsymptoticLink p hcomparison) ≃ₜ AsymptoticConePositive p hcomparison where
  toFun := asymptoticConePositiveProjection hcomparison
  invFun := fun a => (⟨asymptoticConeRadius hcomparison a.1, a.property⟩,
    asymptoticConeAngle hcomparison a)
  left_inv := by
    rintro ⟨r, l⟩
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · exact asymptoticConeAngle_projection hcomparison r l
  right_inv := asymptoticConePositiveProjection_radius_angle hcomparison
  continuous_toFun := continuous_asymptoticConePositiveProjection hcomparison
  continuous_invFun :=
    (((lipschitzWith_asymptoticConeRadius hcomparison).continuous.comp continuous_subtype_val).subtype_mk
      (fun a => a.property)).prodMk (continuous_asymptoticConeAngle hcomparison)

end Poincare.AncientVolume.ScalarRatio
