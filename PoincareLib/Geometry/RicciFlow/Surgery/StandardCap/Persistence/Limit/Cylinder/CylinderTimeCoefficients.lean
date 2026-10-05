import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Cylinder.CylinderSlabCoefficients

/-!
# Actual cylinder coefficients in physical time

The physical-time coefficient field has no normalization factor.
A fixed included slice supplies harmless values outside the time
domain. Morgan--Tian, Lemma 16.8, pp. 372-373;
see M44 derivation 62.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

/-- Actual unnormalized cylinder coefficients in physical time.
Source: Lemma 16.8, pp. 372-373; M44 derivation 62. -/
noncomputable def cylinderTimeCoefficients
    (e : SurgeryFlowCylinder F C origin scale I U) (f : E → C.carrier)
    (r : ℝ) (hr : r ∈ I) (p : ℝ × E) : E →L[ℝ] E →L[ℝ] ℝ := by
  classical
  exact if hs : scale * (p.1 - origin) ∈ I then
    cylinderPhysicalCoefficients e f (scale * (p.1 - origin)) hs p.2
  else cylinderPhysicalCoefficients e f r hr p.2

/-- Conversion from physical time back to cylinder time is
exact for every positive cylinder scale. Source: Lemma 16.8;
M44 derivation 62. -/
theorem cylinder_clock_parameter
    (e : SurgeryFlowCylinder F C origin scale I U) (t : ℝ) :
    origin + (scale * (t - origin)) / scale = t := by
  field_simp [ne_of_gt e.scale_pos]
  ring

/-- The affine clock identifies the half-open parameter and
physical time intervals exactly. Source: Lemma 16.8;
M44 derivation 62. -/
theorem cylinder_parameter_mem_ico
    (e : SurgeryFlowCylinder F C origin scale I U) (B t : ℝ) :
    scale * (t - origin) ∈ Ico 0 B ↔ t ∈ Ico origin (origin + B / scale) := by
  have hclock := cylinder_clock_parameter e t
  constructor
  · intro h
    exact ⟨by linarith [div_nonneg h.1 e.scale_pos.le],
      by linarith [(div_lt_div_iff_of_pos_right e.scale_pos).mpr h.2]⟩
  · intro h
    refine ⟨mul_nonneg e.scale_pos.le (sub_nonneg.mpr h.1), ?_⟩
    apply (div_lt_div_iff_of_pos_right e.scale_pos).mp
    linarith [h.2]

/-- Included physical times of the cylinder belong to the
actual surgery-flow time domain. Source: Proposition 16.5;
M44 derivation 62. -/
theorem cylinder_parameter_time_mem
    (e : SurgeryFlowCylinder F C origin scale I U) {t : ℝ}
    (ht : scale * (t - origin) ∈ I) : t ∈ F.time_domain := by
  have h := e.time_subset (mem_image_of_mem (fun s => origin + s / scale) ht)
  rwa [cylinder_clock_parameter e] at h

/-- The physical coefficient field at an included cylinder time
is exactly the original actual pullback. Source: Lemma 16.8;
M44 derivation 62. -/
theorem cylinderTimeCoefficients_at
    (e : SurgeryFlowCylinder F C origin scale I U) (f : E → C.carrier)
    (r : ℝ) (hr : r ∈ I) (s : ℝ) (hs : s ∈ I) (x : E) :
    cylinderTimeCoefficients e f r hr (origin + s / scale, x) =
      cylinderPhysicalCoefficients e f s hs x := by
  have heq : scale * (origin + s / scale - origin) = s := by
    field_simp [ne_of_gt e.scale_pos]
    ring
  have hs' : scale * (origin + s / scale - origin) ∈ I := by rwa [heq]
  simp only [cylinderTimeCoefficients, dif_pos hs']
  simp only [heq]

/-- Every physical-time slice is smooth on the fixed source,
also for the chosen off-interval values. Source: Lemma 16.8;
M44 derivation 62. -/
theorem cylinderTimeCoefficients_spatial_smooth
    (e : SurgeryFlowCylinder F C origin scale I U)
    {f : E → C.carrier} {V : Set E} (hV : IsOpen V)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V) (hmap : MapsTo f V U)
    (r : ℝ) (hr : r ∈ I) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun x => cylinderTimeCoefficients e f r hr (t, x)) V := by
  by_cases hs : scale * (t - origin) ∈ I
  · simpa only [cylinderTimeCoefficients, dif_pos hs] using
      cylinderPhysicalCoefficients_smooth e hV hf hmap _ hs
  · simpa only [cylinderTimeCoefficients, dif_neg hs] using
      cylinderPhysicalCoefficients_smooth e hV hf hmap r hr

/-- Metric symmetry holds for the full physical-time family.
Source: Lemma 16.8; M44 derivation 62. -/
theorem cylinderTimeCoefficients_symm
    (e : SurgeryFlowCylinder F C origin scale I U) (f : E → C.carrier)
    (r : ℝ) (hr : r ∈ I) (t : ℝ) (x v w : E) :
    cylinderTimeCoefficients e f r hr (t, x) v w =
      cylinderTimeCoefficients e f r hr (t, x) w v := by
  unfold cylinderTimeCoefficients
  split_ifs
  all_goals exact cylinderPhysicalCoefficients_symm e f _ _ x v w

/-- A birth chart with target in the tracked region gives a
positive physical-time coefficient family. Source: Lemma 16.8;
M44 derivation 62. -/
theorem cylinderTimeCoefficients_pos
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞)
    (hmap : f.target ⊆ U) (r : ℝ) (hr : r ∈ I) (t : ℝ)
    {x : E} (hx : x ∈ f.source) (v : E) (hv : v ≠ 0) :
    0 < cylinderTimeCoefficients e f r hr (t, x) v v := by
  unfold cylinderTimeCoefficients
  split_ifs
  all_goals exact cylinderPhysicalCoefficients_pos e hU f hmap _ _ hx v hv

/-- On an ordinary slab the physical-time coefficient is the
actual ordinary flow in one fixed reference chart. Source:
Lemma 16.8, pp. 372-373; M44 derivation 62. -/
theorem cylinderTimeCoefficients_eq_slab
    (e : SurgeryFlowCylinder F C origin scale I U)
    {f : E → C.carrier} {V : Set E} (hV : IsOpen V)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V) (hmap : MapsTo f V U)
    (r0 : ℝ) (hr0 : r0 ∈ I)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ F.time_domain)
    (hNo : Disjoint F.surgery_times (Ioc a b))
    (r : ℝ) (hr : r ∈ I) (hr' : origin + r / scale ∈ Icc a b)
    {t : ℝ} (ht : scale * (t - origin) ∈ I) (ht' : t ∈ Icc a b)
    {x : E} (hx : x ∈ V) :
    cylinderTimeCoefficients e f r0 hr0 (t, x) =
      ((F.regular_slabs a b hab hJ hNo).flow.metric t).pullbackCoefficients
        (((F.regular_slabs a b hab hJ hNo).identify ⟨origin + r / scale, hr'⟩).symm ∘
          e.forward r hr ∘ f) x := by
  have htclock : origin + (scale * (t - origin)) / scale ∈ Icc a b := by
    rwa [cylinder_clock_parameter e]
  simpa only [cylinderTimeCoefficients, dif_pos ht, cylinder_clock_parameter e]
    using cylinderPhysicalCoefficients_eq_slab e hV hf hmap hab hJ hNo
      r hr hr' _ ht htclock hx

end PoincareMT.M44
