import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Neck.NeckCoordinates
/-!
# Compact regular support for the comparison map

Morgan--Tian Proposition 15.12, p. 365, uses the retained region and the
finite surgery collars of Claim 13.1, pp. 331-332. The closed positive
collars, pulled back through the actual limit identification, form a compact
regular set together with the retained region. This is the support needed
for the near-unit estimate in the 2026-09-18 SurgeryComparison repair contract.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.SurgeryComparison

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
  (E : SurgeryEventData g₀ K P slice metric T)

/-- A closed positive neck collar in the actual pre-surgery carrier.
Claim 13.1, pp. 331-332, and the SurgeryComparison repair contract use a cutoff strictly
inside the neck to keep the nonconstant part in the regular region. -/
def positiveNeckControl (i : Fin E.cap_count) (c : ℝ) :
    Set (slice E.tMinus).carrier :=
  E.limit_identify.inverse '' ((E.necks i).neck.coordinate_map ''
    (univ ×ˢ Icc 0 c))

/-- The finite compact regular control set for Proposition 15.12, p. 365,
with the central levels included as required by the SurgeryComparison repair contract. -/
def regularControl (c : Fin E.cap_count → ℝ) :
    Set (slice E.tMinus).carrier :=
  E.retained_pre ∪ ⋃ i, positiveNeckControl E i (c i)

/-- Closed positive collars lie in the actual regular region. This uses
the inverse identification from Proposition 15.12, p. 365. -/
theorem positiveNeckControl_subset_regular (i : Fin E.cap_count) (c : ℝ) :
    positiveNeckControl E i c ⊆ E.regular_limit := by
  rintro x ⟨y, _, rfl⟩
  exact E.limit_identify.inverse_image.subset ⟨y, mem_univ y, rfl⟩

/-- A positive closed coordinate strip with upper endpoint strictly inside
the neck is compact after regular-limit transport. See Claim 13.1,
pp. 331-332, and the compact regular support in the SurgeryComparison repair contract. -/
theorem positiveNeckControl_compact (i : Fin E.cap_count) {c : ℝ}
    (hc : c < (E.necks i).neck.epsilon⁻¹) :
    IsCompact (positiveNeckControl E i c) := by
  have hdom : (univ ×ˢ Icc 0 c : Set (UnitTwoSphere × ℝ)) ⊆
      univ ×ˢ Ioo (-(E.necks i).neck.epsilon⁻¹) (E.necks i).neck.epsilon⁻¹ := by
    intro z hz
    refine ⟨hz.1, ?_, lt_of_le_of_lt hz.2.2 hc⟩
    have heps : 0 < (E.necks i).neck.epsilon⁻¹ :=
      inv_pos.mpr (E.necks i).neck.epsilon_pos
    linarith [hz.2.1]
  have hstrip : IsCompact ((E.necks i).neck.coordinate_map ''
      (univ ×ˢ Icc 0 c)) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      ((E.necks i).neck.coordinate_map_smooth.continuousOn.mono hdom)
  exact hstrip.image (continuousOn_univ.mp E.limit_identify.inverse_smooth.continuousOn)

/-- The actual coordinate inverse characterizes a closed control collar.
No value of the total forward limit map outside its regular domain is used.
This is the closed-strip support of Proposition 15.12, p. 365. -/
theorem mem_positiveNeckControl_iff (i : Fin E.cap_count) {c : ℝ}
    (hc : c < (E.necks i).neck.epsilon⁻¹) {x : (slice E.tMinus).carrier} :
    x ∈ positiveNeckControl E i c ↔
      x ∈ E.regular_limit ∧
      E.limit_identify.map x ∈ (E.necks i).neck.carrier ∧
      0 ≤ ((E.necks i).neck.coordinate_inverse (E.limit_identify.map x)).2 ∧
      ((E.necks i).neck.coordinate_inverse (E.limit_identify.map x)).2 ≤ c := by
  constructor
  · intro hx
    have hreg := positiveNeckControl_subset_regular E i c hx
    rcases hx with ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have hdom : z ∈ univ ×ˢ
        Ioo (-(E.necks i).neck.epsilon⁻¹) (E.necks i).neck.epsilon⁻¹ := by
      refine ⟨hz.1, ?_, lt_of_le_of_lt hz.2.2 hc⟩
      have heps : 0 < (E.necks i).neck.epsilon⁻¹ :=
        inv_pos.mpr (E.necks i).neck.epsilon_pos
      linarith [hz.2.1]
    rw [E.limit_identify.right_inverse (mem_univ _)]
    exact ⟨hreg, MetricSurgery.neck_coordinate_mem _ z hdom, by
      simpa only [MetricSurgery.neck_inverse_coordinate _ z hdom, mem_Icc] using hz.2⟩
  · rintro ⟨hreg, hneck, hzero, hc⟩
    refine ⟨E.limit_identify.map x, ?_, E.limit_identify.left_inverse hreg⟩
    exact ⟨(E.necks i).neck.coordinate_inverse (E.limit_identify.map x),
      ⟨mem_univ _, hzero, hc⟩, MetricSurgery.neck_coordinate_inverse _ hneck⟩

/-- The positive open neck region is covered by the corresponding closed
control strip. Proposition 15.12, p. 365, and Claim 13.1, p. 332. -/
theorem positiveNeckControl_contains_region (i : Fin E.cap_count) (c : ℝ) :
    E.limit_identify.inverse '' (E.necks i).neck.region 0 c ⊆
      positiveNeckControl E i c := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  exact ⟨(E.necks i).neck.coordinate_inverse y,
    ⟨mem_univ _, hy.2.1.le, hy.2.2.le⟩, MetricSurgery.neck_coordinate_inverse _ hy.1⟩

/-- The central level is included, including the endpoint zero. This is
the closed-cap boundary needed in Proposition 15.12, p. 365. -/
theorem positiveNeckControl_contains_central (i : Fin E.cap_count) {c : ℝ}
    (hc : 0 ≤ c) :
    E.limit_identify.inverse '' (E.necks i).neck.central_sphere ⊆
      positiveNeckControl E i c := by
  apply image_mono
  rw [(E.necks i).neck.central_sphere_eq]
  apply image_mono
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hz0 : z.2 = 0 := hz.2
  rw [hz0]
  exact ⟨le_rfl, hc⟩

/-- The retained set lies in the compact control set from Proposition
15.12, p. 365, for every choice of collar cutoffs. -/
theorem retained_pre_subset_regularControl (c : Fin E.cap_count → ℝ) :
    E.retained_pre ⊆ regularControl E c := subset_union_left

/-- Each individual collar lies in the finite control set of Proposition
15.12, p. 365. -/
theorem positiveNeckControl_subset_regularControl (c : Fin E.cap_count → ℝ)
    (i : Fin E.cap_count) :
    positiveNeckControl E i (c i) ⊆ regularControl E c := by
  intro x hx
  exact Or.inr (mem_iUnion.mpr ⟨i, hx⟩)

/-- The control set is compact since surgery uses finitely many collars.
Proposition 15.12, p. 365, and the SurgeryComparison repair contract's compact support. -/
theorem regularControl_compact (c : Fin E.cap_count → ℝ)
    (hc : ∀ i, c i < (E.necks i).neck.epsilon⁻¹) :
    IsCompact (regularControl E c) :=
  E.retained_pre_compact.union
    (isCompact_iUnion fun i => positiveNeckControl_compact E i (hc i))

/-- The finite control set remains entirely in the regular-limit region,
as required for the metric convergence used in Proposition 15.12, p. 365. -/
theorem regularControl_subset_regular (c : Fin E.cap_count → ℝ) :
    regularControl E c ⊆ E.regular_limit :=
  union_subset E.retained_pre_subset
    (iUnion_subset fun i => positiveNeckControl_subset_regular E i (c i))

/-- The positive part of each open collar is controlled. Proposition
15.12, p. 365, uses the static map of Claim 13.1, p. 332, there. -/
theorem regularControl_contains_region (c : Fin E.cap_count → ℝ)
    (i : Fin E.cap_count) :
    E.limit_identify.inverse '' (E.necks i).neck.region 0 (c i) ⊆
      regularControl E c :=
  (positiveNeckControl_contains_region E i (c i)).trans
    (positiveNeckControl_subset_regularControl E c i)

/-- The closed central levels are in the finite control set whenever its
cutoffs are nonnegative. Proposition 15.12, p. 365, includes these cap
boundary points in the metric-controlled region. -/
theorem regularControl_contains_central (c : Fin E.cap_count → ℝ)
    (i : Fin E.cap_count) (hc : 0 ≤ c i) :
    E.limit_identify.inverse '' (E.necks i).neck.central_sphere ⊆
      regularControl E c :=
  (positiveNeckControl_contains_central E i hc).trans
    (positiveNeckControl_subset_regularControl E c i)

/-- Each entire truncated open collar is controlled: its negative part
is retained and its nonnegative part lies in the closed strip. This gives
the collar neighborhoods for Proposition 15.12, p. 365, as specified by
the compact regular support in the SurgeryComparison repair contract. -/
theorem regularControl_contains_neck_region (c : Fin E.cap_count → ℝ)
    (i : Fin E.cap_count) :
    E.limit_identify.inverse ''
        (E.necks i).neck.region (-(E.necks i).neck.epsilon⁻¹) (c i) ⊆
      regularControl E c := by
  rintro x ⟨y, hy, rfl⟩
  by_cases hneg : ((E.necks i).neck.coordinate_inverse y).2 < 0
  · obtain ⟨z, hz, hzy⟩ := E.neck_negative_retained i ⟨hy.1, hy.2.1, hneg⟩
    apply retained_pre_subset_regularControl E c
    rw [← hzy, E.limit_identify.left_inverse (E.retained_pre_subset hz)]
    exact hz
  · apply positiveNeckControl_subset_regularControl E c i
    refine ⟨y, ?_, rfl⟩
    exact ⟨(E.necks i).neck.coordinate_inverse y,
      ⟨mem_univ _, le_of_not_gt hneg, hy.2.2.le⟩,
      MetricSurgery.neck_coordinate_inverse _ hy.1⟩

/-- On the regular region, the entire preimage of a truncated open neck
lies in the control set. This is the form used by the local gluing cover
for Proposition 15.12, p. 365. -/
theorem regularControl_contains_regular_neck_region (c : Fin E.cap_count → ℝ)
    (i : Fin E.cap_count) :
    E.regular_limit ∩ E.limit_identify.map ⁻¹'
        (E.necks i).neck.region (-(E.necks i).neck.epsilon⁻¹) (c i) ⊆
      regularControl E c := by
  intro x hx
  exact regularControl_contains_neck_region E c i
    ⟨E.limit_identify.map x, hx.2, E.limit_identify.left_inverse hx.1⟩

end PoincareMT.SurgeryComparison
