import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Retention
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.OpenSlices
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.RegularHistory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Neck.NeckCoordinates

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

namespace SurgeryEventData

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {S : ℝ → GeneralizedSliceCarrier.{u}}
  {g : ∀ t, RiemannianMetric 3 (S t).carrier} {T : ℝ}
  (E : SurgeryEventData g₀ K P S g T)

theorem retained_post_interior_nonempty [Nonempty (S T).carrier] :
    (interior E.retained_post).Nonempty := by
  classical
  by_cases hzero : E.cap_count = 0
  · have hcaps : (⋃ i, (E.caps i).carrier) = ∅ := by
      ext x
      simp only [mem_iUnion, mem_empty_iff_false, iff_false, not_exists]
      intro i
      exact (Nat.not_lt_zero i.val (hzero ▸ i.isLt)).elim
    have hpost : E.retained_post = univ := by
      simpa only [hcaps, union_empty] using E.post_cover
    rw [hpost, interior_univ]
    exact univ_nonempty
  · let i : Fin E.cap_count := ⟨0, Nat.pos_of_ne_zero hzero⟩
    let N := (E.necks i).neck
    let V := N.region (-N.epsilon⁻¹) 0
    have hV : IsOpen V := MetricSurgery.neck_region_isOpen N _ _
    have hVne : V.Nonempty := by
      obtain ⟨z, _, _⟩ := N.central_sphere_eq ▸ N.center_on_central_sphere
      have heps : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
      let s : Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := ⟨-N.epsilon⁻¹ / 2, by
        constructor <;> linarith⟩
      refine ⟨(N.coordinate (z.1, s)).val, (N.coordinate (z.1, s)).property, ?_⟩
      rw [N.coordinate_inverse_left]
      dsimp [s]
      constructor <;> linarith
    have hpre : E.limit_identify.inverse '' V ⊆ E.retained_pre := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := E.neck_negative_retained i hy
      rw [← hxy, E.limit_identify.left_inverse (E.retained_pre_subset hx)]
      exact hx
    have hopen : IsOpen (E.limit_identify.inverse '' V) :=
      E.limit_identify.symm.image_isOpen hV (by simp)
    have hne : (interior E.retained_pre).Nonempty :=
      (hVne.image E.limit_identify.inverse).mono (interior_maximal hpre hopen)
    rw [← E.retention.image_interior]
    exact hne.image E.retention.map

end SurgeryEventData

theorem m33RegularRegion_isOpen (F : SurgeryFlowData.{u}) (t : ℝ) :
    IsOpen (m33RegularRegion F t) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  by_cases hT : t ∈ F.surgery_times
  · let : Nonempty (F.slice t).carrier := ⟨x⟩
    rw [m33RegularRegion_of_surgery F t hT]
    exact isOpen_interior.mem_nhds (hx hT)
  · rw [m33RegularRegion_of_regular F t hT]
    exact Filter.univ_mem

theorem m33RegularRegion_nonempty (F : SurgeryFlowData.{u}) (t : ℝ)
    [Nonempty (F.slice t).carrier] : (m33RegularRegion F t).Nonempty := by
  by_cases hT : t ∈ F.surgery_times
  · rw [m33RegularRegion_of_surgery F t hT]
    exact (F.event t hT).retained_post_interior_nonempty
  · rw [m33RegularRegion_of_regular F t hT]
    exact univ_nonempty

namespace Surgery.RegularHistory

variable {F : SurgeryFlowData.{u}} (W : M33RegularHistoryWindow F)

def region (t : ℝ) : Set (F.slice t).carrier :=
  {x | t ∈ W.interval ∧ x ∈ m33RegularRegion F t}

theorem region_isOpen (t : ℝ) : IsOpen (region W t) := by
  by_cases ht : t ∈ W.interval
  · have heq : region W t = m33RegularRegion F t := Set.ext fun _ => and_iff_right ht
    rw [heq]
    exact m33RegularRegion_isOpen F t
  · simp only [region, ht, false_and, ofPred_false, isOpen_empty]

def regionOpens (t : ℝ) : Opens (F.slice t).carrier := ⟨region W t, region_isOpen W t⟩

def slice (t : ℝ) : GeneralizedSliceCarrier.{u} := (F.slice t).openSubset (regionOpens W t)

def metric (t : ℝ) : RiemannianMetric 3 (slice W t).carrier :=
  (F.slice t).openSubsetMetric (regionOpens W t) (F.metric t)

def connection (t : ℝ) : LeviCivitaData (metric W t) :=
  (F.slice t).openSubsetConnection (regionOpens W t) (F.metric t)

def forward (t : ℝ) : (slice W t).carrier → (F.slice t).carrier := Subtype.val

theorem slice_nonempty_iff (t : ℝ) : Nonempty (slice W t).carrier ↔ t ∈ W.interval := by
  constructor
  · rintro ⟨x⟩
    exact x.property.1
  · intro ht
    let : Nonempty (F.slice t).carrier := W.slice_nonempty t ht
    obtain ⟨x, hx⟩ := m33RegularRegion_nonempty F t
    exact ⟨⟨x, ht, hx⟩⟩

theorem forward_openEmbedding (t : ℝ) : Topology.IsOpenEmbedding (forward W t) :=
  (F.slice t).openSubset_inclusion_openEmbedding (regionOpens W t)

theorem forward_smooth (t : ℝ) : ContMDiff (𝓡 3) (𝓡 3) ∞ (forward W t) :=
  (F.slice t).openSubset_inclusion_smooth (regionOpens W t)

theorem regular_range (t : ℝ) (ht : t ∈ W.interval) :
    range (forward W t) = m33RegularRegion F t := by
  change range (Subtype.val : (slice W t).carrier → (F.slice t).carrier) = _
  rw [(F.slice t).openSubset_inclusion_range (regionOpens W t)]
  ext x
  exact and_iff_right ht

theorem metric_pullback (t : ℝ) (x : (slice W t).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (F.metric t).inner (forward W t x)
      (mfderiv (𝓡 3) (𝓡 3) (forward W t) x v)
      (mfderiv (𝓡 3) (𝓡 3) (forward W t) x w) = (metric W t).inner x v w := rfl

theorem scalar_pullback (t : ℝ) (x : (slice W t).carrier) :
    (F.connection t).scalarCurvature (forward W t x) =
      (connection W t).scalarCurvature x :=
  ((F.slice t).openSubset_scalar (regionOpens W t) (F.metric t) (F.connection t) x).symm

theorem curvature_norm_pullback (t : ℝ) (x : (slice W t).carrier) :
    (F.connection t).curvatureTensorNorm (forward W t x) =
      (connection W t).curvatureTensorNorm x :=
  ((F.slice t).openSubset_curvatureNorm (regionOpens W t)
    (F.metric t) (F.connection t) x).symm

theorem negative_part_pullback (t : ℝ) (x : (slice W t).carrier) :
    (F.connection t).negativeCurvaturePart (forward W t x) =
      (connection W t).negativeCurvaturePart x :=
  ((F.slice t).openSubset_negativePart (regionOpens W t)
    (F.metric t) (F.connection t) x).symm

theorem volume_image (t : ℝ) (U : Set (slice W t).carrier) :
    calibratedMetricVolume (F.metric t) (forward W t '' U) =
      calibratedMetricVolume (metric W t) U :=
  (F.slice t).openSubset_volume (regionOpens W t) (F.metric t) U

theorem regular_distance (t : ℝ) (ht : t ∈ W.interval) (hT : t ∉ F.surgery_times)
    (x y : (slice W t).carrier) :
    (F.metric t).edist (forward W t x) (forward W t y) = (metric W t).edist x y := by
  have hregion : (regionOpens W t : Set (F.slice t).carrier) = univ := by
    ext z
    simp only [regionOpens, Opens.coe_mk, region, mem_ofPred_eq, ht, true_and,
      m33RegularRegion_of_regular F t hT, mem_univ]
  exact ((F.slice t).openSubset_distance_of_isClosed (regionOpens W t)
    (hregion ▸ isClosed_univ) (F.metric t) x y).symm

def inverse (t : ℝ) (ht : t ∈ W.interval) : (F.slice t).carrier → (slice W t).carrier := by
  let : Nonempty (slice W t).carrier := (slice_nonempty_iff W t).mpr ht
  exact Function.invFun (forward W t)

theorem left_inverse (t : ℝ) (ht : t ∈ W.interval) :
    Function.LeftInverse (inverse W t ht) (forward W t) := by
  let : Nonempty (slice W t).carrier := (slice_nonempty_iff W t).mpr ht
  exact Function.leftInverse_invFun (forward_openEmbedding W t).injective

theorem right_inverse (t : ℝ) (ht : t ∈ W.interval) :
    LeftInvOn (forward W t) (inverse W t ht) (range (forward W t)) := by
  rintro _ ⟨x, rfl⟩
  rw [left_inverse W t ht x]

theorem inverse_smooth (t : ℝ) (ht : t ∈ W.interval) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (inverse W t ht) (range (forward W t)) := by
  let : Nonempty (slice W t).carrier := (slice_nonempty_iff W t).mpr ht
  exact (metric W t).contMDiffOn_invFun_of_injective_pullback_eq
    (F.metric t) (forward_smooth W t) (forward_openEmbedding W t).injective
    (metric_pullback W t)

end Surgery.RegularHistory

end PoincareConjecture
