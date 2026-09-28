import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.Regularity
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenMetricBalls
import PoincareConjecture.Proofs.M28.Generalized.MetricVolumeCalibration
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

private theorem mapsTo_open_of_pathELength_lt_of_regular
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M) (p : U)
    {r : ℝ} (hp : p ∈ regularPoints (intrinsicOpenMetric g U) r)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1))
    (h0 : γ 0 = (p : M)) (hlen : g.pathELength γ 0 1 < ENNReal.ofReal r) :
    MapsTo γ (Icc (0 : ℝ) 1) (U : Set M) := by
  let h := intrinsicOpenMetric g U
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨h.toRiemannianMetric⟩
  have hfinite : g.pathELength γ 0 1 ≠ ⊤ := ne_top_of_lt (hlen.trans_le le_top)
  obtain ⟨s, hLs, hsr⟩ := exists_between (ENNReal.toReal_lt_of_lt_ofReal hlen)
  have hs : 0 < s := ENNReal.toReal_nonneg.trans_lt hLs
  have hshort : g.pathELength γ 0 1 < ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff hs).mpr hLs
  let K : Set M := (Subtype.val : U → M) '' closure (h.ball p s)
  have hK : IsCompact K := (hp s hsr).image continuous_subtype_val
  have hKU : K ⊆ (U : Set M) := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have h0U : γ 0 ∈ (U : Set M) := by rw [h0]; exact p.property
  intro t ht
  by_contra htU
  let F : Set ℝ := Icc (0 : ℝ) 1 ∩ γ ⁻¹' (U : Set M)ᶜ
  have hF : IsCompact F := isCompact_Icc.of_isClosed_subset
    (hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc U.isOpen.isClosed_compl)
    inter_subset_left
  obtain ⟨c, hc, hleast⟩ := hF.exists_isLeast ⟨t, ht, htU⟩
  have hcpos : 0 < c := lt_of_le_of_ne hc.1.1 (by
    intro heq
    exact hc.2 (heq ▸ h0U))
  have hbefore : MapsTo γ (Ico (0 : ℝ) c) (U : Set M) := by
    intro v hv
    by_contra hvU
    exact (not_lt_of_ge (hleast ⟨⟨hv.1, hv.2.le.trans hc.1.2⟩, hvU⟩)) hv.2
  have hprefix : MapsTo γ (Ico (0 : ℝ) c) K := by
    intro v hv
    have hγv : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) v) :=
      hγ.mono (Icc_subset_Icc le_rfl (hv.2.le.trans hc.1.2))
    have hγU : MapsTo γ (Icc (0 : ℝ) v) (U : Set M) := by
      intro w hw
      exact hbefore ⟨hw.1, hw.2.trans_lt hv.2⟩
    obtain ⟨η, hη, heq, hlength⟩ :=
      exists_intrinsicOpenMetric_path_lift g U hv.1 hγv hγU
    have hη0 : η 0 = p := Subtype.ext ((heq (left_mem_Icc.mpr hv.1)).trans h0)
    have hdist : h.edist p (η v) ≤ h.pathELength η 0 v :=
      Manifold.riemannianEDist_le_pathELength hη hη0 rfl hv.1
    have hmono : g.pathELength γ 0 v ≤ g.pathELength γ 0 1 :=
      Manifold.pathELength_mono le_rfl (hv.2.le.trans hc.1.2)
    have hball : η v ∈ h.ball p s := by
      change h.edist p (η v) < ENNReal.ofReal s
      exact hdist.trans_lt (hlength.trans_le hmono |>.trans_lt hshort)
    exact ⟨η v, subset_closure hball, heq (right_mem_Icc.mpr hv.1)⟩
  have hγc : ContinuousOn γ (closure (Ico (0 : ℝ) c)) := by
    rw [closure_Ico hcpos.ne]
    exact hγ.continuousOn.mono (Icc_subset_Icc le_rfl hc.1.2)
  have hclosed : MapsTo γ (Icc (0 : ℝ) c) K := by
    simpa only [closure_Ico hcpos.ne, hK.isClosed.closure_eq] using
      hprefix.closure_of_continuousOn hγc
  exact hc.2 (hKU (hclosed (right_mem_Icc.mpr hcpos.le)))

theorem ambient_ball_subset_open_of_intrinsic_regular
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M) (p : U)
    {r : ℝ} (hp : p ∈ regularPoints (intrinsicOpenMetric g U) r) :
    g.ball (p : M) r ⊆ (U : Set M) := by
  intro q hq
  obtain ⟨γ, h0, h1, hγ, hlen, _⟩ := g.exists_short_path_in_ball (p : M) q hq
  have hmaps := mapsTo_open_of_pathELength_lt_of_regular g U p hp hγ h0 hlen
  simpa only [h1] using hmaps (right_mem_Icc.mpr zero_le_one)

theorem intrinsicOpenMetric_ball_eq_preimage_of_regular
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M) (p : U)
    {r : ℝ} (hp : p ∈ regularPoints (intrinsicOpenMetric g U) r) :
    (intrinsicOpenMetric g U).ball p r =
      (Subtype.val : U → M) ⁻¹' g.ball (p : M) r :=
  intrinsicOpenMetric_ball_eq_preimage g U p
    (ambient_ball_subset_open_of_intrinsic_regular g U p hp)

theorem intrinsicOpenMetric_ball_image_of_regular
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M) (p : U)
    {r : ℝ} (hp : p ∈ regularPoints (intrinsicOpenMetric g U) r) :
    (Subtype.val : U → M) '' (intrinsicOpenMetric g U).ball p r =
      g.ball (p : M) r := by
  rw [intrinsicOpenMetric_ball_eq_preimage_of_regular g U p hp]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, ambient_ball_subset_open_of_intrinsic_regular g U p hp hx⟩, hx, rfl⟩

variable [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]

theorem intrinsicOpenMetric_ball_volume_of_regular
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M) (p : U)
    {r : ℝ} (hp : p ∈ regularPoints (intrinsicOpenMetric g U) r) :
    (intrinsicOpenMetric g U).volumeMeasure ((intrinsicOpenMetric g U).ball p r) =
      g.volumeMeasure (g.ball (p : M) r) := by
  let h := intrinsicOpenMetric g U
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace U := EMetricSpace.ofRiemannianMetric (𝓡 3) U
  have hball : MeasurableSet (h.ball p r) := by
    change MeasurableSet {q : U | edist p q < ENNReal.ofReal r}
    exact (isOpen_lt (continuous_const.edist continuous_id) continuous_const).measurableSet
  rw [intrinsicOpenMetric_volumeMeasure_apply g U hball,
    intrinsicOpenMetric_ball_image_of_regular g U p hp]

theorem intrinsicOpenMetric_ball_calibratedVolume_of_regular
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M) (p : U)
    {r : ℝ} (hp : p ∈ regularPoints (intrinsicOpenMetric g U) r) :
    calibratedMetricVolume (intrinsicOpenMetric g U) ((intrinsicOpenMetric g U).ball p r) =
      calibratedMetricVolume g (g.ball (p : M) r) := by
  simpa only [volumeMeasure_eq_calibratedMetricVolume] using
    intrinsicOpenMetric_ball_volume_of_regular g U p hp

end PoincareConjecture.M28
