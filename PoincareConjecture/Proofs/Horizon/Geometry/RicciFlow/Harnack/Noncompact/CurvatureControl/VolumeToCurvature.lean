import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.FromVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Volume.Asymptotic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.Factor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ZeroVolume.Theorem
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.InitialVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.RightBounds















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t3Space FlowCarrier.secondCountable



theorem false_of_positive_volume_small_ancient_limit
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (C : FlowCarrier.{0} (m + 1)) {δ : ℝ} (hδ : 0 < δ)
    (G : RicciFlow (m + 1) C.carrier (Iio δ)) (p : C.carrier)
    (hcomplete : ∀ t ∈ Iio δ, MetricComplete (G.metric t))
    (hnonflat : 0 < (G.connection 0).curvatureTensorNorm p)
    (hbound : ∀ t ∈ Iio δ, ∀ x : C.carrier,
      (G.connection t).curvatureTensorNorm x ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * 4)
    (hoperator : ∀ t ∈ Iio δ, ∀ x : C.carrier,
      (G.connection t).NonnegativeCurvatureOperator x)
    {ν : ℝ} (hν : 0 < ν)
    (hvolume : ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (ν * r ^ (m + 1)) ≤
        (G.metric 0).volumeMeasure ((G.metric 0).ball p r)) : False := by
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  let : ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftChartedSpace _ C.carrier
  let : IsManifold (𝓡 (m + 1)) ∞ (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftIsManifold (𝓡 (m + 1)) C.carrier
  let : ConnectedSpace (ULift.{u} C.carrier) :=
    (Homeomorph.ulift.connectedSpace_iff).mpr inferInstance
  let : SecondCountableTopology (ULift.{u} C.carrier) :=
    Homeomorph.ulift.secondCountableTopology
  let Hlift : RicciFlow (m + 1) (ULift.{u} C.carrier) (Iio δ) := G.ulift
  let H : RicciFlow (m + 1) (ULift.{u} C.carrier) (Iic 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow Hlift
      (fun _ ht => ht.trans_lt hδ) ordConnected_Iic
      (by exact ⟨-1, by norm_num, 0, by norm_num, by norm_num⟩)
  have hc (t : ℝ) (ht : t ≤ 0) : MetricComplete (H.metric t) :=
    (G.ulift_metricComplete_iff t).mpr (hcomplete t (ht.trans_lt hδ))
  have hop (t : ℝ) (ht : t ≤ 0) (x : ULift.{u} C.carrier) :
      (H.connection t).NonnegativeCurvatureOperator x :=
    (G.ulift_nonnegativeCurvatureOperator_iff t x).mpr
      (hoperator t (ht.trans_lt hδ) x.down)
  have hb (t : ℝ) (ht : t ≤ 0) (x : ULift.{u} C.carrier) :
      (H.connection t).curvatureTensorNorm x ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * 4 := by
    change (G.ulift.connection t).curvatureTensorNorm x ≤ _
    rw [G.ulift_curvatureTensorNorm]
    exact hbound t (ht.trans_lt hδ) x.down
  have hv (r : ℝ) (hr : 0 < r) :
      ENNReal.ofReal (ν * r ^ (m + 1)) ≤
        (H.metric 0).volumeMeasure ((H.metric 0).ball (ULift.up p) r) := by
    change ENNReal.ofReal (ν * r ^ (m + 1)) ≤
      (G.ulift.metric 0).volumeMeasure ((G.ulift.metric 0).ball (ULift.up p) r)
    rw [G.ulift_volumeMeasure_ball]
    exact hvolume r hr
  let : NoncompactSpace (ULift.{u} C.carrier) :=
    (H.metric 0).noncompactSpace_of_ball_volume_lower_bound (by omega)
      (ULift.up p) hν hv
  have hAVR : 0 < (H.metric 0).asymptoticVolumeRatio (ULift.up p) :=
    G.ulift_asymptoticVolumeRatio_pos_of_ball_volume_lower_bound hC (by omega)
      0 p (hcomplete 0 hδ) (hoperator 0 hδ) hν hvolume
  have hscalar : 0 < (H.connection 0).scalarCurvature (ULift.up p) := by
    have hn : 0 < (H.connection 0).curvatureTensorNorm (ULift.up p) := by
      change 0 < (G.ulift.connection 0).curvatureTensorNorm (ULift.up p)
      simpa only [G.ulift_curvatureTensorNorm] using hnonflat
    have h := (H.connection 0).curvatureTensorNorm_le_scalarCurvature
      (hC.tensor_calculus _ _ _ _) (ULift.up p) (hop 0 le_rfl _)
    exact (mul_pos_iff.mp (hn.trans_le h)).resolve_right (by
      intro hh
      exact (sq_nonneg (((m + 1 : ℕ) : ℝ))).not_gt hh.1) |>.2
  obtain ⟨hκ, hnoncollapse⟩ :=
    H.ancient_parabolic_noncollapse_of_terminal_asymptoticVolumeRatio hC hm
      hc hop (by positivity) hb (ULift.up p) hAVR
  have hz := zero_asymptoticVolumeRatio_of_bounded_ancient (n := m + 1)
    (by omega) hC H hc hop (K := ((m + 1 : ℕ) : ℝ) ^ 2 * 4) (by positivity) hb
    (κ := (H.metric 0).asymptoticVolumeRatio (ULift.up p) /
      2 ^ (m + 1)) hκ hnoncollapse ⟨ULift.up p, hscalar⟩
  exact hAVR.ne' ((hz 0 le_rfl (ULift.up p)).1)



theorem exists_time_mul_scalarCurvature_bound_of_unit_ball_volume
    {m : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (F : RicciFlow (m + 1) M J) {a b ν : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hν : 0 < ν)
    (hvolume : ∀ t ∈ Icc a b, ∀ x : M,
      ENNReal.ofReal ν ≤ (F.metric t).volumeMeasure ((F.metric t).ball x 1)) :
    ∃ K : ℝ, ∀ t ∈ Ioc a b, ∀ x : M,
      (t - a) * (F.connection t).scalarCurvature x ≤ K := by
  by_contra hnot
  push Not at hnot
  obtain ⟨C, δ, hδ, _, G, p, hc, hn, hb, hop, hv⟩ :=
    F.exists_positive_volume_ancient_limit_of_unbounded_time_scalar hC hm hab hJ
      hcomplete hoperator hν hvolume hnot
  exact false_of_positive_volume_small_ancient_limit hC hm C hδ G p
    hc hn hb hop (by positivity) hv




theorem exists_right_curvatureTensorNorm_bound_on_component_of_bounded_ancient_zero_volume
    {n : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M J) (p : M) {a b : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a b, ∀ x ∈ connectedComponent p,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hinitial : ∃ S : ℝ, 0 ≤ S ∧ ∀ x ∈ connectedComponent p,
      (F.connection a).CurvatureOperatorBound S x) :
    ∃ d ∈ Ioc a b, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a d,
      ∀ x ∈ connectedComponent p, (F.connection t).curvatureTensorNorm x ≤ B := by
  by_cases hn : n ≤ 1
  · exact ⟨b, ⟨hab, le_rfl⟩, 0, le_rfl, fun t _ x _ =>
      F.curvatureTensorNorm_bound_zero_of_dimension_le_one hn t x⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm : 0 < m := by omega
  obtain ⟨d, hd, ν, hν, hvolume⟩ :=
    F.exists_right_unit_ball_volume_lower_bound_on_component hC (by omega) p hab
      hJ hcomplete hoperator hinitial
  have hsub : Icc a d ⊆ Icc a b := Icc_subset_Icc_right hd.2
  let G := F.restrictComponent p
  obtain ⟨K, hK⟩ := G.exists_time_mul_scalarCurvature_bound_of_unit_ball_volume
    hC hm hd.1 (hsub.trans hJ)
    (fun t ht => F.restrictComponent_metricComplete p t (hcomplete t (hsub ht)))
    (fun t ht x => (F.restrictComponent_nonnegativeCurvatureOperator_iff p t x).mpr
      (hoperator t (hsub ht) x x.property)) hν (by
        intro t ht x
        rw [F.restrictComponent_volumeMeasure_ball]
        exact hvolume t ht x x.property)
  obtain ⟨B, hB, hb⟩ :=
    F.exists_uniform_curvatureTensorNorm_bound_on_component_of_reciprocal_time_bound
      hC p (hsub.trans hJ) (fun t ht => hcomplete t (hsub ht))
      (fun t ht => hoperator t (hsub ht)) hinitial (K := K) (by
        intro t ht x hx
        have h := hK t ht ⟨x, hx⟩
        rw [F.restrictComponent_scalarCurvature] at h
        apply (le_div_iff₀ (sub_pos.mpr ht.1)).mpr
        simpa only [mul_comm] using h)
  exact ⟨d, hd, B, hB, hb⟩

end PoincareConjecture.RicciFlow
