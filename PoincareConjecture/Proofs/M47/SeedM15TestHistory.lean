import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.HalfRadiusHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M46

structure SeedM15TestHistory {F : SurgeryFlowData.{u}}
    (T : ℝ) (hT : 0 < T) (hTF : T ∈ F.time_domain)
    (x : (F.slice T).carrier) (r : ℝ) where
  spacetime : M46RegularSpacetimeData (F.closedRegularHistoryWindow T hT hTF ⟨x⟩)
  time_mem : T ∈ spacetime.history.generalized.interval
  center : (spacetime.history.generalized.slice T).carrier
  center_eq : spacetime.history.history.forward T time_mem center = x
  cylinder : GeneralizedFlowCylinder spacetime.history.generalized
    (spacetime.history.generalized.slice T) T 1
    (Icc (-(r / 2) ^ 2) 0)
    ((spacetime.history.generalized.metric T).ball center (r / 2))
  time_subset : Icc (T - (r / 2) ^ 2) T ⊆ spacetime.history.generalized.interval
  based : ∀ h y,
    y ∈ (spacetime.history.generalized.metric T).ball center (r / 2) →
    cylinder.pointMap 0 h y = (⟨T, y⟩ : spacetime.history.generalized.point)
  curvature : ∀ s hs y,
    y ∈ (spacetime.history.generalized.metric T).ball center (r / 2) →
    spacetime.history.generalized.curvatureNorm (cylinder.pointMap s hs y) ≤
      (r / 2)⁻¹ ^ 2
  terminal_ball_compact : IsCompact (closure
    ((spacetime.geometry.toLGeometry.slices T).metricOnPoints.ball
      ((spacetime.geometry.sliceIdentification T).identification center) (r / 2)))

private theorem history_point_heq {F : SurgeryFlowData.{u}}
    {G : GeneralizedRicciFlowData.{u}} (H : M33RegularHistoryRealization G F)
    {s t : ℝ} (hs : s ∈ G.interval) (ht : t ∈ G.interval)
    {x : (G.slice s).carrier} {y : (G.slice t).carrier} (hst : s = t)
    (h : HEq (H.forward s hs x) (H.forward t ht y)) : HEq x y := by
  subst t
  exact heq_of_eq ((H.forward_openEmbedding s hs).injective (eq_of_heq h))

theorem seedM15_testHistory (P : M46Predecessors.{u})
    {F : SurgeryFlowData.{u}} {T r : ℝ} (hT : 0 < T) (hTF : T ∈ F.time_domain)
    (x : (F.slice T).carrier) (hr : 0 < r)
    (test : SurgeryFlowCylinder F (F.slice T) T 1
      (Icc (-r ^ 2) 0) ((F.metric T).ball x r))
    (hbased : ∀ h y, y ∈ (F.metric T).ball x r → HEq (test.forward 0 h y) y)
    (hcurv : ∀ s hs y, y ∈ (F.metric T).ball x r →
      (F.connection (T + s / 1)).curvatureTensorNorm (test.forward s hs y) ≤ r⁻¹ ^ 2) :
    Nonempty (SeedM15TestHistory T hT hTF x r) := by
  obtain ⟨R⟩ := P.regularSpacetime (F.closedRegularHistoryWindow T hT hTF ⟨x⟩)
  have ht : T ∈ R.history.generalized.interval := by
    rw [R.history.interval_eq]
    exact ⟨hT.le, le_rfl⟩
  have hretain := test.terminal_ball_regular x hr hbased
  have hxball : x ∈ (F.metric T).ball x r := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice T).carrier → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) x x < ENNReal.ofReal r
    simpa only [Manifold.riemannianEDist_self] using ENNReal.ofReal_pos.mpr hr
  obtain ⟨y, hy⟩ : x ∈ range (R.history.history.forward T ht) := by
    rw [R.history.regular_range]
    exact hretain hxball
  have hJ : Icc (-(r / 2) ^ 2) 0 ⊆ Icc (-r ^ 2) 0 := by
    intro s hs
    exact ⟨by nlinarith [hs.1, sq_nonneg r], hs.2⟩
  let U := (F.metric T).ball (R.history.history.forward T ht y) (r / 2)
  have hU : U ⊆ (F.metric T).ball x r := by
    intro z hz
    rw [← hy]
    exact hz.trans_le (ENNReal.ofReal_le_ofReal (half_le_self hr.le))
  let e := test.restrict hJ ordConnected_Icc hU
  have htime (s : ℝ) (hs : s ∈ Icc (-(r / 2) ^ 2) 0) :
      T + s / 1 ∈ R.history.generalized.interval := by
    rw [R.history.interval_eq]
    have hn := F.time_domain_nonnegative (e.time_subset ⟨s, hs, rfl⟩)
    exact ⟨hn, by simpa using hs.2⟩
  have hreg (s : ℝ) (hs : s ∈ Icc (-(r / 2) ^ 2) 0) :
      e.forward s hs '' U ⊆ m33RegularRegion F (T + s / 1) := by
    rintro z ⟨w, hw, rfl⟩
    exact (test.regular_image_smaller_closed (half_pos hr) (half_lt_self hr) hs).choose_spec
      ⟨w, hU hw, rfl⟩
  obtain ⟨d, hd, _⟩ := R.history.cylinders_from_surgery (F.slice T) T 1
    (Icc (-(r / 2) ^ 2) 0) U (M04.initial_ball_isOpen _ _ _) htime e hreg
  let c := R.history.history.rebaseCylinder T ht y (r / 2) d
  have hmaps (z : (R.history.generalized.slice T).carrier)
      (hz : z ∈ (R.history.generalized.metric T).ball y (r / 2)) :
      R.history.history.forward T ht z ∈ U :=
    R.history.history.ball_image_subset T ht y (r / 2) ⟨z, hz, rfl⟩
  have hb : ∀ h z,
      z ∈ (R.history.generalized.metric T).ball y (r / 2) →
      c.pointMap 0 h z = (⟨T, z⟩ : R.history.generalized.point) := by
    intro h z hz
    apply Sigma.ext (by simp [GeneralizedFlowCylinder.pointMap])
    apply history_point_heq R.history.history (htime 0 h) ht (by simp)
    exact (heq_of_eq (hd 0 h _ (hmaps z hz))).trans
      (hbased (hJ h) _ (hU (hmaps z hz)))
  have hc : ∀ s hs z,
      z ∈ (R.history.generalized.metric T).ball y (r / 2) →
      R.history.generalized.curvatureNorm (c.pointMap s hs z) ≤ (r / 2)⁻¹ ^ 2 := by
    intro s hs z hz
    have hp := R.history.curvature_norm_pullback (T + s / 1) (htime s hs)
      (d.forward s hs (R.history.history.forward T ht z))
    rw [hd s hs _ (hmaps z hz)] at hp
    change (R.history.generalized.connection (T + s / 1)).curvatureTensorNorm
      (d.forward s hs (R.history.history.forward T ht z)) ≤ _
    rw [← hp]
    apply (hcurv s (hJ hs) _ (hU (hmaps z hz))).trans
    exact pow_le_pow_left₀ (inv_nonneg.mpr hr.le)
      ((inv_le_inv₀ hr (half_pos hr)).mpr (half_le_self hr.le)) 2
  refine ⟨{
    spacetime := R
    time_mem := ht
    center := y
    center_eq := hy
    cylinder := c
    time_subset := ?_
    based := hb
    curvature := hc
    terminal_ball_compact := ?_ }⟩
  · intro s hs
    have h := htime (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simpa only [div_one, add_sub_cancel] using h
  · have hcompact := history_halfBall_compact R.history ht y hr
      (by simpa only [hy] using hretain)
    change IsCompact (closure ((R.geometry.realization.slices T).metricOnPoints.ball
      ((R.geometry.sliceIdentification T).identification y) (r / 2)))
    rw [← Proofs.M13.originalSlice_ball R.geometry P.m13 T y (r / 2)]
    convert! hcompact.image (R.geometry.sliceIdentification T).identification.continuous
      using 1
    exact ((R.geometry.sliceIdentification T).identification.toHomeomorph.image_closure
      ((R.history.generalized.metric T).ball y (r / 2))).symm

end PoincareConjecture.M47
