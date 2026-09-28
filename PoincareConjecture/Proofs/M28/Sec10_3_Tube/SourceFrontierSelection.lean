import PoincareConjecture.Proofs.M28.Sec10_3_Tube.FrontierSelection
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceNeckRegion
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckPrecompactBalls
import Mathlib.Topology.UniformSpace.HeineCantor










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckSegment

variable {epsilon C A D₀ D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D₀ D}




theorem exists_neck_scale_lower (S : CounterexampleNeckSegment E) :
    ∃ h : ℝ, 0 < h ∧ ∀ N ∈ S.cover.necks, h ≤ N.scale := by
  let R := E.flow.scalar ⟨E.time, S.path S.upper⟩
  have hu : S.path S.upper ∈ S.cover.X := by
    rw [S.cover_set]
    exact mem_image_of_mem _ (right_mem_Icc.mpr S.lower_lt_upper.le)
  obtain ⟨Nu, hNu, hcenter⟩ := S.cover.pointwise_center_cover _ hu
  have hR : 0 < R := by
    have h := Nu.scalar_center_pos
    rw [Nu.connection.scalarCurvature_eq_m28 (E.flow.connection E.time), hcenter] at h
    exact h
  refine ⟨min 1 R⁻¹, lt_min zero_lt_one (inv_pos.mpr hR), ?_⟩
  intro N hN
  have hc := S.center_mem_cover N hN
  rw [S.cover_set] at hc
  obtain ⟨s, hs, hcenter⟩ := hc
  have hupper : E.flow.scalar ⟨E.time, N.center⟩ ≤ R := by
    rw [← hcenter]
    exact (S.scalar_band s hs).2
  have hnormalize := tube.neck_normalized_scalar_center N (E.flow.connection E.time)
  change N.scale ^ 2 * E.flow.scalar ⟨E.time, N.center⟩ = 1 at hnormalize
  have hsq : 1 ≤ N.scale ^ 2 * R := by
    rw [← hnormalize]
    exact mul_le_mul_of_nonneg_left hupper (sq_nonneg N.scale)
  by_cases hlarge : 1 ≤ N.scale
  · exact (min_le_left _ _).trans hlarge
  · have hsmall : N.scale < 1 := lt_of_not_ge hlarge
    have hpower : N.scale ^ 2 ≤ N.scale := by nlinarith [N.scale_pos]
    have hmul := mul_le_mul_of_nonneg_right hpower hR.le
    apply (min_le_right _ _).trans
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hR).mpr
    nlinarith only [hsq, hmul]




theorem exists_neck_parameter_margin (S : CounterexampleNeckSegment E) :
    ∃ d : ℝ, 0 < d ∧ ∀ s ∈ Icc S.lower S.upper,
      ∀ N ∈ S.cover.necks, N.center = S.path s →
        ∀ t ∈ Icc S.lower S.upper, |t - s| < d → S.path t ∈ N.carrier := by
  let g := E.flow.metric E.time
  let M := (E.flow.slice E.time).carrier
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  obtain ⟨h, hh, hscale⟩ := S.exists_neck_scale_lower
  have hepsilon : 0 < epsilon := S.cover_epsilon ▸ S.cover.epsilon_pos
  let r := h * epsilon⁻¹ / 8
  have hr : 0 < r := by dsimp [r]; positivity
  have hpath : ContinuousOn S.path (Icc S.lower S.upper) :=
    S.path_smooth.continuousOn.mono
      (Icc_subset_Icc S.lower_pos.le S.upper_lt_one.le)
  have huniform := isCompact_Icc.uniformContinuousOn_of_continuous hpath
  obtain ⟨delta, hdelta, hmod⟩ := EMetric.uniformContinuousOn_iff.mp huniform
    (ENNReal.ofReal r) (ENNReal.ofReal_pos.mpr hr)
  obtain ⟨d, _, hd, hddelta⟩ := ENNReal.lt_iff_exists_real_btwn.mp hdelta
  have hdpos : 0 < d := ENNReal.ofReal_pos.mp hd
  refine ⟨d, hdpos, ?_⟩
  intro s hs N hN hcenter t ht hnear
  have hst : edist s t < delta := by
    rw [edist_dist, Real.dist_eq, abs_sub_comm]
    exact ((ENNReal.ofReal_lt_ofReal_iff hdpos).mpr hnear).trans hddelta
  have hball := hmod hs ht hst
  change g.edist (S.path s) (S.path t) < ENNReal.ofReal r at hball
  have heps : N.epsilon = epsilon := (S.cover.neck_epsilon N hN).trans S.cover_epsilon
  have hrad : r ≤ N.scale * N.epsilon⁻¹ / 8 := by
    rw [heps]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hscale N hN) (inv_nonneg.mpr hepsilon.le))
      (by norm_num)
  have hsmall : S.path t ∈ g.ball N.center (N.scale * N.epsilon⁻¹ / 8) := by
    change g.edist N.center (S.path t) < _
    rw [hcenter]
    exact hball.trans_le (ENNReal.ofReal_le_ofReal hrad)
  exact (N.small_ball_subset_middle N.center_on_central_sphere hsmall).1





theorem exists_frontier_neck_selection (S : CounterexampleNeckSegment E) :
    ∃ N : ℝ → EpsilonNeck (E.flow.metric E.time),
      (∀ s ∈ Icc S.lower S.upper,
        N s ∈ S.cover.necks ∧ (N s).center = S.path s) ∧
      ∃ l : List ℝ,
        (∀ s ∈ S.lower :: l, s ∈ Icc S.lower S.upper) ∧
        (S.lower :: l).IsChain (fun s t =>
          s < t ∧ S.path t ∈ frontier (N s).carrier ∧
            MapsTo S.path (Ico s t) (N s).carrier) ∧
        MapsTo S.path (Icc ((S.lower :: l).getLast (List.cons_ne_nil _ _)) S.upper)
          (N ((S.lower :: l).getLast (List.cons_ne_nil _ _))).carrier ∧
        MapsTo S.path (Icc S.lower S.upper)
          {x | ∃ s ∈ S.lower :: l, x ∈ (N s).carrier} := by
  classical
  have hselect (s : ℝ) (hs : s ∈ Icc S.lower S.upper) :
      ∃ N ∈ S.cover.necks, N.center = S.path s := by
    apply S.cover.pointwise_center_cover
    rw [S.cover_set]
    exact mem_image_of_mem _ hs
  let N₀ := Classical.choose (hselect S.lower (left_mem_Icc.mpr S.lower_lt_upper.le))
  let N : ℝ → EpsilonNeck (E.flow.metric E.time) := fun s =>
    if hs : s ∈ Icc S.lower S.upper then Classical.choose (hselect s hs) else N₀
  have hN (s : ℝ) (hs : s ∈ Icc S.lower S.upper) :
      N s ∈ S.cover.necks ∧ (N s).center = S.path s := by
    dsimp only [N]
    rw [dif_pos hs]
    exact Classical.choose_spec (hselect s hs)
  obtain ⟨d, hd, hnear⟩ := S.exists_neck_parameter_margin
  obtain ⟨l, hlmem, hlchain, hlast⟩ := exists_finite_frontier_selection S.path
    (fun s => (N s).carrier) S.lower_lt_upper.le hd
    (S.path_smooth.continuousOn.mono
      (Icc_subset_Icc S.lower_pos.le S.upper_lt_one.le))
    (fun s _ => (N s).carrier_open)
    (fun s hs t ht hst => hnear s hs (N s) (hN s hs).1 (hN s hs).2 t ht hst)
  refine ⟨N, hN, l, hlmem, ?_, hlast, ?_⟩
  · exact hlchain.imp (fun _ _ h => ⟨by linarith [h.1], h.2⟩)
  · exact mapsTo_finite_frontier_selection (hlchain.imp (fun _ _ h => h.2.2)) hlast

end PoincareConjecture.M28.CounterexampleNeckSegment
