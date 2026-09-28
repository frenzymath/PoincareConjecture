import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckQuarterOverlap










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckSegment

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

private theorem old_positive_quarter_edist_le (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 1000) {x y : M}
    (hx : x ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)
    (hy : y ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) :
    g.edist x y ≤ ENNReal.ofReal ((0.51 : ℝ) * N.scale * N.epsilon⁻¹) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let z := N.coordinate_inverse x
  let w := N.coordinate_inverse y
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem x hx.1).2
  have hw : w.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem y hy.1).2
  have hxy : g.edist x y ≤ ENNReal.ofReal
      (N.scale * Real.sqrt (1 + N.epsilon) * Real.sqrt 2 * Real.pi) +
      ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * |w.2 - z.2|) := by
    calc
      _ = g.edist (N.coordinate_map (z.1, z.2))
          (N.coordinate_map (w.1, w.2)) := by
        rw [Prod.eta, Prod.eta, N.coordinate_map_coordinate_inverse hx.1,
          N.coordinate_map_coordinate_inverse hy.1]
      _ ≤ g.edist (N.coordinate_map (z.1, z.2))
          (N.coordinate_map (w.1, z.2)) +
          g.edist (N.coordinate_map (w.1, z.2))
            (N.coordinate_map (w.1, w.2)) := Manifold.riemannianEDist_triangle
      _ ≤ _ := add_le_add (N.edist_coordinate_map_slice_le z.1 w.1 hz)
        (N.edist_coordinate_map_axis_le w.1 hz hw)
  have haxis : |w.2 - z.2| ≤ N.epsilon⁻¹ / 2 := by
    apply abs_le.mpr
    dsimp [z, w]
    constructor <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
  have hinv : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε (inv_pos.mpr N.epsilon_pos).le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  have hroot : Real.sqrt (1 + N.epsilon) ≤ (1.001 : ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon)]
  have hsphere : Real.sqrt (1 + N.epsilon) * Real.sqrt 2 ≤ 2 := by
    have hsq : (Real.sqrt (1 + N.epsilon) * Real.sqrt 2) ^ 2 =
        (1 + N.epsilon) * 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith [N.epsilon_pos]),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [N.epsilon_lt_half,
      mul_nonneg (Real.sqrt_nonneg (1 + N.epsilon)) (Real.sqrt_nonneg 2)]
  have hnum : Real.sqrt (1 + N.epsilon) * Real.sqrt 2 * Real.pi +
      Real.sqrt (1 + N.epsilon) * |w.2 - z.2| ≤
        (0.51 : ℝ) * N.epsilon⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_right hsphere Real.pi_pos.le
    have h2 := mul_le_mul hroot haxis (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1.001)
    nlinarith [Real.pi_le_four]
  apply hxy.trans
  have ha : 0 ≤ N.scale * Real.sqrt (1 + N.epsilon) * Real.sqrt 2 * Real.pi := by
    exact mul_nonneg (mul_nonneg (mul_nonneg N.scale_pos.le
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) Real.pi_pos.le
  have hb : 0 ≤ N.scale * Real.sqrt (1 + N.epsilon) * |w.2 - z.2| := by
    exact mul_nonneg (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)) (abs_nonneg _)
  rw [← ENNReal.ofReal_add ha hb]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [mul_le_mul_of_nonneg_left hnum N.scale_pos.le]

private theorem neck_positive_quarter_closure_edist_le (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 1000) {x y : M}
    (hx : x ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)
    (hy : y ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)) :
    g.edist x y ≤ ENNReal.ofReal ((0.51 : ℝ) * N.scale * N.epsilon⁻¹) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  exact closure_minimal (fun z hz => old_positive_quarter_edist_le N hε hx hz)
    (isClosed_le (continuous_const.edist continuous_id) continuous_const) hy

variable {epsilon C A D₀ D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D₀ D}






theorem exists_source_frontier_three_quarter_accuracy
    (S : CounterexampleNeckSegment E) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (_hsmall : epsilon ≤ epsilon₀), ∃ N : ℝ → EpsilonNeck (E.flow.metric E.time),
      (∀ s ∈ Icc S.lower S.upper,
        N s ∈ S.cover.necks ∧ (N s).center = S.path s) ∧
      ∃ l : List ℝ,
        (∀ s ∈ S.lower :: l, s ∈ Icc S.lower S.upper) ∧
        (S.lower :: l).IsChain (fun s t =>
          s < t ∧ S.path t ∈ frontier (N s).carrier ∧
            MapsTo S.path (Ico s t) (N s).carrier) ∧
        (∀ s t, s ∈ S.lower :: l → t ∈ S.lower :: l →
          s < t → S.path t ∈ frontier (N s).carrier →
          MapsTo S.path (Ico s t) (N s).carrier →
          ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
            (N t).center ∈ closure (neckSignedRegion (N s) sigma
              ((N s).epsilon⁻¹ / 2) (N s).epsilon⁻¹) ∧
            neckSignedRegion (N s) sigma ((N s).epsilon⁻¹ / 2)
                (N s).epsilon⁻¹ ⊆ (N t).carrier ∧
            neckSignedRegion (N s) sigma ((N s).epsilon⁻¹ / 2)
                (N s).epsilon⁻¹ ⊆
              (N t).region (-(3 * (N t).epsilon⁻¹ / 4))
                (3 * (N t).epsilon⁻¹ / 4)) := by
  obtain ⟨epsilonQ, hQpos, hQsmall, hQ⟩ :=
    exists_source_frontier_quarter_accuracy S
  obtain ⟨epsilonS, hSpos, hSsmall, hS⟩ :=
    PoincareConjecture.M28.exists_neck_balanced_scale_accuracy.{u}
  let epsilon₀ := min epsilonQ (min epsilonS (1 / 1000))
  have h0pos : 0 < epsilon₀ :=
    lt_min hQpos (lt_min hSpos (by norm_num))
  have h0small : epsilon₀ ≤ (1 / 200 : ℝ) := by
    exact (min_le_right epsilonQ (min epsilonS (1 / 1000))).trans
      ((min_le_left epsilonS (1 / 1000)).trans hSsmall)
  refine ⟨epsilon₀, h0pos, h0small, ?_⟩
  intro hsmall
  obtain ⟨N, hN, l, hlmem, hlchain, hedge⟩ :=
    hQ (hsmall.trans (min_le_left _ _))
  refine ⟨N, hN, l, hlmem, hlchain, ?_⟩
  intro s t hs ht hst hfront hmap
  obtain ⟨sigma, hsigma, hcenter, hcarrier⟩ :=
    hedge s t hs ht hst hfront hmap
  have hsI : s ∈ Icc S.lower S.upper := hlmem s hs
  have htI : t ∈ Icc S.lower S.upper := hlmem t ht
  have hsc : (N s).epsilon = epsilon :=
    (S.cover.neck_epsilon (N s) (hN s hsI).1).trans S.cover_epsilon
  have htc : (N t).epsilon = epsilon :=
    (S.cover.neck_epsilon (N t) (hN t htI).1).trans S.cover_epsilon
  have hOldSmall : (N s).epsilon ≤ (1 / 1000 : ℝ) := by
    calc
      (N s).epsilon = epsilon := hsc
      _ ≤ epsilon₀ := hsmall
      _ ≤ min epsilonS (1 / 1000) := min_le_right _ _
      _ ≤ (1 / 1000 : ℝ) := min_le_right _ _
  have hNewSmall : (N t).epsilon ≤ (1 / 1000 : ℝ) := by
    calc
      (N t).epsilon = epsilon := htc
      _ ≤ epsilon₀ := hsmall
      _ ≤ min epsilonS (1 / 1000) := min_le_right _ _
      _ ≤ (1 / 1000 : ℝ) := min_le_right _ _
  have hScaleOld : (N s).epsilon ≤ epsilonS := by
    calc
      (N s).epsilon = epsilon := hsc
      _ ≤ epsilon₀ := hsmall
      _ ≤ epsilonS :=
        (min_le_right _ _).trans (min_le_left epsilonS (1 / 1000))
  have hScaleNew : (N t).epsilon ≤ epsilonS := by
    calc
      (N t).epsilon = epsilon := htc
      _ ≤ epsilon₀ := hsmall
      _ ≤ epsilonS :=
        (min_le_right _ _).trans (min_le_left epsilonS (1 / 1000))
  have hmeet : ((N s).carrier ∩ (N t).carrier).Nonempty := by
    obtain ⟨y, hy, hy'⟩ := mem_closure_iff.mp hcenter (N t).carrier
      (N t).carrier_open
      ((N t).central_sphere_subset (N t).center_on_central_sphere)
    exact ⟨y, hy'.1, hy⟩
  obtain ⟨_, hscaleUpper⟩ := hS
    (E.flow.slice E.time).carrier (E.flow.metric E.time)
      (E.flow.connection E.time) (N s) (N t) hScaleOld hScaleNew hmeet
  have hnewLower : (999 / 1000 : ℝ) * (N s).scale < (N t).scale := by
    nlinarith only [hscaleUpper, (N s).scale_pos, (N t).scale_pos]
  have hrootLower : (999 / 1000 : ℝ) ≤
      Real.sqrt (1 - (N t).epsilon) := by
    have heps : 0 ≤ 1 - (N t).epsilon := by
      linarith [hNewSmall]
    have hsquare := Real.sq_sqrt heps
    nlinarith [Real.sqrt_nonneg (1 - (N t).epsilon)]
  have hInvNew : 0 < (N t).epsilon⁻¹ := inv_pos.mpr (N t).epsilon_pos
  have hSqrtNew : 0 < Real.sqrt (1 - (N t).epsilon) :=
    Real.sqrt_pos.2 (by linarith [hNewSmall])
  have hTargetPos : 0 <
      ((N t).scale * Real.sqrt (1 - (N t).epsilon)) *
        (3 * (N t).epsilon⁻¹ / 4) := by
    exact mul_pos (mul_pos (N t).scale_pos hSqrtNew)
      (div_pos (mul_pos (by norm_num) hInvNew) (by norm_num))
  have hcoeff : (0.51 : ℝ) * (N s).scale <
      (3 / 4 : ℝ) * ((N t).scale *
        Real.sqrt (1 - (N t).epsilon)) := by
    nlinarith only [hnewLower, hrootLower, (N s).scale_pos,
      (N t).scale_pos, Real.sqrt_nonneg (1 - (N t).epsilon)]
  have htarget :
      (0.51 : ℝ) * (N s).scale * (N s).epsilon⁻¹ <
        ((N t).scale * Real.sqrt (1 - (N t).epsilon)) *
          (3 * (N t).epsilon⁻¹ / 4) := by
    have hmul := mul_lt_mul_of_pos_right hcoeff
      (inv_pos.mpr (N s).epsilon_pos)
    calc
      (0.51 : ℝ) * (N s).scale * (N s).epsilon⁻¹ =
          ((0.51 : ℝ) * (N s).scale) * (N s).epsilon⁻¹ := by ring
      _ < ((3 / 4 : ℝ) * ((N t).scale *
          Real.sqrt (1 - (N t).epsilon))) * (N s).epsilon⁻¹ := hmul
      _ = ((N t).scale * Real.sqrt (1 - (N t).epsilon)) *
          (3 * (N t).epsilon⁻¹ / 4) := by rw [htc, hsc]; ring
  refine ⟨sigma, hsigma, hcenter, hcarrier, ?_⟩
  rcases hsigma with rfl | rfl
  · intro x hx
    have hxold : x ∈ (N s).region ((N s).epsilon⁻¹ / 2)
        (N s).epsilon⁻¹ := by
      simpa only [neckSignedRegion_one] using hx
    by_contra hout
    have hr : 0 < 3 * (N t).epsilon⁻¹ / 4 :=
      div_pos (mul_pos (by norm_num) hInvNew) (by norm_num)
    have hlower0 := (N t).edist_central_lower_of_not_mem_region
      (r := 3 * (N t).epsilon⁻¹ / 4)
      hr (by
        have heps : 0 < (N t).epsilon⁻¹ := inv_pos.mpr (N t).epsilon_pos
        nlinarith) (N t).center_on_central_sphere hout
    have hlower : ENNReal.ofReal
        (((N t).scale * Real.sqrt (1 - (N t).epsilon)) *
          (3 * (N t).epsilon⁻¹ / 4)) ≤
        (E.flow.metric E.time).edist x (N t).center := by
      simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hlower0
    have hupper := neck_positive_quarter_closure_edist_le (N s)
      hOldSmall hxold (by simpa only [neckSignedRegion_one] using hcenter)
    have hupper' : (E.flow.metric E.time).edist x (N t).center ≤
        ENNReal.ofReal ((0.51 : ℝ) * (N s).scale *
          (N s).epsilon⁻¹) := hupper
    have hlt : ENNReal.ofReal ((0.51 : ℝ) * (N s).scale *
        (N s).epsilon⁻¹) < ENNReal.ofReal
        (((N t).scale * Real.sqrt (1 - (N t).epsilon)) *
          (3 * (N t).epsilon⁻¹ / 4)) := by
      apply (ENNReal.ofReal_lt_ofReal_iff hTargetPos).mpr
      exact htarget
    exact (not_lt_of_ge (hlower.trans hupper')) hlt
  · intro x hx
    have hxold : x ∈ (N s).reversed.region
        ((N s).reversed.epsilon⁻¹ / 2) (N s).reversed.epsilon⁻¹ := by
      simpa only [neckSignedRegion_neg_one, EpsilonNeck.reversed_region,
        EpsilonNeck.reversed_epsilon] using hx
    have hcenterRev : (N t).center ∈ closure ((N s).reversed.region
        ((N s).reversed.epsilon⁻¹ / 2) (N s).reversed.epsilon⁻¹) := by
      simpa only [neckSignedRegion_neg_one, EpsilonNeck.reversed_region,
        EpsilonNeck.reversed_epsilon] using hcenter
    by_contra hout
    have hr : 0 < 3 * (N t).epsilon⁻¹ / 4 :=
      div_pos (mul_pos (by norm_num) hInvNew) (by norm_num)
    have hlower0 := (N t).edist_central_lower_of_not_mem_region
      (r := 3 * (N t).epsilon⁻¹ / 4)
      hr (by
        have heps : 0 < (N t).epsilon⁻¹ := inv_pos.mpr (N t).epsilon_pos
        nlinarith) (N t).center_on_central_sphere hout
    have hlower : ENNReal.ofReal
        (((N t).scale * Real.sqrt (1 - (N t).epsilon)) *
          (3 * (N t).epsilon⁻¹ / 4)) ≤
        (E.flow.metric E.time).edist x (N t).center := by
      simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hlower0
    have hupper := neck_positive_quarter_closure_edist_le (N s).reversed
      hOldSmall hxold hcenterRev
    have hupper' : (E.flow.metric E.time).edist x (N t).center ≤
        ENNReal.ofReal ((0.51 : ℝ) * (N s).scale *
          (N s).epsilon⁻¹) := by
      simpa only [EpsilonNeck.reversed_scale, EpsilonNeck.reversed_epsilon] using hupper
    have hlt : ENNReal.ofReal ((0.51 : ℝ) * (N s).scale *
        (N s).epsilon⁻¹) < ENNReal.ofReal
        (((N t).scale * Real.sqrt (1 - (N t).epsilon)) *
          (3 * (N t).epsilon⁻¹ / 4)) := by
      apply (ENNReal.ofReal_lt_ofReal_iff hTargetPos).mpr
      exact htarget
    exact (not_lt_of_ge (hlower.trans hupper')) hlt



end PoincareConjecture.M28.CounterexampleNeckSegment
