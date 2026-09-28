import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckFrontierSphere
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFrontierSelection
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckBalancedDistance
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckBalancedScale
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Reversal

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

private theorem old_positive_quarter_closure_edist_le (N : EpsilonNeck g)
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

private theorem exists_positive_quarter_subset_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g), N.epsilon ≤ epsilon₀ →
        N'.epsilon = N.epsilon →
        N'.center ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
        N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ N'.carrier := by
  obtain ⟨epsilonS, hSpos, hSsmall, hscale⟩ :=
    PoincareConjecture.M28.exists_neck_balanced_scale_accuracy.{u}
  refine ⟨min epsilonS (1 / 1000), lt_min hSpos (by norm_num),
    min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hε heq hcenter x hx
  have hsmall : N.epsilon ≤ 1 / 1000 := hε.trans (min_le_right _ _)
  have hmeet : (N.carrier ∩ N'.carrier).Nonempty := by
    obtain ⟨y, hy, hy'⟩ := mem_closure_iff.mp hcenter N'.carrier
      N'.carrier_open (N'.central_sphere_subset N'.center_on_central_sphere)
    exact ⟨y, hy'.1, hy⟩
  obtain ⟨hsN, hsN'⟩ := hscale M g N.connection N N'
    (hε.trans (min_le_left _ _))
    (heq ▸ hε.trans (min_le_left _ _)) hmeet
  by_contra hout
  have hxout : x ∉ N'.region (-((999 / 1000 : ℝ) * N'.epsilon⁻¹))
      ((999 / 1000 : ℝ) * N'.epsilon⁻¹) := by
    intro hx'
    exact hout hx'.1
  have hlower0 := N'.edist_central_lower_of_not_mem_region
    (r := (999 / 1000 : ℝ) * N'.epsilon⁻¹)
    (mul_pos (by norm_num) (inv_pos.mpr N'.epsilon_pos)) (by
      have hA : 0 < N'.epsilon⁻¹ := inv_pos.mpr N'.epsilon_pos
      nlinarith) N'.center_on_central_sphere hxout
  have hrootLower : (999 / 1000 : ℝ) ≤ Real.sqrt (1 - N'.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - N'.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N'.epsilon)]
  have hcoef : (0.99 : ℝ) ≤ Real.sqrt (1 - N'.epsilon) * (999 / 1000) := by
    nlinarith only [hrootLower]
  have hlower : ENNReal.ofReal ((0.99 : ℝ) * N'.scale * N'.epsilon⁻¹) ≤
      g.edist N'.center x := by
    apply (ENNReal.ofReal_le_ofReal ?_).trans hlower0
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoef N'.scale_pos.le)
      (inv_pos.mpr N'.epsilon_pos).le
    nlinarith only [h]
  have hupper := old_positive_quarter_closure_edist_le N hsmall hx hcenter
  have hlower' : ENNReal.ofReal ((0.99 : ℝ) * N'.scale * N'.epsilon⁻¹) ≤
      g.edist x N'.center := by
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hlower
  have hlt : ENNReal.ofReal ((0.51 : ℝ) * N.scale * N.epsilon⁻¹) <
      ENNReal.ofReal ((0.99 : ℝ) * N'.scale * N'.epsilon⁻¹) := by
    rw [heq]
    have hqpos : 0 < (0.99 : ℝ) * N'.scale * N.epsilon⁻¹ := by
      exact mul_pos (mul_pos (by norm_num) N'.scale_pos)
        (inv_pos.mpr N.epsilon_pos)
    apply (ENNReal.ofReal_lt_ofReal_iff hqpos).mpr
    have hratio : (999 / 1000 : ℝ) * N.scale < N'.scale := by
      nlinarith only [hsN', N.scale_pos, N'.scale_pos]
    have hscale : (0.51 : ℝ) * N.scale < 0.99 * N'.scale := by
      nlinarith only [hratio, N.scale_pos, N'.scale_pos]
    have hmul := mul_lt_mul_of_pos_right hscale
      (inv_pos.mpr N.epsilon_pos)
    nlinarith only [hmul]
  exact (not_lt_of_ge (hlower'.trans hupper)) hlt

variable {epsilon C A D₀ D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D₀ D}

theorem exists_source_frontier_quarter_accuracy (S : CounterexampleNeckSegment E) :
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
                (N s).epsilon⁻¹ ⊆ (N t).carrier) := by
  obtain ⟨epsilonF, hFpos, hFsmall, hF⟩ :=
    exists_frontier_neck_sphere_sides_accuracy.{u}
  obtain ⟨epsilonQ, hQpos, hQsmall, hQ⟩ :=
    exists_positive_quarter_subset_accuracy.{u}
  let epsilon₀ := min epsilonF epsilonQ
  refine ⟨epsilon₀, lt_min hFpos hQpos,
    (min_le_left _ _).trans hFsmall, ?_⟩
  intro hsmall
  obtain ⟨N, hN, l, hlmem, hlchain, _, _⟩ :=
    S.exists_frontier_neck_selection
  refine ⟨N, hN, l, hlmem, hlchain, ?_⟩
  intro s t hs ht hst hfront hmap
  have hsI : s ∈ Icc S.lower S.upper := hlmem s hs
  have htI : t ∈ Icc S.lower S.upper := hlmem t ht
  have hsc : (N s).epsilon = epsilon :=
    (S.cover.neck_epsilon (N s) (hN s hsI).1).trans S.cover_epsilon
  have htc : (N t).epsilon = epsilon :=
    (S.cover.neck_epsilon (N t) (hN t htI).1).trans S.cover_epsilon
  have heq : (N s).epsilon = (N t).epsilon := hsc.trans htc.symm
  have hcenter : (N s).center = S.path s := (hN s hsI).2
  have hcentert : (N t).center = S.path t := (hN t htI).2
  have hcont : ContinuousOn S.path (Icc s t) := by
    apply (S.path_smooth.continuousOn.mono
      (Icc_subset_Icc S.lower_pos.le S.upper_lt_one.le)).mono
    exact Icc_subset_Icc hsI.1 htI.2
  have hout : (N t).center ∉ (N s).carrier := by
    rw [hcentert]
    rw [frontier, (N s).carrier_open.interior_eq] at hfront
    exact hfront.2
  have hfront' : (N t).center ∈ frontier (N s).carrier := by
    rw [hcentert]
    exact hfront
  obtain ⟨sigma, hsigma, v, hv, hlevel, hafter, hcloseT, hcloseO, hcap, -⟩ :=
    hF (E.flow.slice E.time).carrier (E.flow.metric E.time)
      (E.flow.connection E.time) (N s) (N t) heq
      (by
        have hsF : (N s).epsilon ≤ epsilonF := by
          rw [hsc]
          exact hsmall.trans (min_le_left _ _)
        simpa only [hsc] using hsF) S.path s t hst
      hcont hcenter.symm hcentert.symm hmap hfront'
  have hsQ : (N s).epsilon ≤ epsilonQ := by
    rw [hsc]
    exact hsmall.trans (min_le_right _ _)
  have hquarterData :
      (N t).center ∈ closure (neckSignedRegion (N s) sigma
        ((N s).epsilon⁻¹ / 2) (N s).epsilon⁻¹) ∧
      neckSignedRegion (N s) sigma ((N s).epsilon⁻¹ / 2)
        (N s).epsilon⁻¹ ⊆ (N t).carrier := by
    rcases hsigma with rfl | rfl
    · have hcloseQ : (N t).center ∈ closure
          ((N s).region ((N s).epsilon⁻¹ / 2) (N s).epsilon⁻¹) := by
        have hcloseRaw : (N t).center ∈ closure
            (neckSignedRegion (N s) 1
              (255 * (N s).epsilon⁻¹ / 256) (N s).epsilon⁻¹) := by
          simpa only [show (255 : ℝ) / 256 = 255 / 256 by rfl] using hcloseO
        have hsubset :
            (N s).region (255 * (N s).epsilon⁻¹ / 256)
                (N s).epsilon⁻¹ ⊆
              (N s).region ((N s).epsilon⁻¹ / 2) (N s).epsilon⁻¹ := by
          intro x hx
          have hA : 0 < (N s).epsilon⁻¹ := inv_pos.mpr (N s).epsilon_pos
          exact ⟨hx.1, by linarith [hx.2.1, hA], hx.2.2⟩
        exact closure_mono hsubset (by
          simpa only [neckSignedRegion_one] using hcloseRaw)
      refine ⟨?_, ?_⟩
      · simpa only [neckSignedRegion_one] using hcloseQ
      · simpa only [neckSignedRegion_one] using
          (hQ (N s) (N t) hsQ heq.symm hcloseQ)
    · have hcloseQ : (N t).center ∈ closure
          ((N s).reversed.region ((N s).reversed.epsilon⁻¹ / 2)
            (N s).reversed.epsilon⁻¹) := by
        have hcloseRaw : (N t).center ∈ closure
            (neckSignedRegion (N s) (-1)
              (255 * (N s).epsilon⁻¹ / 256) (N s).epsilon⁻¹) := hcloseO
        have hcloseN : (N t).center ∈ closure
            ((N s).region (-((N s).epsilon⁻¹))
              (-((N s).epsilon⁻¹ / 2))) := by
          have hsubset :
              (N s).region (-((N s).epsilon⁻¹))
                  (-((255 * (N s).epsilon⁻¹ / 256))) ⊆
                (N s).region (-((N s).epsilon⁻¹))
                  (-((N s).epsilon⁻¹ / 2)) := by
            intro x hx
            have hA : 0 < (N s).epsilon⁻¹ := inv_pos.mpr (N s).epsilon_pos
            exact ⟨hx.1, hx.2.1, by linarith [hx.2.2, hA]⟩
          apply closure_mono hsubset
          simpa only [neckSignedRegion_neg_one] using hcloseRaw
        simpa only [EpsilonNeck.reversed_region,
          EpsilonNeck.reversed_epsilon] using hcloseN
      have hQrev := hQ (N s).reversed (N t) hsQ
        (by simpa only [EpsilonNeck.reversed_epsilon] using heq.symm) hcloseQ
      refine ⟨?_, ?_⟩
      · simpa only [neckSignedRegion_neg_one, EpsilonNeck.reversed_region,
          EpsilonNeck.reversed_epsilon] using hcloseQ
      · simpa only [neckSignedRegion_neg_one, EpsilonNeck.reversed_region,
          EpsilonNeck.reversed_epsilon] using hQrev
  have hcloseQuarter := hquarterData.1
  have hquarter := hquarterData.2
  refine ⟨sigma, hsigma, ?_, ?_⟩
  · exact hcloseQuarter
  · exact hquarter

end PoincareConjecture.M28.CounterexampleNeckSegment
