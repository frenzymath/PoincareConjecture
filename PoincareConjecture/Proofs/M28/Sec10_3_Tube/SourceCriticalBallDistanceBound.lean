import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallPathCapture
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSpherePaths
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CapturedPathDistance











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 3200000 in





theorem exists_retained_positive_distance_bound_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H),
        epsilon ≤ epsilon0 →
        ∀ (G : RegularPointedMetricConvergence
          (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
          (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (_D0 : LeviCivitaData G.limitMetric)
            (L : EpsilonNeck G.limitMetric) (j : ℕ), L.center = G.base →
            L.carrier ⊆ G.exhaustion j →
            ∀ (sigma : ℕ → ℕ), StrictMono sigma →
            ∀ (f : ℕ → UnitTwoSphere → ℝ),
              (∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k)) →
              (∀ k z, |f k z| < epsilon⁻¹ / 32) →
              (∀ k, (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                W.high_index G (sigma k)) '' L.central_sphere =
                  range (fun z =>
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                      (z, f k z))) →
              ∀ q : G.limitCarrier.carrier,
                (∀ᶠ k in atTop, (G.embedding (sigma k) q).val.val ∉
                  ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                    (f k)) →
                G.limitMetric.edist G.base q ≤ ENNReal.ofReal
                  ((4 * standardSpherePathCeiling) * L.scale + 2 * W.radius) := by
  obtain ⟨epsilon0, hpos, hsmall, hsuffix⟩ :=
    exists_retained_short_suffix_capture_accuracy P
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : G.limitCarrier.carrier → Type _) :=
    ⟨G.limitMetric.toRiemannianMetric⟩
  intro D0 L j hLcenter hLstage sigma hsigma f hf hbound hgraphs q hside
  obtain ⟨ell, hpaths⟩ := hsuffix H W hepsilon G D0 q L j hLcenter hLstage
    sigma hsigma f hf hbound hgraphs hside
  obtain ⟨jq, hqstage⟩ : ∃ jq, q ∈ G.exhaustion jq := by
    have hq : q ∈ ⋃ i, G.exhaustion i := by rw [G.exhaustion_covers]; exact mem_univ _
    exact mem_iUnion.mp hq
  obtain ⟨k, hkpath, hkcompare, hkq⟩ := (hpaths.and
    ((hsigma.tendsto_atTop.eventually
      (G.eventually_edist_le_twice_captured_path_length ell)).and
        (hsigma.tendsto_atTop.eventually (eventually_ge_atTop jq)))).exists
  obtain ⟨_, hkj, a, ha, gamma, h0, h1, hgamma, hcapture, hlength⟩ := hkpath
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun i => subset_closure.trans (G.exhaustion_step i))
  have hdist := hkcompare a q
    (hmono hkj (hLstage (L.central_sphere_subset ha))) (hmono hkq hqstage)
    gamma 0 1 zero_le_one hgamma h0 h1 hcapture
  obtain ⟨alpha, ha0, ha1, halpha, _, halength, _, _⟩ :=
    exists_central_sphere_shortcut L (hLcenter ▸ L.center_on_central_sphere) ha
  have hsphere : G.limitMetric.edist G.base a <
      ENNReal.ofReal ((4 * standardSpherePathCeiling) * L.scale) :=
    (Manifold.riemannianEDist_le_pathELength halpha.contMDiffOn ha0 ha1 zero_le_one).trans_lt
      halength
  have hpositive : 0 < (4 * standardSpherePathCeiling) * L.scale :=
    mul_pos (mul_pos (by norm_num) standardSpherePathCeiling_pos) L.scale_pos
  calc
    G.limitMetric.edist G.base q ≤ G.limitMetric.edist G.base a + G.limitMetric.edist a q :=
      Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal ((4 * standardSpherePathCeiling) * L.scale) +
        2 * ENNReal.ofReal W.radius :=
      add_le_add hsphere.le (hdist.trans (mul_le_mul_right hlength.le 2))
    _ = ENNReal.ofReal ((4 * standardSpherePathCeiling) * L.scale + 2 * W.radius) := by
      rw [ENNReal.ofReal_add hpositive.le (mul_nonneg (by norm_num) W.radius_pos.le),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

end PoincareConjecture.M28.CounterexampleNeckFamily
