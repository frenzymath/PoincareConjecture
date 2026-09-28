import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartContactTube
import PoincareConjecture.Proofs.M14.Sec6_3_PrefixMinimality

set_option autoImplicit false

open Set Filter
open scoped Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point}

theorem finiteValueDomain_of_fullPath_through
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (p : M14BackwardPath G T a b x y)
    (hp : M14IsMinimizing p) (q : M14BackwardPath G T a b x y)
    {c : ℝ} (hc : c ∈ Ioo a b) :
    M14FiniteValueDomain G T a c x (q.curve c) := by
  refine ⟨⟨_, action_mem_actionSet (prefixPath q c hc.1 hc.2.le)⟩,
    ⟨M14BackwardLAction G p - ∫ s in c..b, M14BackwardLIntegrand G q s, ?_⟩⟩
  rintro A ⟨r, rfl⟩
  have hle := minimizing_action_le_prefix_add_tail hM12 p hp q r hc.2
  linarith

theorem exists_pastTube_finiteValueDomain
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (p : M14BackwardPath G T a b x y)
    (hp : M14IsMinimizing p) :
    ∃ N : Set G.Point, IsOpen N ∧ y ∈ N ∧
      N ⊆ {q | a < T - G.spacetime.timeFunction q} ∧
      ∀ q ∈ N, T - G.spacetime.timeFunction q < b →
        M14FiniteValueDomain G T a (T - G.spacetime.timeFunction q) x q := by
  obtain ⟨N, hN, hy, hNa, hpaths⟩ := exists_pastTube_sameEndpointPaths hM12 p
  refine ⟨N, hN, hy, hNa, ?_⟩
  intro q hq hqb
  obtain ⟨r, hr⟩ := hpaths q hq hqb
  have hf := finiteValueDomain_of_fullPath_through hM12 p hp r ⟨hNa hq, hqb⟩
  simpa only [hr] using hf

theorem reducedLengthAt_le_action_of_pastFinite
    {q : G.Point} (r : M14BackwardPath G T a b x q) {N : Set G.Point}
    (hN : N ∈ 𝓝 q) (hf : ContinuousAt (M14ReducedLengthAt G T a x) q)
    (hfinite : ∀ z ∈ N, T - G.spacetime.timeFunction z < b →
      M14FiniteValueDomain G T a (T - G.spacetime.timeFunction z) x z) :
    M14ReducedLengthAt G T a x q ≤ M14BackwardLAction G r / (2 * Real.sqrt b) := by
  have hb : 0 < b := r.tau_nonneg.trans_lt r.tau_lt
  have ht : Tendsto (fun d : ℝ => b - d) (𝓝[>] 0) (𝓝 b) := by
    have ht' : Continuous (fun d : ℝ => b - d) := continuous_const.sub continuous_id
    simpa only [sub_zero] using ht'.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have htI : Tendsto (fun d : ℝ => b - d) (𝓝[>] 0) (𝓝[Icc a b] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr r.tau_lt)] with d hd
    exact ⟨by linarith [hd.2], by linarith [hd.1]⟩
  have hcurve : Tendsto (fun d : ℝ => r.curve (b - d)) (𝓝[>] 0) (𝓝 q) := by
    simpa only [Function.comp_def, r.curve_end] using
      (r.curve_continuous b ⟨r.tau_lt.le, le_rfl⟩).tendsto.comp htI
  have hnum : Tendsto (fun d : ℝ => ∫ s in a..(b - d), M14BackwardLIntegrand G r s)
      (𝓝[>] 0) (𝓝 (M14BackwardLAction G r)) := by
    simpa only [one_mul, M14BackwardLAction, M14BackwardLIntegrand] using
      tendsto_integral_upper_from_left r.tau_lt r.action_integrable zero_lt_one
  have hden : Tendsto (fun d : ℝ => 2 * Real.sqrt (b - d)) (𝓝[>] 0)
      (𝓝 (2 * Real.sqrt b)) :=
    tendsto_const_nhds.mul (Real.continuous_sqrt.continuousAt.tendsto.comp ht)
  have hlimit := hnum.div hden (mul_pos zero_lt_two (Real.sqrt_pos.mpr hb)).ne'
  apply le_of_tendsto_of_tendsto (hf.tendsto.comp hcurve) hlimit
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr r.tau_lt), hcurve.eventually hN] with d hd hdN
  have hca : a < b - d := by linarith [hd.2]
  have hcb : b - d < b := by linarith [hd.1]
  have hclock := r.curve_time (b - d) ⟨hca.le, hcb.le⟩
  have hfin := hfinite (r.curve (b - d)) hdN (by rw [hclock, sub_sub_cancel]; exact hcb)
  rw [hclock, sub_sub_cancel] at hfin
  have hle := actionValue_le_action hfin (prefixPath r (b - d) hca hcb.le)
  change M14ReducedLengthAt G T a x (r.curve (b - d)) ≤
    (∫ s in a..(b - d), M14BackwardLIntegrand G r s) / (2 * Real.sqrt (b - d))
  unfold M14ReducedLengthAt M14ReducedLengthValue
  rw [hclock, sub_sub_cancel]
  simpa only [M14BackwardLAction, M14BackwardLIntegrand, prefixPath, restrictPath] using
    div_le_div_of_nonneg_right hle (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (Real.sqrt_nonneg (b - d)))

theorem actionSet_bddBelow_of_pastFinite {q : G.Point} {N : Set G.Point}
    (hb : 0 < b) (hN : N ∈ 𝓝 q) (hf : ContinuousAt (M14ReducedLengthAt G T a x) q)
    (hfinite : ∀ z ∈ N, T - G.spacetime.timeFunction z < b →
      M14FiniteValueDomain G T a (T - G.spacetime.timeFunction z) x z) :
    BddBelow (M14ActionSet G T a b x q) := by
  refine ⟨(2 * Real.sqrt b) * M14ReducedLengthAt G T a x q, ?_⟩
  rintro A ⟨r, rfl⟩
  have hle := reducedLengthAt_le_action_of_pastFinite r hN hf hfinite
  simpa only [mul_comm] using (le_div_iff₀ (mul_pos zero_lt_two (Real.sqrt_pos.mpr hb))).mp hle

end PoincareConjecture.M14
