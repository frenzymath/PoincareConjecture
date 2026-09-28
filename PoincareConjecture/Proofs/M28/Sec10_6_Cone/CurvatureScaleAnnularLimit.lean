import PoincareConjecture.Proofs.M28.Sec10_6_Cone.ChordConeAnnulus
import PoincareConjecture.Proofs.M28.Mathlib.CompactPrefixRay
import PoincareConjecture.Proofs.M28.Mathlib.CurvatureScaleRadiusBuffer
import Mathlib.Topology.Algebra.Order.Field












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal

namespace PoincareConjecture.M28






theorem exists_curvatureScale_annular_limit
    {S X L : Type*} [MetricSpace X] [MetricSpace L] [CompactSpace L]
    (E : UniformSpace.Completion X) (x : ℕ → S → X) (q : ℕ → X) (R : ℕ → ℝ)
    (hRpos : ∀ i, 0 < R i) (hRtop : Tendsto R atTop atTop)
    {a m : ℝ} (hm : 0 < m) (ham : a ≤ m)
    (hcenter : Tendsto
      (fun i => Real.sqrt (R i) * dist (q i : UniformSpace.Completion X) E)
      atTop (𝓝 m))
    (hshort : ∀ᶠ i in atTop, ∀ u : S,
      Real.sqrt (R i) * dist (x i u) (q i) ≤ 3 * a / 64)
    (d : S → S → ℝ≥0∞) (hdfinite : ∀ u v : S, d u v ≠ ⊤)
    (hsource : ∀ u v : S, Tendsto
      (fun i => Real.sqrt (R i) * dist (x i u) (x i v))
      atTop (𝓝 (d u v).toReal))
    (htriangle : ∀ z w v : L, ∀ r s t : ℝ, 0 < r → 0 < s → 0 < t →
      chordConeDistance r t (dist z v) ≤
        chordConeDistance r s (dist z w) + chordConeDistance s t (dist w v)) :
    letI := chordConeAnnulusMetric (half_pos hm)
      (show m / 2 ≤ 2 * m by linarith only [hm]) htriangle
    ∀ F : ℝ → X → ChordConeAnnulus L (m / 2) (2 * m),
      (∀ (s : ℝ) (p : X),
        dist (p : UniformSpace.Completion X) E / s ∈ Icc (m / 2) (2 * m) →
          ((F s p).2 : ℝ) = dist (p : UniformSpace.Completion X) E / s) →
      (∀ eta : ℝ, 0 < eta → ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
        ∀ p : X, dist (p : UniformSpace.Completion X) E / s ∈ Icc (m / 2) (2 * m) →
        ∀ q : X, dist (q : UniformSpace.Completion X) E / s ∈ Icc (m / 2) (2 * m) →
          0 ≤ dist (F s p) (F s q) - dist p q / s ∧
            dist (F s p) (F s q) - dist p q / s < eta) →
      ∃ j : S → ChordConeAnnulus L (m / 2) (2 * m),
        (∀ u : S, Tendsto (fun i => F ((Real.sqrt (R i))⁻¹) (x i u))
          (hyperfilter ℕ : Filter ℕ) (𝓝 (j u))) ∧
        (∀ u v : S, edist (j u) (j v) = d u v) ∧
        ∀ u : S, ((j u).2 : ℝ) ∈ Icc (3 * m / 4) (5 * m / 4) := by
  classical
  have hab : m / 2 ≤ 2 * m := by linarith only [hm]
  let := chordConeAnnulusMetric (half_pos hm) hab htriangle
  let : CompactSpace (ChordConeAnnulus L (m / 2) (2 * m)) := chordConeAnnulus_compact
  intro F hFradius hFdistortion
  let scale (i : ℕ) : ℝ := (Real.sqrt (R i))⁻¹
  have hscale : Tendsto scale atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_inv_atTop_nhdsGT_zero.comp (Real.tendsto_sqrt_atTop.comp hRtop)
  have hbuffer : ∀ᶠ i in atTop, ∀ u : S,
      dist (x i u : UniformSpace.Completion X) E / scale i ∈
        Icc (3 * m / 4) (5 * m / 4) :=
    eventually_curvatureScale_radius_mem_Icc E x q R hRpos hm ham hcenter hshort
  have hmemAnnulus {r : ℝ} (hr : r ∈ Icc (3 * m / 4) (5 * m / 4)) :
      r ∈ Icc (m / 2) (2 * m) := by
    constructor <;> linarith only [hr.1, hr.2, hm]
  have hannulus : ∀ᶠ i in atTop, ∀ u : S,
      dist (x i u : UniformSpace.Completion X) E / scale i ∈
        Icc (m / 2) (2 * m) :=
    hbuffer.mono fun _ hi u => hmemAnnulus (hi u)
  let f (i : ℕ) (u : S) := F (scale i) (x i u)
  have htarget : ∀ u v : S, Tendsto (fun i => dist (f i u) (f i v))
      atTop (𝓝 (d u v).toReal) := by
    intro u v
    have herror : Tendsto
        (fun i => dist (f i u) (f i v) -
          Real.sqrt (R i) * dist (x i u) (x i v)) atTop (𝓝 (0 : ℝ)) := by
      apply Metric.tendsto_nhds.mpr
      intro epsilon hepsilon
      filter_upwards [hscale.eventually (hFdistortion epsilon hepsilon), hannulus]
        with i hdist hannulus
      have hpair := hdist (x i u) (hannulus u) (x i v) (hannulus v)
      have hnonneg :
          0 ≤ dist (f i u) (f i v) - Real.sqrt (R i) * dist (x i u) (x i v) := by
        simpa only [f, scale, div_inv_eq_mul, mul_comm] using hpair.1
      have hsmall :
          dist (f i u) (f i v) - Real.sqrt (R i) * dist (x i u) (x i v) < epsilon := by
        simpa only [f, scale, div_inv_eq_mul, mul_comm] using hpair.2
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
      exact hsmall
    simpa only [sub_add_cancel, zero_add] using herror.add (hsource u v)
  have hcompact : ∀ u ∈ (univ : Set S),
      ∃ K : Set (ChordConeAnnulus L (m / 2) (2 * m)), IsCompact K ∧
        ∀ᶠ i in atTop, f i u ∈ K := by
    intro u _hu
    exact ⟨univ, isCompact_univ, Eventually.of_forall fun _ => mem_univ _⟩
  obtain ⟨j, hj, hjdist⟩ := exists_pointwise_metric_limit_of_eventually_compact
    (univ : Set S) f (fun u v => (d u v).toReal) hcompact
      (fun u _hu v _hv => htarget u v)
  have hradiusBuffer : ∀ᶠ i in atTop, ∀ u : S,
      ((f i u).2 : ℝ) ∈ Icc (3 * m / 4) (5 * m / 4) := by
    filter_upwards [hbuffer] with i hi
    intro u
    change ((F (scale i) (x i u)).2 : ℝ) ∈ _
    rw [hFradius (scale i) (x i u) (hmemAnnulus (hi u))]
    exact hi u
  refine ⟨j, fun u => hj u (mem_univ u), ?_, ?_⟩
  · intro u v
    rw [edist_dist, hjdist u (mem_univ u) v (mem_univ v),
      ENNReal.ofReal_toReal (hdfinite u v)]
  · intro u
    have hradiusLimit : Tendsto (fun i => ((f i u).2 : ℝ))
        (hyperfilter ℕ : Filter ℕ) (𝓝 ((j u).2 : ℝ)) :=
      ((chordConeAnnulus_radius_lipschitz (half_pos hm) hab htriangle).continuous.tendsto
        (j u)).comp (hj u (mem_univ u))
    exact isClosed_Icc.mem_of_tendsto hradiusLimit
      ((hradiusBuffer.mono fun _ hi => hi u).filter_mono Nat.hyperfilter_le_atTop)

end PoincareConjecture.M28
