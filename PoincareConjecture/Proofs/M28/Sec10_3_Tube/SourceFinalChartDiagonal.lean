import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallFreshCapture
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallRawStage
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallScalarLimit
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFamilyScales
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.RelativeCompactMetric
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.UniformCompactScalar
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 3200000 in

theorem exists_source_final_chart_diagonal
    {epsilon C A : ℝ}
    {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
      ((n : ℝ) + 1) ((n : ℝ) + 1)}
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (D0 : LeviCivitaData G.limitMetric)
      (q : ℕ → G.limitCarrier.carrier) (sigma : ℕ → ℕ), StrictMono sigma →
    let nu := fun k => W.high_index (G.subsequence (sigma k))
    let Q := fun k => (E (nu k + H.shift)).flow.scalar
      ⟨(E (nu k + H.shift)).time, (E (nu k + H.shift)).basepoint⟩
    let R := fun i => D0.scalarCurvature (q i)
    let delta := fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 2)
    ∀ J : ∀ _i k : ℕ, GeneralizedStrongNeck
      (E (nu k + H.shift)).flow (E (nu k + H.shift)).time epsilon,
    (∀ i k, (J i k).center = (G.embedding (sigma k) (q i)).val.val) →
    (∀ i, 0 < R i) →
    (∀ i, Tendsto (fun k => Q k * (J i k).scale ^ 2) atTop (𝓝 (R i)⁻¹)) →
    (∀ i, ∃ j : ℕ, ∀ᶠ k in atTop, j ≤ sigma k ∧
      ∀ x ∈ (J i k).carrier,
        |((J i k).coordinate_inverse x).2| ≤ 2 * epsilon⁻¹ / 3 →
        x ∈ (fun y => (G.embedding (sigma k) y).val.val) '' G.exhaustion j) →
    ∃ j kappa : ℕ → ℕ, StrictMono kappa ∧ ∀ i : ℕ,
      let k := kappa i
      let e := H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
        W.high_index G (sigma k)
      q i ∈ G.exhaustion (j i) ∧
      j i + 1 ≤ sigma k ∧
      |R i * (Q k * (J i k).scale ^ 2) - 1| ≤ delta i ∧
      2 * ((i : ℝ) + 1) / R i ≤ Q k ∧
      ((i : ℝ) + 1) ≤ ((J i k).scale⁻¹) ^ 2 ∧
      (∀ x ∈ closure (G.exhaustion (j i)),
        ∀ v : TangentSpace (𝓡 3) x,
          (1 + delta i)⁻¹ * G.limitMetric.inner x v v ≤
            (H.tubeCriticalMetric W.tube W.radius (nu k)).inner
              (G.embedding (sigma k) x)
              (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma k)) x v)
              (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma k)) x v) ∧
          (H.tubeCriticalMetric W.tube W.radius (nu k)).inner
            (G.embedding (sigma k) x)
            (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma k)) x v)
            (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma k)) x v) ≤
              (1 + delta i) * G.limitMetric.inner x v v) ∧
      (∀ x ∈ closure (G.exhaustion (j i)),
        |(E (nu k + H.shift)).flow.scalar
            ⟨(E (nu k + H.shift)).time,
              (G.embedding (sigma k) x).val.val⟩ / Q k -
            D0.scalarCurvature x| ≤ 1) ∧
      e.symm (J i k).center = q i ∧
      (∀ x ∈ (J i k).carrier,
        |((J i k).coordinate_inverse x).2| ≤ 2 * epsilon⁻¹ / 3 →
                  x ∈ e.target ∧ e.symm x ∈ G.exhaustion (j i) ∧ e (e.symm x) = x) := by
  classical
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q sigma hsigma nu Q R delta J hcenter hpositive hscale hcapture
  let raw (k : ℕ) : G.limitCarrier.carrier →
      ((E (nu k + H.shift)).flow.slice (E (nu k + H.shift)).time).carrier :=
    fun y => (G.embedding (sigma k) y).val.val
  have hRpositive (i : ℕ) : 0 < R i := hpositive i
  have hdelta (i : ℕ) : 0 < delta i := by dsimp [delta]; positivity
  have hdeltaHalf (i : ℕ) : delta i ≤ (1 / 2 : ℝ) := by
    change 1 / ((i : ℝ) + 2) ≤ (1 / 2 : ℝ)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (i : ℝ) + 2)).2
    nlinarith only [Nat.cast_nonneg (α := ℝ) i]
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun j => subset_closure.trans (G.exhaustion_step j))
  choose j0 hj0 using hcapture
  have hqstage : ∀ i : ℕ, ∃ j : ℕ, q i ∈ G.exhaustion j := by
    intro i
    have hq : q i ∈ ⋃ j, G.exhaustion j := by
      rw [G.exhaustion_covers]
      exact mem_univ _
    exact mem_iUnion.mp hq
  choose jq hjq using hqstage
  let j := fun i => max (j0 i) (jq i)
  have hqj (i : ℕ) : q i ∈ G.exhaustion (j i) :=
    hmono (le_max_right (j0 i) (jq i)) (hjq i)
  let K := fun i => closure (G.exhaustion (j i))
  have hcompact (i : ℕ) : IsCompact (K i) := G.exhaustion_compactClosure (j i)
  let Cap : ℕ → ℕ → Prop := fun i k => ∀ x ∈ (J i k).carrier,
    |((J i k).coordinate_inverse x).2| ≤ 2 * epsilon⁻¹ / 3 →
      x ∈ raw k '' G.exhaustion (j i)
  have hcap (i : ℕ) : ∀ᶠ k in atTop, Cap i k := by
    refine (hj0 i).mono ?_
    intro k hk x hx hheight
    have hsubset : G.exhaustion (j0 i) ⊆ G.exhaustion (j i) :=
      hmono (le_max_left (j0 i) (jq i))
    have hsource : ∀ x ∈ (J i k).carrier,
        |((J i k).coordinate_inverse x).2| ≤ 2 * epsilon⁻¹ / 3 →
          x ∈ raw k '' G.exhaustion (j0 i) := hk.2
    exact image_mono (f := raw k) hsubset (hsource x hx hheight)
  let Rel := fun i k => ∀ x ∈ K i, ∀ v : TangentSpace (𝓡 3) x,
    (1 + delta i)⁻¹ * G.limitMetric.inner x v v ≤
      (H.tubeCriticalMetric W.tube W.radius (nu k)).inner
        (G.embedding (sigma k) x)
        (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma k)) x v)
        (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma k)) x v) ∧
    (H.tubeCriticalMetric W.tube W.radius (nu k)).inner
      (G.embedding (sigma k) x)
      (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma k)) x v)
      (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma k)) x v) ≤
        (1 + delta i) * G.limitMetric.inner x v v
  have hrel (i : ℕ) : ∀ᶠ k in atTop, Rel i k :=
    hsigma.tendsto_atTop.eventually
      (G.eventually_compact_relative_inner_bounds (K i) (hcompact i) (delta i) (hdelta i))
  let Sca := fun i k => ∀ x ∈ K i,
    |(E (nu k + H.shift)).flow.scalar
        ⟨(E (nu k + H.shift)).time, (G.embedding (sigma k) x).val.val⟩ / Q k -
      D0.scalarCurvature x| ≤ 1
  let D : ∀ k, LeviCivitaData
      (H.tubeCriticalMetric W.tube W.radius (W.high_index k)) := fun k =>
    Classical.choice (exists_leviCivitaData
      (H.tubeCriticalMetric W.tube W.radius (W.high_index k)))
  have hsca (i : ℕ) : ∀ᶠ k in atTop, Sca i k := by
    have hlim := G.tendstoUniformlyOn_scalarCurvature D D0 (K i) (hcompact i)
    have htail := Metric.tendstoUniformlyOn_iff.mp hlim (1 : ℝ) zero_lt_one
    filter_upwards [hsigma.tendsto_atTop.eventually htail] with k hk
    intro x hx
    have h := (hk x hx).le
    rw [H.tubeCritical_scalar_eq W.tube W.radius (nu k)
      (D (G.subsequence (sigma k))) (G.embedding (sigma k) x)] at h
    simpa only [Real.dist_eq, abs_sub_comm] using h
  have hnu : StrictMono nu := W.high_index_strictMono.comp
    (G.subsequence_strictMono.comp hsigma)
  have hQ : Tendsto Q atTop atTop := H.base_scalar_tendsto_atTop.comp hnu.tendsto_atTop
  have hscaleTest (i : ℕ) : ∀ᶠ k in atTop,
      |R i * (Q k * (J i k).scale ^ 2) - 1| ≤ delta i := by
    have hlim : Tendsto (fun k => R i * (Q k * (J i k).scale ^ 2)) atTop
        (𝓝 (R i * (R i)⁻¹)) := tendsto_const_nhds.mul (hscale i)
    rw [mul_inv_cancel₀ (hRpositive i).ne'] at hlim
    filter_upwards [Metric.tendsto_nhds.mp hlim (delta i) (hdelta i)] with k hk
    exact (by simpa only [Real.dist_eq] using hk :
      |R i * (Q k * (J i k).scale ^ 2) - 1| < delta i).le
  let Row : ℕ → ℕ → Prop := fun i k =>
      j i + 1 ≤ sigma k ∧
      |R i * (Q k * (J i k).scale ^ 2) - 1| ≤ delta i ∧
      2 * ((i : ℝ) + 1) / R i ≤ Q k ∧ Rel i k ∧ Sca i k ∧ Cap i k
  have hrow (i : ℕ) : ∀ᶠ k in atTop, Row i k := by
    exact (hsigma.tendsto_atTop.eventually (eventually_ge_atTop (j i + 1))).and
      ((hscaleTest i).and
        ((hQ.eventually_ge_atTop (2 * ((i : ℝ) + 1) / R i)).and
          ((hrel i).and ((hsca i).and (hcap i)))))
  have hselection : ∃ kappa : ℕ → ℕ,
      StrictMono kappa ∧ ∀ k i, i ≤ k → Row i (kappa k) :=
    Poincare.exists_strictMono_forall_le_of_eventually (P := Row) hrow
  let kappa : ℕ → ℕ := Classical.choose hselection
  have hkappa : StrictMono kappa := (Classical.choose_spec hselection).1
  have hselected : ∀ k i, i ≤ k → Row i (kappa k) :=
    (Classical.choose_spec hselection).2
  refine ⟨j, kappa, hkappa, ?_⟩
  intro i k e
  have hrowi : Row i k := hselected i i le_rfl
  have hguard : j i + 1 ≤ sigma k := hrowi.1
  have hs : |R i * (Q k * (J i k).scale ^ 2) - 1| ≤ delta i := hrowi.2.1
  have hbase : 2 * ((i : ℝ) + 1) / R i ≤ Q k := hrowi.2.2.1
  have hm : Rel i k := hrowi.2.2.2.1
  have hscalar : Sca i k := hrowi.2.2.2.2.1
  have hcore : Cap i k := hrowi.2.2.2.2.2
  have hgrowth : ((i : ℝ) + 1) ≤ ((J i k).scale⁻¹) ^ 2 := by
    have hs2 : 0 < (J i k).scale ^ 2 := sq_pos_of_pos (J i k).scale_pos
    have hupper : R i * (Q k * (J i k).scale ^ 2) ≤ 2 := by
      have h : R i * (Q k * (J i k).scale ^ 2) - 1 ≤ delta i :=
        (abs_le.mp hs).2
      linarith only [h, hdeltaHalf i]
    have hbase' : 2 * ((i : ℝ) + 1) ≤ Q k * R i :=
      (div_le_iff₀ (hRpositive i)).1 hbase
    have hmul := mul_le_mul_of_nonneg_right hbase' hs2.le
    have hprod : ((i : ℝ) + 1) * (J i k).scale ^ 2 ≤ 1 := by
      nlinarith only [hupper, hmul]
    have h := (le_div_iff₀ hs2).2 hprod
    simpa only [one_div, inv_pow] using h
  have hjk : j i ≤ sigma k := (Nat.le_succ (j i)).trans hguard
  have hqsource : q i ∈ e.source := by
    rw [H.regularRawStageDiffeomorph_source]
    exact hmono hjk (hqj i)
  have hcenterInverse : e.symm (J i k).center = q i := by
    have hc : (J i k).center = e (q i) := hcenter i k
    rw [hc]
    exact e.left_inv hqsource
  have hcoreInverse : ∀ x ∈ (J i k).carrier,
      |((J i k).coordinate_inverse x).2| ≤ 2 * epsilon⁻¹ / 3 →
      x ∈ e.target ∧ e.symm x ∈ G.exhaustion (j i) ∧ e (e.symm x) = x := by
    intro x hx hheight
    obtain ⟨y, hy, hxy⟩ := hcore x hx hheight
    have hysource : y ∈ e.source := by
      rw [H.regularRawStageDiffeomorph_source]
      exact hmono hjk hy
    have hexy : e y = x := hxy
    have hxtarget : x ∈ e.target := hexy ▸ e.map_source hysource
    have hleft : e.symm x = y := by
      rw [← hexy]
      exact e.left_inv hysource
    exact ⟨hxtarget, hleft.symm ▸ hy, e.right_inv hxtarget⟩
  exact ⟨hqj i, hguard, hs, hbase, hgrowth, hm, hscalar, hcenterInverse, hcoreInverse⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
