import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallFrontierReachability
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeScaleBudget

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

structure CriticalBallSpine
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (k : ℕ) where
  gamma : ∀ t : ℝ, t < A1 → H.tubeCriticalRegion T A1 k
  radial : ∀ (t : ℝ) (ht : t ∈ Ico (0 : ℝ) A1),
    ((H.tubeMetric T k).edist (H.tubeBase T k)
      ((gamma t ht.2 : H.tubeCriticalRegion T A1 k) : (T k).carrierOpen)).toReal = t
  segment : ∀ {s t : ℝ}, (hs : s ∈ Ico (0 : ℝ) A1) → (ht : t ∈ Ico s A1) →
    ((H.tubeCriticalMetric T A1 k).edist
      (gamma s hs.2) (gamma t ht.2)).toReal ≤ t - s
  frontier : ∀ {r : ℝ}, r < A1 →
    ∃ t : ℝ, t ∈ Ico (0 : ℝ) A1 ∧ r < t
  near : ∀ (i : ℤ), i ∈ (T k).chain.shape.active →
    ∀ (x : H.tubeCriticalRegion T A1 k),
      (x : (T k).carrierOpen).val ∈ ((T k).chain.neck i).carrier →
      ∃ t : ℝ, ∃ ht : t ∈ Ico (0 : ℝ) A1,
        ((H.tubeMetric T k).edist (x : (T k).carrierOpen)
          ((gamma t ht.2 : H.tubeCriticalRegion T A1 k) : (T k).carrierOpen)).toReal ≤
            (5858 / 1000 : ℝ) * H.tubeNodeScale T k i ∧
        ((H.tubeCriticalMetric T A1 k).edist x (gamma t ht.2)).toReal ≤
            (5858 / 1000 : ℝ) * H.tubeNodeScale T k i

theorem criticalBall_access_of_spine
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {A1 delta : ℝ}
    (hA1 : 0 < A1) (hdelta : 0 < delta) (k : ℕ)
    (S : CriticalBallSpine H T A1 k)
    {x : H.tubeCriticalRegion T A1 k} {i : ℤ}
    (hi : i ∈ (T k).chain.shape.active)
    (hx : (x : (T k).carrierOpen).val ∈ ((T k).chain.neck i).carrier)
    (hsmall : H.tubeNodeScale T k i < delta / 48)
    (hfar : A1 - delta / 2 <
      ((H.tubeMetric T k).edist (H.tubeBase T k)
        (x : (T k).carrierOpen)).toReal) :
    ∀ n : ℕ, ∃ y : H.tubeCriticalRegion T A1 k,
      A1 - 1 / ((n : ℝ) + 1) <
          ((H.tubeMetric T k).edist (H.tubeBase T k)
            (y : (T k).carrierOpen)).toReal ∧
        (H.tubeCriticalMetric T A1 k).edist x y <
          ENNReal.ofReal (3 * delta / 4) := by
  let : PreconnectedSpace (T k).carrierOpen := (T k).preconnected
  let : ConnectedSpace (H.tubeCriticalRegion T A1 k) :=
    H.tubeCriticalRegion_connected T A1 hA1 k
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : (T k).carrierOpen → Type _) :=
    ⟨(H.tubeMetric T k).toRiemannianMetric⟩
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : H.tubeCriticalRegion T A1 k → Type _) :=
    ⟨(H.tubeCriticalMetric T A1 k).toRiemannianMetric⟩
  intro n
  obtain ⟨tc, htc, htcTube, htcCritical⟩ := S.near i hi x hx
  let q : ℝ := (5858 / 1000 : ℝ) * H.tubeNodeScale T k i
  have hq : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (by norm_num) (H.tubeNodeScale_pos T k i).le
  have htcLower : A1 - delta / 2 - q < tc := by
    have hrad := S.radial tc htc
    have htcTube' :
        ((H.tubeMetric T k).edist
          ((S.gamma tc htc.2 : H.tubeCriticalRegion T A1 k) : (T k).carrierOpen)
          (x : (T k).carrierOpen)).toReal ≤ q := by
      have hcomm :
          (H.tubeMetric T k).edist
              ((S.gamma tc htc.2 : H.tubeCriticalRegion T A1 k) : (T k).carrierOpen)
              (x : (T k).carrierOpen) =
            (H.tubeMetric T k).edist (x : (T k).carrierOpen)
              ((S.gamma tc htc.2 : H.tubeCriticalRegion T A1 k) : (T k).carrierOpen) :=
        Manifold.riemannianEDist_comm
      rw [hcomm]
      simpa only [q] using htcTube
    have htri := (H.tubeMetric T k).toReal_edist_triangle
      (H.tubeBase T k)
      ((S.gamma tc htc.2 : H.tubeCriticalRegion T A1 k) : (T k).carrierOpen)
      (x : (T k).carrierOpen)
    rw [hrad] at htri
    dsimp [q] at htcTube' ⊢
    linarith [htcTube']
  have hfrontier_arg : max (A1 - 1 / ((n : ℝ) + 1)) tc < A1 := by
    apply max_lt
    · have hn : 0 < (n : ℝ) + 1 := by positivity
      have hrecip : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn
      linarith
    · exact htc.2
  obtain ⟨t, ht, hrt⟩ := S.frontier hfrontier_arg
  let y : H.tubeCriticalRegion T A1 k := S.gamma t ht.2
  have hyfrontier : A1 - 1 / ((n : ℝ) + 1) <
      ((H.tubeMetric T k).edist (H.tubeBase T k)
        (y : (T k).carrierOpen)).toReal := by
    have hrad := S.radial t ht
    dsimp [y]
    rw [hrad]
    exact (le_max_left _ _).trans_lt hrt
  refine ⟨y, hyfrontier, ?_⟩
  have htc_le_t : tc ≤ t := by
    exact (le_max_right _ _).trans_lt hrt |>.le
  have htseg : t ∈ Ico tc A1 := ⟨htc_le_t, ht.2⟩
  have hseg := S.segment htc htseg
  have htri := (H.tubeCriticalMetric T A1 k).toReal_edist_triangle
    x (S.gamma tc htc.2) (S.gamma t ht.2)
  have hgap : t - tc < delta / 2 + q := by
    have htA : t < A1 := ht.2
    linarith
  have hqsmall : q < (5858 / 1000 : ℝ) * (delta / 48) := by
    dsimp [q]
    exact mul_lt_mul_of_pos_left hsmall (by norm_num)
  have hbudget : 2 * q + delta / 2 < (3 / 4 : ℝ) * delta := by
    nlinarith
  have hreal :
      ((H.tubeCriticalMetric T A1 k).edist x y).toReal < 3 * delta / 4 := by
    dsimp [y]
    have hsum := htri.trans (add_le_add htcCritical hseg)
    dsimp [q] at hsum hgap hbudget ⊢
    linarith
  apply (ENNReal.toReal_lt_toReal
    ((H.tubeCriticalMetric T A1 k).edist_ne_top x y) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact hreal

end PoincareConjecture.M28.CounterexampleNeckFamily
