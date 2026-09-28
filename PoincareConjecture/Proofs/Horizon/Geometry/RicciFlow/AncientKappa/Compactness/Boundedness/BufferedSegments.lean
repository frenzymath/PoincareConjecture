import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.BufferedSegments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

theorem exists_buffered_opposite_segments_on_closed_ancient_flows
    {m : ℕ} {M : Type} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (hm : 0 < m) (F : ℕ → RicciFlow (m + 1) M (Iic 0))
    {δ Λ scale : ℝ} (hδ : 0 < δ) (hΛ : 0 ≤ Λ) (hscale : 0 < scale)
    (hc : ∀ i t, t ≤ 0 → MetricComplete ((F i).metric t))
    (hRic : ∀ i t, t ≤ 0 → ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x,
      0 ≤ ((F i).connection t).ricci x v v)
    (q : ℕ → M) (r L : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hmargin : ∀ i, 4 * Real.exp (Λ * δ) * r i ≤ L i)
    (hupper : ∀ i t, t ∈ Icc (-δ) 0 → ∀ z ∈ ((F i).metric 0).ball (q i) (L i),
      ∀ v : TangentSpace (𝓡 (m + 1)) z,
        ((F i).connection t).ricci z v v ≤ Λ * ((F i).metric t).inner z v v)
    (minus plus : ℕ → ℝ → M) (a b : ℕ → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hminus0 : ∀ i, minus i 0 = q i) (hplus0 : ∀ i, plus i 0 = q i)
    (hminus : ∀ i, ∀ s ∈ Icc (0 : ℝ) (a i), ∀ t ∈ Icc (0 : ℝ) (a i),
      (((F i).metric 0).edist (minus i s) (minus i t)).toReal = |s - t|)
    (hplus : ∀ i, ∀ s ∈ Icc (0 : ℝ) (b i), ∀ t ∈ Icc (0 : ℝ) (b i),
      (((F i).metric 0).edist (plus i s) (plus i t)).toReal = |s - t|)
    (hx : ∀ i, minus i (a i) ∈ ((F i).metric 0).ball (q i) (r i))
    (hy : ∀ i, plus i (b i) ∈ ((F i).metric 0).ball (q i) (r i))
    (haTop : Tendsto a atTop atTop) (hbTop : Tendsto b atTop atTop)
    (hcos : Tendsto (fun i =>
      (a i ^ 2 + b i ^ 2 -
        (((F i).metric 0).edist (minus i (a i)) (plus i (b i))).toReal ^ 2) /
          (2 * a i * b i)) atTop (𝓝 (-1))) :
    let A := fun i => (((F i).metric (-δ)).edist (q i) (minus i (a i))).toReal
    let B := fun i => (((F i).metric (-δ)).edist (q i) (plus i (b i))).toReal
    (∀ i, 0 < A i ∧ 0 < B i) ∧
    Tendsto A atTop atTop ∧ Tendsto B atTop atTop ∧
    Tendsto (fun i =>
      (A i ^ 2 + B i ^ 2 -
        (((F i).metric (-δ)).edist (minus i (a i)) (plus i (b i))).toReal ^ 2) /
          (2 * A i * B i)) atTop (𝓝 (-1)) ∧
    ∃ earlierMinus earlierPlus : ℕ → ℝ → M,
      (∀ i, earlierMinus i 0 = q i ∧ earlierMinus i (A i) = minus i (a i) ∧
        earlierPlus i 0 = q i ∧ earlierPlus i (B i) = plus i (b i)) ∧
      (∀ i, ∀ s ∈ Icc (0 : ℝ) (A i), ∀ t ∈ Icc (0 : ℝ) (A i),
        (((F i).metric (-δ)).edist (earlierMinus i s) (earlierMinus i t)).toReal = |s - t|) ∧
      (∀ i, ∀ s ∈ Icc (0 : ℝ) (B i), ∀ t ∈ Icc (0 : ℝ) (B i),
        (((F i).metric (-δ)).edist (earlierPlus i s) (earlierPlus i t)).toReal = |s - t|) := by
  let A := fun i => (((F i).metric (-δ)).edist (q i) (minus i (a i))).toReal
  let B := fun i => (((F i).metric (-δ)).edist (q i) (plus i (b i))).toReal
  let error := (4 * (((m + 1 : ℕ) : ℝ)) * scale + 8 * Λ / scale) * δ
  have herror : 0 ≤ error := by dsimp [error]; positivity
  have haminus (i : ℕ) : (((F i).metric 0).edist (q i) (minus i (a i))).toReal = a i := by
    rw [← hminus0 i, hminus i 0 ⟨le_rfl, (ha i).le⟩ (a i) ⟨(ha i).le, le_rfl⟩,
      zero_sub, abs_neg, abs_of_pos (ha i)]
  have hbplus (i : ℕ) : (((F i).metric 0).edist (q i) (plus i (b i))).toReal = b i := by
    rw [← hplus0 i, hplus i 0 ⟨le_rfl, (hb i).le⟩ (b i) ⟨(hb i).le, le_rfl⟩,
      zero_sub, abs_neg, abs_of_pos (hb i)]
  have hmonotone (i : ℕ) (x y : M) :
      (((F i).metric 0).edist x y).toReal ≤ (((F i).metric (-δ)).edist x y).toReal :=
    (F i).terminal_distance_le_of_ancient_ricci_nonneg (hRic i) (by linarith) x y
  have hadd (i : ℕ) (x y : M)
      (hx' : x ∈ ((F i).metric 0).ball (q i) (r i))
      (hy' : y ∈ ((F i).metric 0).ball (q i) (r i)) :
      (((F i).metric (-δ)).edist x y).toReal ≤
        (((F i).metric 0).edist x y).toReal + error := by
    simpa only [sub_neg_eq_add, zero_add] using
      (F i).toReal_edist_le_add_on_closed_terminal_ball hm (by linarith : -δ < 0)
        (hc i) (hRic i) hΛ hscale (hr i)
        (by simpa only [sub_neg_eq_add, zero_add] using hmargin i)
        (q i) (hupper i) x y hx' hy'
  have hqball (i : ℕ) : q i ∈ ((F i).metric 0).ball (q i) (r i) := by
    simpa only [RiemannianMetric.ball, mem_ofPred_eq, RiemannianMetric.edist,
      Manifold.riemannianEDist_self] using ENNReal.ofReal_pos.mpr (hr i)
  have hA (i : ℕ) : a i ≤ A i ∧ A i ≤ a i + error := by
    constructor
    · simpa only [haminus] using hmonotone i (q i) (minus i (a i))
    · simpa only [haminus] using hadd i (q i) (minus i (a i)) (hqball i) (hx i)
  have hB (i : ℕ) : b i ≤ B i ∧ B i ≤ b i + error := by
    constructor
    · simpa only [hbplus] using hmonotone i (q i) (plus i (b i))
    · simpa only [hbplus] using hadd i (q i) (plus i (b i)) (hqball i) (hy i)
  have hAp (i : ℕ) : 0 < A i := (ha i).trans_le (hA i).1
  have hBp (i : ℕ) : 0 < B i := (hb i).trans_le (hB i).1
  have htriangle (g : RiemannianMetric (m + 1) M) (q x y : M) :
      (g.edist x y).toReal ≤ (g.edist q x).toReal + (g.edist q y).toReal := by
    let := g.toMetricSpace
    change dist x y ≤ dist q x + dist q y
    simpa only [dist_comm x q] using dist_triangle x q y
  have hterminalTriangle (i : ℕ) :
      (((F i).metric 0).edist (minus i (a i)) (plus i (b i))).toReal ≤ a i + b i := by
    simpa only [haminus, hbplus] using
      htriangle ((F i).metric 0) (q i) (minus i (a i)) (plus i (b i))
  have hnewcos := Poincare.AncientVolume.Splitting.tendsto_comparison_cosine_of_additive_bounds
    herror ha hb (fun _ => ENNReal.toReal_nonneg) hterminalTriangle
    haTop hbTop hcos hA hB (fun i => hmonotone i (minus i (a i)) (plus i (b i)))
    (fun i => htriangle ((F i).metric (-δ)) (q i) (minus i (a i)) (plus i (b i)))
  choose earlierMinus hm0 hmend hmmin using fun i =>
    ((F i).metric (-δ)).exists_unit_speed_minimizing_segment_of_metricComplete
      (hc i (-δ) (by linarith)) (q i) (minus i (a i)) (hAp i)
  choose earlierPlus hp0 hpend hpmin using fun i =>
    ((F i).metric (-δ)).exists_unit_speed_minimizing_segment_of_metricComplete
      (hc i (-δ) (by linarith)) (q i) (plus i (b i)) (hBp i)
  exact ⟨(fun i => ⟨hAp i, hBp i⟩),
    tendsto_atTop_mono (fun i => (hA i).1) haTop,
    tendsto_atTop_mono (fun i => (hB i).1) hbTop, hnewcos,
    earlierMinus, earlierPlus, (fun i => ⟨hm0 i, hmend i, hp0 i, hpend i⟩), hmmin, hpmin⟩

end PoincareConjecture.RicciFlow
