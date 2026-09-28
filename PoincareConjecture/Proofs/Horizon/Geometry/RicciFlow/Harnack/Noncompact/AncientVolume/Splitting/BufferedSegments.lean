import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.DistanceDistortion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SourceSegments














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Poincare.AncientVolume.Splitting

private theorem comparison_cosine_additive_bounds
    {a b c A B D C : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hC : 0 ≤ C) (htriangle : c ≤ a + b)
    (hA : a ≤ A ∧ A ≤ a + C) (hB : b ≤ B ∧ B ≤ b + C)
    (hcD : c ≤ D) (htriangle' : D ≤ A + B) :
    0 ≤ (A ^ 2 + B ^ 2 - D ^ 2) / (2 * A * B) + 1 ∧
      (A ^ 2 + B ^ 2 - D ^ 2) / (2 * A * B) + 1 ≤
        (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) + 1 +
          2 * C / a + 2 * C / b + (2 * C ^ 2 / a) / b := by
  have hAp : 0 < A := ha.trans_le hA.1
  have hBp : 0 < B := hb.trans_le hB.1
  have hD : 0 ≤ D := hc.trans hcD
  have hden : 0 < 2 * a * b := by positivity
  have hden' : 0 < 2 * A * B := by positivity
  have hdenle : 2 * a * b ≤ 2 * A * B := by
    nlinarith [mul_le_mul hA.1 hB.1 hb.le hAp.le]
  have hold : 0 ≤ (a + b) ^ 2 - c ^ 2 :=
    sub_nonneg.mpr (pow_le_pow_left₀ hc htriangle 2)
  have hnew : 0 ≤ (A + B) ^ 2 - D ^ 2 :=
    sub_nonneg.mpr (pow_le_pow_left₀ hD htriangle' 2)
  have hnum : (A + B) ^ 2 - D ^ 2 ≤
      (a + b) ^ 2 - c ^ 2 + 4 * C * (a + b) + 4 * C ^ 2 := by
    have hsum : A + B ≤ a + b + 2 * C := by linarith [hA.2, hB.2]
    have hsum2 := pow_le_pow_left₀ (by positivity : 0 ≤ A + B) hsum 2
    have hc2 := pow_le_pow_left₀ hc hcD 2
    nlinarith
  have holdplus : 0 ≤ (a + b) ^ 2 - c ^ 2 + 4 * C * (a + b) + 4 * C ^ 2 := by
    positivity
  have hidentity (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
      (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) + 1 =
        ((a + b) ^ 2 - c ^ 2) / (2 * a * b) := by
    field_simp
    ring
  rw [hidentity A B D hAp.ne' hBp.ne']
  refine ⟨div_nonneg hnew hden'.le, ?_⟩
  calc
    _ ≤ ((a + b) ^ 2 - c ^ 2 + 4 * C * (a + b) + 4 * C ^ 2) / (2 * A * B) :=
      div_le_div_of_nonneg_right hnum hden'.le
    _ ≤ ((a + b) ^ 2 - c ^ 2 + 4 * C * (a + b) + 4 * C ^ 2) / (2 * a * b) :=
      div_le_div_of_nonneg_left holdplus hden hdenle
    _ = _ := by field_simp; ring




theorem tendsto_comparison_cosine_of_additive_bounds
    {a b c A B D : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 ≤ c i)
    (htriangle : ∀ i, c i ≤ a i + b i)
    (haTop : Tendsto a atTop atTop) (hbTop : Tendsto b atTop atTop)
    (hcos : Tendsto (fun i => (a i ^ 2 + b i ^ 2 - c i ^ 2) / (2 * a i * b i))
      atTop (𝓝 (-1)))
    (hA : ∀ i, a i ≤ A i ∧ A i ≤ a i + C)
    (hB : ∀ i, b i ≤ B i ∧ B i ≤ b i + C)
    (hD : ∀ i, c i ≤ D i) (htriangle' : ∀ i, D i ≤ A i + B i) :
    Tendsto (fun i => (A i ^ 2 + B i ^ 2 - D i ^ 2) / (2 * A i * B i))
      atTop (𝓝 (-1)) := by
  have hzero : Tendsto
      (fun i => (a i ^ 2 + b i ^ 2 - c i ^ 2) / (2 * a i * b i) + 1) atTop (𝓝 0) := by
    simpa only [neg_add_cancel] using hcos.add_const 1
  have he1 : Tendsto (fun i => 2 * C / a i) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop haTop
  have he2 : Tendsto (fun i => 2 * C / b i) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hbTop
  have he3 : Tendsto (fun i => (2 * C ^ 2 / a i) / b i) atTop (𝓝 0) :=
    (tendsto_const_nhds.div_atTop haTop).div_atTop hbTop
  have hu : Tendsto (fun i =>
      (a i ^ 2 + b i ^ 2 - c i ^ 2) / (2 * a i * b i) + 1 +
        2 * C / a i + 2 * C / b i + (2 * C ^ 2 / a i) / b i) atTop (𝓝 0) := by
    simpa only [add_zero] using ((hzero.add he1).add he2).add he3
  have hbound (i : ℕ) := comparison_cosine_additive_bounds (ha i) (hb i) (hc i) hC
    (htriangle i) (hA i) (hB i) (hD i) (htriangle' i)
  have hnew : Tendsto
      (fun i => (A i ^ 2 + B i ^ 2 - D i ^ 2) / (2 * A i * B i) + 1) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun i => (hbound i).1) (fun i => (hbound i).2)
  simpa only [add_sub_cancel_right, zero_sub] using hnew.sub_const 1

end Poincare.AncientVolume.Splitting

universe u

namespace PoincareConjecture.RicciFlow

private theorem toReal_edist_le_of_ricci_nonneg
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) {a b : ℝ}
    (hab : a ≤ b) (hJ : Icc a b ⊆ interior J)
    (hRic : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v) (p x : M) :
    ((F.metric b).edist p x).toReal ≤ ((F.metric a).edist p x).toReal := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  have hx : x ∈ (F.metric a).ball p r :=
    (ENNReal.lt_ofReal_iff_toReal_lt ((F.metric a).edist_ne_top p x)).mpr hr
  have hx' := F.ball_subset_ball_of_ricci_nonneg hJ p r
    ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab (fun t ht y _ v => hRic t ht y v) hx
  exact ((ENNReal.lt_ofReal_iff_toReal_lt ((F.metric b).edist_ne_top p x)).mp hx').le

private theorem endpoint_distance_triangle
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (q x y : M) :
    (g.edist x y).toReal ≤ (g.edist q x).toReal + (g.edist q y).toReal := by
  let := g.toMetricSpace
  change dist x y ≤ dist q x + dist q y
  simpa only [dist_comm x q] using dist_triangle x q y




theorem exists_buffered_opposite_minimizing_segments
    {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (J : ℕ → Set ℝ) (F : ∀ i, RicciFlow (m + 1) M (J i))
    {δ Λ scale : ℝ} (hδ : 0 < δ) (hΛ : 0 ≤ Λ) (hscale : 0 < scale)
    (hJ : ∀ i, Icc (-δ) 0 ⊆ interior (J i))
    (hcomplete : ∀ i t, t ∈ Icc (-δ) 0 → MetricComplete ((F i).metric t))
    (hRic : ∀ i t, t ∈ Icc (-δ) 0 → ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x,
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
    let error := (4 * (((m + 1 : ℕ) : ℝ)) * scale + 8 * Λ / scale) * δ
    (∀ i, 0 < A i ∧ 0 < B i ∧ a i ≤ A i ∧ A i ≤ a i + error ∧
      b i ≤ B i ∧ B i ≤ b i + error) ∧
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
    (F i).toReal_edist_le_of_ricci_nonneg (neg_nonpos.mpr hδ.le) (hJ i) (hRic i) x y
  have hadd (i : ℕ) (x y : M)
      (hx' : x ∈ ((F i).metric 0).ball (q i) (r i))
      (hy' : y ∈ ((F i).metric 0).ball (q i) (r i)) :
      (((F i).metric (-δ)).edist x y).toReal ≤
        (((F i).metric 0).edist x y).toReal + error := by
    simpa only [sub_neg_eq_add, zero_add] using
      (F i).toReal_edist_le_add_of_ricci_upper_on_terminal_ball hC hm
        (neg_nonpos.mpr hδ.le) (hJ i) (hcomplete i) (hRic i) hΛ hscale (hr i)
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
  have htriangle (i : ℕ) :
      (((F i).metric 0).edist (minus i (a i)) (plus i (b i))).toReal ≤ a i + b i := by
    simpa only [haminus, hbplus] using
      endpoint_distance_triangle ((F i).metric 0) (q i) (minus i (a i)) (plus i (b i))
  have hnewcos := Poincare.AncientVolume.Splitting.tendsto_comparison_cosine_of_additive_bounds
    herror ha hb (fun _ => ENNReal.toReal_nonneg) htriangle haTop hbTop hcos hA hB
    (fun i => hmonotone i (minus i (a i)) (plus i (b i)))
    (fun i => endpoint_distance_triangle ((F i).metric (-δ)) (q i)
      (minus i (a i)) (plus i (b i)))
  choose earlierMinus hm0 hmend hmmin using fun i =>
    ((F i).metric (-δ)).exists_unit_speed_minimizing_segment_of_metricComplete
      (hcomplete i (-δ) ⟨le_rfl, neg_nonpos.mpr hδ.le⟩) (q i) (minus i (a i)) (hAp i)
  choose earlierPlus hp0 hpend hpmin using fun i =>
    ((F i).metric (-δ)).exists_unit_speed_minimizing_segment_of_metricComplete
      (hcomplete i (-δ) ⟨le_rfl, neg_nonpos.mpr hδ.le⟩) (q i) (plus i (b i)) (hBp i)
  exact ⟨(fun i => ⟨hAp i, hBp i, (hA i).1, (hA i).2, hB i⟩),
    tendsto_atTop_mono (fun i => (hA i).1) haTop,
    tendsto_atTop_mono (fun i => (hB i).1) hbTop, hnewcos,
    earlierMinus, earlierPlus, (fun i => ⟨hm0 i, hmend i, hp0 i, hpend i⟩), hmmin, hpmin⟩

end PoincareConjecture.RicciFlow
