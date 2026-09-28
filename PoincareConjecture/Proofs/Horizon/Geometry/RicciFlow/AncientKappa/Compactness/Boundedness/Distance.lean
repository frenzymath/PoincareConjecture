import PoincareConjecture.Proofs.Horizon.Compat.M23DistanceDistortion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Windows
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.DistanceDistortion












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

variable {m : ℕ} {M : Type} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
  (F : RicciFlow (m + 1) M (Iic 0))



theorem terminal_distance_le_of_ancient_ricci_nonneg
    (hRic : ∀ t ≤ 0, ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x,
      0 ≤ (F.connection t).ricci x v v)
    {s : ℝ} (hs : s ≤ 0) (p x : M) :
    ((F.metric 0).edist p x).toReal ≤ ((F.metric s).edist p x).toReal := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  have hx : x ∈ (F.metric s).ball p r :=
    (ENNReal.lt_ofReal_iff_toReal_lt ((F.metric s).edist_ne_top p x)).mpr hr
  have hx' := F.ball_subset_terminal_ball_of_ancient_ricci_nonneg p r hs
    (fun t ht y _ v => hRic t ht y v) hx
  exact ((ENNReal.lt_ofReal_iff_toReal_lt ((F.metric 0).edist_ne_top p x)).mp hx').le



theorem tendsto_terminal_distance_of_local_ricci_bound
    {a Λ r : ℝ} (ha : a < 0) (hΛ : 0 ≤ Λ) (hr : 0 < r) (O : M)
    (hRic : ∀ t ≤ 0, ∀ z : M, ∀ v : TangentSpace (𝓡 (m + 1)) z,
      0 ≤ (F.connection t).ricci z v v)
    (hupper : ∀ t ∈ Icc a 0, ∀ z ∈ (F.metric 0).ball O (3 * r),
      ∀ v : TangentSpace (𝓡 (m + 1)) z,
        (F.connection t).ricci z v v ≤ Λ * (F.metric t).inner z v v)
    (x y : M) (hx : x ∈ (F.metric 0).ball O r) (hy : y ∈ (F.metric 0).ball O r) :
    Tendsto (fun t => ((F.metric t).edist x y).toReal) (𝓝[<] 0)
      (𝓝 (((F.metric 0).edist x y).toReal)) := by
  have hu : Continuous (fun t : ℝ => Real.exp (Λ * |t|) *
      ((F.metric 0).edist x y).toReal) := by fun_prop
  have hlim : Tendsto (fun t : ℝ => Real.exp (Λ * |t|) *
      ((F.metric 0).edist x y).toReal) (𝓝[<] 0)
      (𝓝 (((F.metric 0).edist x y).toReal)) := by
    simpa only [abs_zero, mul_zero, Real.exp_zero, one_mul] using
      hu.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] (0 : ℝ) ≤ 𝓝 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact F.terminal_distance_le_of_ancient_ricci_nonneg hRic ht.le x y
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht hat
    have h := F.edist_le_exp_mul_of_ricci_bound (convex_Icc a 0)
      (fun s hs => hs.2) O r Λ hr ⟨ha.le, le_rfl⟩ ⟨hat.le, ht.le⟩
      (fun s hs z hz v => by
        rw [abs_of_nonneg (hRic s hs.2 z v)]
        exact hupper s hs z hz v) hx hy
    have hfinite : ENNReal.ofReal (Real.exp (Λ * |t - 0|)) *
        (F.metric 0).edist x y ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((F.metric 0).edist_ne_top x y)
    simpa only [sub_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)] using ENNReal.toReal_mono hfinite h



theorem toReal_edist_le_add_on_closed_terminal_ball
    (hm : 0 < m) {a Λ scale r R : ℝ} (ha : a < 0)
    (hc : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hRic : ∀ t ≤ 0, ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x,
      0 ≤ (F.connection t).ricci x v v)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (hr : 0 < r)
    (hmargin : 4 * Real.exp (Λ * (0 - a)) * r ≤ R) (O : M)
    (hupper : ∀ t ∈ Icc a 0, ∀ z ∈ (F.metric 0).ball O R,
      ∀ v : TangentSpace (𝓡 (m + 1)) z,
        (F.connection t).ricci z v v ≤ Λ * (F.metric t).inner z v v)
    (x y : M) (hx : x ∈ (F.metric 0).ball O r) (hy : y ∈ (F.metric 0).ball O r) :
    ((F.metric a).edist x y).toReal ≤ ((F.metric 0).edist x y).toReal +
      (4 * (((m + 1 : ℕ) : ℝ)) * scale + 8 * Λ / scale) * (0 - a) := by
  let E := Real.exp (Λ * (0 - a))
  have hE : 0 < E := Real.exp_pos _
  have hEone : 1 ≤ E := Real.one_le_exp_iff.mpr (mul_nonneg hΛ (by linarith))
  have hthree : 3 * r ≤ R := by
    change 4 * E * r ≤ R at hmargin
    nlinarith [mul_le_mul_of_nonneg_right hEone hr.le]
  have hxy : ((F.metric 0).edist x y).toReal < 2 * r := by
    let := (F.metric 0).toMetricSpace
    have hx' : dist x O < r := by
      simpa only [← (F.metric 0).toMetricSpace_ball, Metric.mem_ball] using hx
    have hy' : dist O y < r := by
      simpa only [← (F.metric 0).toMetricSpace_ball, Metric.mem_ball, dist_comm] using hy
    change dist x y < 2 * r
    linarith [dist_triangle x O y]
  have hlocal (t : ℝ) (ht : t ∈ Icc a 0) :
      ∃ ρ : ℝ, y ∈ (F.metric t).ball x ρ ∧
        ∀ z ∈ (F.metric t).ball x ρ, ∀ v : TangentSpace (𝓡 (m + 1)) z,
          (F.connection t).ricci z v v ≤ Λ * (F.metric t).inner z v v := by
    have hcompare := F.edist_le_exp_mul_of_ricci_bound (convex_Icc a 0)
      (fun s hs => hs.2) O r Λ hr ⟨ha.le, le_rfl⟩ ht (fun s hs z hz v => by
        rw [abs_of_nonneg (hRic s hs.2 z v)]
        exact hupper s hs z (hz.trans_le (ENNReal.ofReal_le_ofReal hthree)) v) hx hy
    have hfinite : ENNReal.ofReal (Real.exp (Λ * |t - 0|)) *
        (F.metric 0).edist x y ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((F.metric 0).edist_ne_top x y)
    have hdist : ((F.metric t).edist x y).toReal ≤
        Real.exp (Λ * |t - 0|) * ((F.metric 0).edist x y).toReal := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
        ENNReal.toReal_mono hfinite hcompare
    have hexp : Real.exp (Λ * |t - 0|) ≤ E := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hΛ
      rw [sub_zero, abs_of_nonpos ht.2]
      linarith [ht.1]
    have hdist' : ((F.metric t).edist x y).toReal < 3 * E * r := by
      have hle := hdist.trans (mul_le_mul_of_nonneg_right hexp ENNReal.toReal_nonneg)
      have hlt := mul_lt_mul_of_pos_left hxy hE
      nlinarith
    refine ⟨3 * E * r, ?_, ?_⟩
    · change (F.metric t).edist x y < ENNReal.ofReal (3 * E * r)
      rw [← ENNReal.ofReal_toReal ((F.metric t).edist_ne_top x y)]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hdist'
    · intro z hz v
      have hzterminal := F.ball_subset_terminal_ball_of_ancient_ricci_nonneg
        x (3 * E * r) ht.2 (fun s hs w _ wv => hRic s hs w wv) hz
      have hzcontrol : z ∈ (F.metric 0).ball O R := by
        let := (F.metric 0).toMetricSpace
        have hx' : dist x O < r := by
          simpa only [← (F.metric 0).toMetricSpace_ball, Metric.mem_ball] using hx
        have hz' : dist z x < 3 * E * r := by
          simpa only [← (F.metric 0).toMetricSpace_ball, Metric.mem_ball] using hzterminal
        rw [← (F.metric 0).toMetricSpace_ball, Metric.mem_ball]
        have hsmall : r + 3 * E * r ≤ R := by
          change 4 * E * r ≤ R at hmargin
          nlinarith [mul_le_mul_of_nonneg_right hEone hr.le]
        linarith [dist_triangle z x O]
      exact hupper t ht z hzcontrol v
  have hdistlimit := F.tendsto_terminal_distance_of_local_ricci_bound ha hΛ hr O hRic
    (fun t ht z hz v => hupper t ht z (hz.trans_le (ENNReal.ofReal_le_ofReal hthree)) v)
    x y hx hy
  have htime : Tendsto (fun b : ℝ =>
      (4 * (((m + 1 : ℕ) : ℝ)) * scale + 8 * Λ / scale) * (b - a))
      (𝓝[<] 0) (𝓝 ((4 * (((m + 1 : ℕ) : ℝ)) * scale + 8 * Λ / scale) * (0 - a))) :=
    (by fun_prop : Continuous (fun b : ℝ =>
      (4 * (((m + 1 : ℕ) : ℝ)) * scale + 8 * Λ / scale) * (b - a))).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  apply ge_of_tendsto (hdistlimit.add htime)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds ha).filter_mono nhdsWithin_le_nhds] with b hb hab
  exact F.toReal_edist_le_add_of_ricci_upper_on_balls_intrinsic hm hab.le
    (fun t ht => by simpa only [interior_Iic, mem_Iio] using ht.2.trans_lt hb)
    (fun t ht => hc t (ht.2.trans hb.le))
    (fun t ht z v => hRic t (ht.2.trans hb.le) z v) hΛ hscale x y
    (fun t ht => hlocal t ⟨ht.1, ht.2.trans hb.le⟩)

end PoincareConjecture.RicciFlow
