import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.LineLimit
import Mathlib.Tactic


















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric



theorem exists_minimizing_ray_of_metricComplete
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ConnectedSpace M] [NoncompactSpace M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) :
    ∃ ray : ℝ → M, ray 0 = p ∧ ∀ s, 0 ≤ s → ∀ t, 0 ≤ t →
      g.edist (ray s) (ray t) = ENNReal.ofReal |s - t| := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MetricSpace M := EMetricSpace.toMetricSpace g.edist_ne_top
  let : ProperSpace M := ProperSpace.of_isCompact_closedBall_of_le 0 (fun x r hr => by
    have hset : closedBall x r = {y | g.edist x y ≤ ENNReal.ofReal r} := by
      ext y
      change dist y x ≤ r ↔ g.edist x y ≤ ENNReal.ofReal r
      rw [dist_comm]
      exact (edist_le_ofReal hr).symm
    rw [hset]
    exact g.isCompact_closedBall_of_metricComplete hc x r)
  have hfar : ∀ i : ℕ, ∃ x : M, (i : ℝ) + 1 < dist p x := by
    intro i
    by_contra! h
    apply (isCompact_closedBall p ((i : ℝ) + 1)).ne_univ
    apply Set.eq_univ_of_forall
    intro x
    simpa only [mem_closedBall, dist_comm] using h x
  choose x hx using hfar
  have hsegments : ∀ i : ℕ, ∃ γ : ℝ → M, γ 0 = p ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist p (x i) := by
    intro i
    obtain ⟨ε, _, γ, _, hγ0, _, hγ⟩ :=
      g.exists_minimizing_geodesic_of_metricComplete hc p (x i)
    refine ⟨γ, hγ0, ?_⟩
    intro s hs t ht
    change (g.edist (γ s) (γ t)).toReal = |s - t| * (g.edist p (x i)).toReal
    rw [hγ s hs t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  choose γ hγ0 hγ using hsegments
  let radius : ℕ → ℝ := fun i => dist p (x i)
  have hpos (i : ℕ) : 0 < radius i := by
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    exact lt_trans (by linarith : 0 < (i : ℝ) + 1) (hx i)
  have hescape : Tendsto radius atTop atTop :=
    tendsto_atTop_mono (fun i => le_trans (by linarith : (i : ℝ) ≤ (i : ℝ) + 1)
      (hx i).le) tendsto_natCast_atTop_atTop
  let arc : ℕ → Ici (0 : ℝ) → M := fun i t => γ i (t.val / radius i)
  have hbase (i : ℕ) : arc i ⟨0, by simp⟩ = p := by
    change γ i (0 / radius i) = p
    simp only [zero_div, hγ0]
  have hdist : ∀ s t : Ici (0 : ℝ),
      Tendsto (fun i => dist (arc i s) (arc i t)) atTop (𝓝 |s.val - t.val|) := by
    intro s t
    apply tendsto_const_nhds.congr'
    filter_upwards [hescape.eventually_ge_atTop s.val, hescape.eventually_ge_atTop t.val]
      with i hsi hti
    change |s.val - t.val| = dist (γ i (s.val / radius i)) (γ i (t.val / radius i))
    rw [hγ i (s.val / radius i)
      ⟨div_nonneg s.property (hpos i).le, (div_le_one (hpos i)).mpr hsi⟩
      (t.val / radius i)
      ⟨div_nonneg t.property (hpos i).le, (div_le_one (hpos i)).mpr hti⟩,
      ← sub_div, abs_div, abs_of_pos (hpos i)]
    exact (div_mul_cancel₀ _ (hpos i).ne').symm
  have hbounded : ∀ t : Ici (0 : ℝ), ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
      arc i t ∈ closedBall p (t.val + 1) := by
    intro t
    have hlim : Tendsto (fun i => dist (arc i t) p) atTop (𝓝 t.val) := by
      simpa only [hbase, sub_zero, abs_of_nonneg (show 0 ≤ t.val from t.property)] using
        hdist t ⟨0, by simp⟩
    have hbound := hlim.eventually (eventually_lt_nhds (by linarith : t.val < t.val + 1))
    filter_upwards [hbound.filter_mono Nat.hyperfilter_le_atTop] with i hi
    exact hi.le
  have hlimit : ∀ t : Ici (0 : ℝ), ∃ q : M,
      Tendsto (fun i => arc i t) (hyperfilter ℕ : Filter ℕ) (𝓝 q) := by
    intro t
    obtain ⟨q, _, hq⟩ := (isCompact_closedBall p (t.val + 1)).ultrafilter_le_nhds'
      ((hyperfilter ℕ).map fun i => arc i t) (hbounded t)
    rw [Ultrafilter.coe_map] at hq
    exact ⟨q, hq⟩
  choose limit hlimit using hlimit
  have hlimitdist (s t : Ici (0 : ℝ)) : dist (limit s) (limit t) = |s.val - t.val| :=
    tendsto_nhds_unique ((hlimit s).dist (hlimit t))
      ((hdist s t).mono_left Nat.hyperfilter_le_atTop)
  have hlimit0 : limit ⟨0, by simp⟩ = p := by
    have hconst : Tendsto (fun i => arc i ⟨0, by simp⟩)
        (hyperfilter ℕ : Filter ℕ) (𝓝 p) := by
      simpa only [hbase] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => p)
          (hyperfilter ℕ : Filter ℕ) (𝓝 p))
    exact tendsto_nhds_unique (hlimit ⟨0, by simp⟩) hconst
  let ray : ℝ → M := fun t => limit ⟨max t 0, by exact le_max_right t (0 : ℝ)⟩
  refine ⟨ray, by simpa only [ray, max_self] using hlimit0, ?_⟩
  intro s hs t ht
  have h := hlimitdist ⟨s, hs⟩ ⟨t, ht⟩
  have hdist' : dist (ray s) (ray t) = |s - t| := by
    simpa only [ray, max_eq_left hs, max_eq_left ht] using h
  change EDist.edist (ray s) (ray t) = _
  rw [edist_dist, hdist']

end PoincareConjecture.RiemannianMetric
