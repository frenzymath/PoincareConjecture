import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem edist_le_pathELength_of_mem_Icc (g : RiemannianMetric n M)
    {γ : ℝ → M} {a b t : ℝ}
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b))
    (ht : t ∈ Icc a b) :
    g.edist (γ a) (γ t) ≤ g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (Manifold.riemannianEDist_le_pathELength
    (hγ.mono (Icc_subset_Icc_right ht.2)) rfl rfl ht.1).trans
      (Manifold.pathELength_mono le_rfl ht.2)

theorem mapsTo_ball_of_pathELength_lt (g : RiemannianMetric n M)
    {γ : ℝ → M} {a b r : ℝ}
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b))
    (hlen : g.pathELength γ a b < ENNReal.ofReal r) :
    MapsTo γ (Icc a b) (g.ball (γ a) r) := by
  intro t ht
  exact (g.edist_le_pathELength_of_mem_Icc hγ ht).trans_lt hlen

theorem exists_short_path_in_ball (g : RiemannianMetric n M)
    (p q : M) {r : ℝ} (hq : q ∈ g.ball p r) :
    ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = q ∧
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc (0 : ℝ) 1) ∧
      g.pathELength γ 0 1 < ENNReal.ofReal r ∧
      MapsTo γ (Icc (0 : ℝ) 1) (g.ball p r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨γ, h0, h1, hγ, hlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hq
  refine ⟨γ, h0, h1, hγ, hlen, ?_⟩
  simpa only [h0] using g.mapsTo_ball_of_pathELength_lt hγ hlen

theorem isCompact_closedBall_of_precompact_ball [T2Space M]
    (g : RiemannianMetric n M) (p : M) {r R : ℝ} (hR : 0 < R)
    (hrR : r < R) (hcompact : IsCompact (closure (g.ball p R))) :
    IsCompact {q | g.edist p q ≤ ENNReal.ofReal r} := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  apply hcompact.of_isClosed_subset
  · exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  · intro q hq
    exact subset_closure (hq.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hrR))

theorem exists_compact_confined_short_paths [T2Space M]
    (g : RiemannianMetric n M) (p q : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R))) (hq : q ∈ g.ball p R) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ g.ball p R ∧
      ∀ l : ℝ≥0∞, g.edist p q < l → ∃ γ : ℝ → M,
        γ 0 = p ∧ γ 1 = q ∧
        ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc (0 : ℝ) 1) ∧
        g.pathELength γ 0 1 < l ∧ MapsTo γ (Icc (0 : ℝ) 1) K := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hfinite : g.edist p q ≠ ⊤ := ne_top_of_lt (hq.trans_le le_top)
  obtain ⟨r, hdr, hrR⟩ := exists_between (ENNReal.toReal_lt_of_lt_ofReal hq)
  have hdr' : g.edist p q < ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_nonneg.trans_lt hdr)).mpr hdr
  refine ⟨{x | g.edist p x ≤ ENNReal.ofReal r},
    g.isCompact_closedBall_of_precompact_ball p hR hrR hcompact, ?_, ?_⟩
  · intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hrR)
  · intro l hl
    obtain ⟨γ, h0, h1, hγ, hlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt (lt_min hl hdr')
    refine ⟨γ, h0, h1, hγ, hlen.trans_le (min_le_left _ _), ?_⟩
    intro t ht
    have hdist := g.edist_le_pathELength_of_mem_Icc hγ ht
    rw [h0] at hdist
    exact (hdist.trans_lt (hlen.trans_le (min_le_right _ _))).le

theorem exists_compact_confined_minimizing_sequence [T2Space M]
    (g : RiemannianMetric n M) (p q : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R))) (hq : q ∈ g.ball p R) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ g.ball p R ∧
      ∃ γ : ℕ → ℝ → M,
        (∀ k, γ k 0 = p ∧ γ k 1 = q ∧
          ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (γ k) (Icc (0 : ℝ) 1) ∧
          MapsTo (γ k) (Icc (0 : ℝ) 1) K) ∧
        Tendsto (fun k => g.pathELength (γ k) 0 1) atTop (𝓝 (g.edist p q)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hfinite : g.edist p q ≠ ⊤ := ne_top_of_lt (hq.trans_le le_top)
  obtain ⟨K, hK, hKR, hpaths⟩ :=
    g.exists_compact_confined_short_paths p q hR hcompact hq
  have happrox (k : ℕ) : g.edist p q <
      ENNReal.ofReal ((g.edist p q).toReal + 1 / ((k : ℝ) + 1)) := by
    apply (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  choose γ h0 h1 hγ hlen hconf using fun k => hpaths _ (happrox k)
  refine ⟨K, hK, hKR, γ, fun k => ⟨h0 k, h1 k, hγ k, hconf k⟩, ?_⟩
  have ht : Tendsto (fun k : ℕ =>
      ENNReal.ofReal ((g.edist p q).toReal + 1 / ((k : ℝ) + 1)))
      atTop (𝓝 (g.edist p q)) := by
    have h : Tendsto (fun k : ℕ =>
        ENNReal.ofReal ((g.edist p q).toReal + 1 / ((k : ℝ) + 1)))
        atTop (𝓝 (ENNReal.ofReal ((g.edist p q).toReal + 0))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat)
    simpa only [add_zero, ENNReal.ofReal_toReal hfinite] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro k
    exact Manifold.riemannianEDist_le_pathELength (hγ k) (h0 k) (h1 k) zero_le_one
  · exact fun k => (hlen k).le

end PoincareConjecture.RiemannianMetric
