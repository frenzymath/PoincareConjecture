import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.PathDistance.Integration


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem regular_paths_distance_tendsto_zero
    (P : AncientAsymptoticSolitonPredecessors K)
    {R : ℝ} {p : M} (G : LExponentialGeometry K.flow 0 R p)
    (Z W : TangentSpace (𝓡 n) p) {τ : ℝ} (hτ : 0 < τ) (hR : τ < R) :
    Tendsto (fun s => ((K.flow.metric (-s)).edist (G.gamma Z s) (G.gamma W s)).toReal)
      (𝓝[>] 0) (𝓝 0) := by
  let g := K.flow.metric (-τ)
  let := g.toMetricSpace
  have hcont (V : TangentSpace (𝓡 n) p) : ContinuousOn (G.gamma V) (Icc 0 τ) := by
    have h := (G.path V τ hτ hR).continuous
    rwa [G.path_eq] at h
  have hfilt : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc 0 τ] 0 :=
    nhdsWithin_le_of_mem (mem_of_superset (Ioc_mem_nhdsGT hτ) Ioc_subset_Icc_self)
  have hlim : Tendsto (fun s => (g.edist (G.gamma Z s) (G.gamma W s)).toReal)
      (𝓝[>] 0) (𝓝 0) := by
    have hdist : ContinuousOn (fun s => dist (G.gamma Z s) (G.gamma W s)) (Icc 0 τ) :=
      continuous_dist.comp_continuousOn ((hcont Z).prodMk (hcont W))
    have h := (hdist 0 ⟨le_rfl, hτ.le⟩).tendsto.mono_left hfilt
    change Tendsto (fun s => dist (G.gamma Z s) (G.gamma W s)) (𝓝[>] 0) (𝓝 0)
    simpa only [G.gamma_at_zero, dist_self] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
  filter_upwards [Ioc_mem_nhdsGT hτ] with s hs
  apply ENNReal.toReal_mono (g.edist_ne_top _ _)
  exact ((Classical.choice P.structural).structural M K).edist_monotone
    (-τ) (-s) (neg_le_neg hs.2) (by linarith [hs.1]) _ _

theorem regular_paths_distance_le
    (P : AncientAsymptoticSolitonPredecessors K)
    {R : ℝ} {p : M} (G : LExponentialGeometry K.flow 0 R p)
    {Z W : TangentSpace (𝓡 n) p} {τ A : ℝ}
    (hZ : (Z, τ) ∈ G.toLExponentialFamily.regularDomain)
    (hW : (W, τ) ∈ G.toLExponentialFamily.regularDomain)
    (hA : 1 ≤ A)
    (hendZ : reducedLength K.flow 0 p (G.gamma Z τ) τ ≤ A)
    (hendW : reducedLength K.flow 0 p (G.gamma W τ) τ ≤ A) :
    ((K.flow.metric (-τ)).edist (G.gamma Z τ) (G.gamma W τ)).toReal ≤
      4 * (2 * (n : ℝ) + 604) * Real.sqrt (A * Real.sqrt τ) * Real.sqrt (Real.sqrt τ) := by
  have hτ := hZ.1.choose
  have hR := hZ.1.choose_spec.choose
  let D := 4 * (2 * (n : ℝ) + 604) * Real.sqrt (A * Real.sqrt τ) * Real.sqrt (Real.sqrt τ)
  have hlim := (P.regular_paths_distance_tendsto_zero G Z W hτ hR).add_const D
  rw [zero_add] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [Ioc_mem_nhdsGT hτ] with a ha
  have h := P.regular_paths_distance_increment_le G hZ hW ha.1 ha.2 hA hendZ hendW
  dsimp only [D]
  have hnonneg : 0 ≤ (2 * (n : ℝ) + 604) *
      (4 * Real.sqrt (A * Real.sqrt τ) * Real.sqrt (Real.sqrt a)) := by positivity
  nlinarith

theorem regular_endpoints_distance_sq_le_reducedLength
    (P : AncientAsymptoticSolitonPredecessors K)
    {R : ℝ} {p : M} (G : LExponentialGeometry K.flow 0 R p)
    {Z W : TangentSpace (𝓡 n) p} {τ : ℝ}
    (hZ : (Z, τ) ∈ G.toLExponentialFamily.regularDomain)
    (hW : (W, τ) ∈ G.toLExponentialFamily.regularDomain) :
    ((K.flow.metric (-τ)).edist (G.gamma Z τ) (G.gamma W τ)).toReal ^ 2 ≤
      16 * (2 * (n : ℝ) + 604) ^ 2 *
        (reducedLength K.flow 0 p (G.gamma Z τ) τ +
          reducedLength K.flow 0 p (G.gamma W τ) τ + 1) * τ := by
  have hτ := hZ.1.choose
  let A := reducedLength K.flow 0 p (G.gamma Z τ) τ +
    reducedLength K.flow 0 p (G.gamma W τ) τ + 1
  have hZpos := P.reducedLength_pos p (G.gamma Z τ) τ hτ
  have hWpos := P.reducedLength_pos p (G.gamma W τ) τ hτ
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have h := P.regular_paths_distance_le G hZ hW hA
    (by dsimp [A]; linarith) (by dsimp [A]; linarith)
  have hsq := (sq_le_sq₀ ENNReal.toReal_nonneg (by positivity)).mpr h
  apply hsq.trans_eq
  simp only [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg τ),
    Real.sq_sqrt (mul_nonneg (show 0 ≤ A by linarith) (Real.sqrt_nonneg τ))]
  have hs := Real.sq_sqrt hτ.le
  dsimp only [A]
  nlinarith [congrArg (fun t : ℝ => 16 * (2 * (n : ℝ) + 604) ^ 2 * A * t) hs]

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
