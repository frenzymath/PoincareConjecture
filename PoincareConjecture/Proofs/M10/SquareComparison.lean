import PoincareConjecture.Proofs.M10.SquareCoordinates
import PoincareConjecture.Proofs.M10.ExponentialDifferential
import PoincareConjecture.Proofs.M10.EndpointMetricContinuity









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem squareFamily_tendsto_zero (G : LExponentialGeometry F T τmax p)
    (hmax : 0 < τmax) (Z : TangentSpace (𝓡 n) p) :
    Tendsto (G.squareFamily Z) (𝓝 (0 : ℝ)) (𝓝 p) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hQ := G.square_smooth.contMDiffAt
    (G.square_open.mem_nhds (squareDomain_at_zero G hmax Z))
  have hc := hQ.continuousAt.comp
    (continuousAt_const.prodMk (continuousAt_id (X := ℝ) (x := 0)))
  simpa only [Function.comp_def, G.square_at_zero] using hc.tendsto

set_option backward.isDefEq.respectTransparency false in

theorem squareCoordinates_horizontal_eq_endpoint
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (Z W : TangentSpace (𝓡 n) p) {s : ℝ} (hs : s ∈ Ioo 0 (Real.sqrt τmax))
    (hq : G.gamma Z (s ^ 2) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    fderiv ℝ (squareCoordinates G) (Z, s) (W, 0) =
      fderiv ℝ (endpointCoordinates G p) (Z, s ^ 2) (W, 0) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hsmax : s ^ 2 < τmax := by nlinarith [Real.sq_sqrt hmax.le, hs.1, hs.2]
  have hdom : (Z, s) ∈ G.squareDomain := G.square_contains ⟨mem_univ _, hs.1.le, hs.2⟩
  have hqs : G.squareFamily Z s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source := by
    rwa [G.square_agrees Z s ⟨hs.1.le, hs.2⟩]
  rw [fderiv_horizontal_eq
      ((squareCoordinates_contDiffAt G (Z, s) hdom hqs).differentiableAt (by simp)) W,
    fderiv_horizontal_eq ((endpointCoordinates_contDiffAt G p (Z, s ^ 2)
      ⟨mem_univ _, sq_pos_of_pos hs.1, hsmax⟩ hq).differentiableAt (by simp)) W]
  have heq : (fun V ↦ squareCoordinates G (V, s)) =
      (fun V ↦ endpointCoordinates G p (V, s ^ 2)) := by
    funext V
    exact congrArg (extChartAt (𝓡 n) p) (G.square_agrees V s ⟨hs.1.le, hs.2⟩)
  rw [heq]

set_option backward.isDefEq.respectTransparency false in

theorem squareCoordinates_pullbackMetric_eq
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (x u v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : s ∈ Ioo 0 (Real.sqrt τmax))
    (hq : G.gamma (metricCoordinates (F.metric T) p x) (s ^ 2) ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    let Z := metricCoordinates (F.metric T) p x
    pullbackMetricForm (F.metric (T - s ^ 2)) (exponentialSliceChart G (s ^ 2)) x u v =
      backwardMetricCoordinates F T p (G.squareFamily Z s, s ^ 2)
        (fderiv ℝ (squareCoordinates G) (Z, s) (metricCoordinates (F.metric T) p u, 0))
        (fderiv ℝ (squareCoordinates G) (Z, s) (metricCoordinates (F.metric T) p v, 0)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  dsimp only
  have hsmax : s ^ 2 < τmax := by nlinarith [Real.sq_sqrt hmax.le, hs.1, hs.2]
  rw [exponentialSlice_pullbackMetric_eq G (sq_pos_of_pos hs.1) hsmax x p hq u v,
    squareCoordinates_horizontal_eq_endpoint G hmax _ _ hs hq,
    squareCoordinates_horizontal_eq_endpoint G hmax _ _ hs hq]
  dsimp only [coordinateBackwardMetric, endpointCoordinates]
  rw [(extChartAt (𝓡 n) p).left_inv (by simpa only [extChartAt_source] using hq),
    G.square_agrees _ s ⟨hs.1.le, hs.2⟩]

set_option backward.isDefEq.respectTransparency false in

theorem squareMetric_tendsto_zero (G : LExponentialGeometry F T τmax p)
    (hmax : 0 < τmax) (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (Z : TangentSpace (𝓡 n) p) :
    Tendsto (fun s : ℝ ↦ backwardMetricCoordinates F T p (G.squareFamily Z s, s ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (backwardMetricCoordinates F T p (p, 0))) := by
  have hQ : Tendsto (G.squareFamily Z) (𝓝[>] (0 : ℝ)) (𝓝 p) :=
    (squareFamily_tendsto_zero G hmax Z).mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun s : ℝ ↦ s ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [id_eq, zero_pow (by decide : (2 : ℕ) ≠ 0)] using!
      ((tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)).mono_left
        nhdsWithin_le_nhds).pow 2
  have hp := hQ.prodMk_nhds hs
  have hwithin : Tendsto (fun s : ℝ ↦ (G.squareFamily Z s, s ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝[univ ×ˢ Icc 0 τmax] (p, 0)) := by
    apply tendsto_nhdsWithin_iff.mpr ⟨hp, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (Real.sqrt_pos.2 hmax)] with s hs
    refine ⟨mem_univ _, sq_nonneg _, ?_⟩
    nlinarith [Real.sq_sqrt hmax.le, hs.1, hs.2]
  exact (backwardMetricCoordinates_continuousWithinAt_zero hT hwindow p).tendsto.comp hwithin

end PoincareConjecture.M10
