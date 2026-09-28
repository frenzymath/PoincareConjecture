import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.ChartOverlaps
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.JetBounds
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Operations
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

theorem pullbackCoefficients_chartParametrization_restrict
    {ι : Type*} {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M)
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)] (i : ι) (f : EuclideanSpace ℝ (Fin n) → M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U i) :
    g.pullbackCoefficients (ChartDistance.chartParametrization U hU
      (fun y : Piece U i => f y)) x = g.pullbackCoefficients f x := by
  have heq : ChartDistance.chartParametrization U hU (fun y : Piece U i => f y)
      =ᶠ[𝓝 x] f := by
    filter_upwards [(hU i).mem_nhds hx] with y hy
    exact ChartDistance.chartParametrization_apply U hU
      (fun z : Piece U i => f z) ⟨y, hy⟩
  ext v w
  change g.inner _ (mfderiv (𝓡 n) (𝓡 n) _ x v) (mfderiv (𝓡 n) (𝓡 n) _ x w) =
    g.inner _ (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)
  rw [heq.mfderiv_eq, heq.self_of_nhds]

theorem isLocalDiffeomorph_normal_chart_restrict
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) [Nonempty U]
    (hsource : U ⊆ Φ.source) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (fun x : U => Φ x) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro x
  exact (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 n) U hU ∞ x).comp (𝓡 n) M
    (Φ.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (hsource x.property))

theorem locallyEventuallyBoundedDerivatives_normal_chart_transition
    {n : ℕ} {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, T3Space (M k)]
    [∀ k, PreconnectedSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)] [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, RiemannianMetric n (M k)) (q : ∀ k, ℕ → M k)
    (Φ : ∀ k, ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) (M k) ∞)
    (h : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {S r : ℝ} (hr : 0 < r) (hrS : 3 * r ≤ S)
    (hsource : ∀ k j, (Φ k j).source = Metric.ball 0 S)
    (htarget : ∀ k j, (Φ k j).target = (g k).ball (q k j) S)
    (hradial : ∀ k j x, x ∈ Metric.ball 0 S →
      (g k).edist (q k j) (Φ k j x) = ENNReal.ofReal ‖x‖)
    (helliptic : ∀ k j, ∀ x ∈ Metric.ball 0 (3 * r), ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ (g k).pullbackCoefficients (Φ k j) x v v ∧
      (g k).pullbackCoefficients (Φ k j) x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2)
    (hjets : ∀ j m C, IsCompact C → C ⊆ Metric.ball 0 r → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients (Φ k j)))
      (iteratedFDeriv ℝ m (h j).euclideanCoefficients) atTop C) :
    let U := fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
    let hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
    letI : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, Metric.mem_ball_self hr⟩⟩
    ∀ (d : ∀ i j, C(Piece U i × Piece U j, ℝ)),
      (∀ i j (x : Piece U i) (y : Piece U j), Tendsto
        (fun k => ((g k).edist (Φ k i x) (Φ k j y)).toReal)
        atTop (𝓝 (d i j (x, y)))) →
      ∀ i j, LocallyEventuallyBoundedDerivatives
        (Subtype.val '' ChartDistance.overlap (fun i j => d i j) i j)
        (fun k => ChartDistance.coordinateRepresentative U hU
          (fun x : Piece U i => Function.invFun (fun y : Piece U j => Φ k j y) (Φ k i x))) := by
  let U := fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
  let hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
  let : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, Metric.mem_ball_self hr⟩⟩
  dsimp only
  intro d hd i j
  let : ∀ k, MetricSpace (M k) := fun k => (g k).toMetricSpace
  let e : ∀ k j, Piece U j → M k := fun k j x => Φ k j x
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ Metric.ball 0 S :=
    Metric.ball_subset_ball (by linarith)
  have hs (k j : ℕ) : U j ⊆ (Φ k j).source := by
    rw [hsource]
    exact hsub
  have hdist (k j : ℕ) (x y : Piece U j) :
      (1 / 2 : ℝ) * dist x y ≤ dist (e k j x) (e k j y) ∧
        dist (e k j x) (e k j y) ≤ (3 / 2 : ℝ) * dist x y := by
    have hh := (g k).toReal_edist_bounds_of_normal_pullback_bounds (q k j) (Φ k j)
      hr hrS (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) ≤ 9 / 4)
      (hsource k j) (htarget k j) (hradial k j) (helliptic k j) x.property y.property
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h9 : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num [Real.sqrt_div, h4, h9] at hh
    exact hh
  have hLip (k j : ℕ) : LipschitzWith (3 / 2 : ℝ≥0) (e k j) :=
    LipschitzWith.of_dist_le_mul (fun x y => by simpa using (hdist k j x y).2)
  have hopen (k j : ℕ) : Topology.IsOpenEmbedding (e k j) :=
    (Φ k j).toOpenPartialHomeomorph.isOpenEmbedding_restrict.comp
      (Topology.IsOpenEmbedding.inclusion (hs k j)
        ((hU j).preimage continuous_subtype_val))
  have hconn (k : ℕ) (p : M k) (s : ℝ) : IsPreconnected (Metric.ball p s) := by
    rw [(g k).toMetricSpace_ball]
    exact (g k).isPreconnected_ball p s
  have hsmooth : letI : ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U j) :=
        fun j => letI : Nonempty (U j) := ⟨⟨0, Metric.mem_ball_self hr⟩⟩
          (hU j).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k j, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k j) := by
    intro k j
    let : Nonempty (U j) := ⟨⟨0, Metric.mem_ball_self hr⟩⟩
    exact isLocalDiffeomorph_normal_chart_restrict (Φ k j) (U j) (hU j) (hs k j)
  have hcoeff (k j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U j) :
      (g k).pullbackCoefficients (ChartDistance.chartParametrization U hU (e k j)) x =
        (g k).pullbackCoefficients (Φ k j) x :=
    (g k).pullbackCoefficients_chartParametrization_restrict U hU j (Φ k j) hx
  have hcoeffBound (j : ℕ) : LocallyEventuallyBoundedDerivatives (U j)
      (fun k => (g k).pullbackCoefficients (ChartDistance.chartParametrization U hU (e k j))) := by
    have hb := locallyEventuallyBoundedDerivatives_of_tendsto_jets (hU j)
      (show ContDiffOn ℝ ∞ (h j).euclideanCoefficients (U j) from
        fun x _ => ((h j).contDiffAt_euclideanCoefficients x).contDiffWithinAt) (hjets j)
    intro C hC hCU m
    obtain ⟨B, hB⟩ := hb C hC hCU m
    refine ⟨B, hB.mono ?_⟩
    intro k hk x hx
    have heq : (g k).pullbackCoefficients (ChartDistance.chartParametrization U hU (e k j))
        =ᶠ[𝓝 x] (g k).pullbackCoefficients (Φ k j) :=
      Filter.eventuallyEq_of_mem ((hU j).mem_nhds (hCU hx)) (hcoeff k j)
    rw [(heq.iteratedFDeriv ℝ m).self_of_nhds]
    exact hk x hx
  have hlow (j : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (_ : IsCompact C) (hCU : C ⊆ U j) :
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ C, ∀ v,
        a * ‖v‖ ^ 2 ≤ (g k).pullbackCoefficients
          (ChartDistance.chartParametrization U hU (e k j)) x v v := by
    refine ⟨1 / 4, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro k x hx v
    rw [hcoeff k j x (hCU hx)]
    exact (helliptic k j x (Metric.ball_subset_ball (by linarith : r ≤ 3 * r) (hCU hx)) v).1
  exact ChartDistance.locallyEventuallyBoundedDerivatives_source_transition U hU hd
    (fun _ => 3 / 2) hLip (fun _ => 1 / 2) (fun _ => by norm_num)
    (fun k j x y => (hdist k j x y).1) hopen hconn hsmooth g hcoeffBound hlow i j

end PoincareConjecture.RiemannianMetric
