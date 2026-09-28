import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.SelectedParabolicApplication
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.MixedBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff Bundle
open PoincareConjecture.ChartDistance

universe u

namespace PoincareConjecture.M28







structure SelectedParabolicApplicationBase
    {M : ℕ → Type u} [∀ k : ℕ, MetricSpace (M k)]
    [∀ k : ℕ, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k : ℕ, IsManifold (𝓡 3) ∞ (M k)]
    (tau A : ℝ) where
  tau_pos : 0 < tau
  U : ℕ → Set (EuclideanSpace ℝ (Fin 3))
  isOpen_U : ∀ i, IsOpen (U i)
  convex_U : ∀ i, Convex ℝ (U i)
  piece_nonempty : ∀ i, Nonempty (Piece U i)
  embedding : ∀ k i, Piece U i → M k
  distance_limit : ∀ i j, C(Piece U i × Piece U j, ℝ)
  distance_limit_spec : ∀ i j, TendstoLocallyUniformly
    (fun k (p : Piece U i × Piece U j) =>
      dist (embedding k i p.1) (embedding k j p.2))
      (distance_limit i j) atTop
  lipschitz_constant : ℕ → ℝ≥0
  lipschitz : ∀ k i, LipschitzWith (lipschitz_constant i) (embedding k i)
  lower_constant : ℕ → ℝ
  lower_constant_pos : ∀ i, 0 < lower_constant i
  lower_distance : ∀ k i x y,
    lower_constant i * dist x y ≤ dist (embedding k i x) (embedding k i y)
  open_embedding : ∀ k i, Topology.IsOpenEmbedding (embedding k i)
  ball_preconnected : ∀ k (p : M k) r, IsPreconnected (ball p r)
  smooth :
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece U i) :=
      fun i => (isOpen_U i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ k i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (embedding k i)
  transition_bounds : ∀ i j, LocallyEventuallyBoundedDerivatives
    (Subtype.val '' overlap (fun i j => distance_limit i j) i j)
    (fun k => coordinateRepresentative (U := U) (hU := isOpen_U)
      (i := i) (j := j)
      (fun x : Piece U i => Function.invFun (embedding k j) (embedding k i x)))
  base_index : ℕ
  base_point : Piece U base_index
  range_bound : ∀ i (x : Piece U i),
    distance_limit base_index i (base_point, x) < A
  compact_cover : ∀ R : ℝ, 0 < R → R < A → ∃ s : Finset ℕ,
    ∃ K : ∀ i, Set (Piece U i), (∀ i ∈ s, IsCompact (K i)) ∧
      ∀ᶠ k in atTop,
        ball (embedding k base_index base_point) R ⊆
          ⋃ i ∈ s, embedding k i '' K i
  flow : ∀ k, RicciFlow 3 (M k) (Icc (-tau) 0)
  distance_eq : ∀ k (x y : M k),
    edist x y = ((flow k).metric 0).edist x y

set_option synthInstance.maxHeartbeats 100000 in


theorem SelectedParabolicApplicationBase.partial_flow_of_compact_spatial_bounds
    {A tau : ℝ} (hA : 0 < A)
    {M : ℕ → Type u} [∀ k : ℕ, MetricSpace (M k)]
    [∀ k : ℕ, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k : ℕ, IsManifold (𝓡 3) ∞ (M k)]
    {B : SelectedParabolicApplicationBase (M := M) tau A}
    [∀ i, Nonempty (Piece B.U i)]
    (hchart : ∀ k i x, x ∈ B.U i →
      (mfderiv (𝓡 3) (𝓡 3)
        (chartParametrization B.U B.isOpen_U (B.embedding k i)) x).IsInvertible)
    (helliptic : ∀ i V, IsCompact V → V ⊆ B.U i →
      ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, 0 ≤ b ∧ ∀ᶠ k in atTop,
        ∀ t ∈ Icc (-tau) 0, ∀ x ∈ V, ∀ v,
          a * ‖v‖ ^ 2 ≤
              ((B.flow k).metric t).pullbackCoefficients
                (chartParametrization B.U B.isOpen_U (B.embedding k i)) x v v ∧
            ((B.flow k).metric t).pullbackCoefficients
                (chartParametrization B.U B.isOpen_U (B.embedding k i)) x v v ≤
              b * ‖v‖ ^ 2)
    (hcurvature : ∀ i V, IsCompact V → V ⊆ B.U i → ∀ s, ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ k in atTop, ∀ t ∈ Ioo (-tau) 0, ∀ x ∈ V,
        ((B.flow k).connection t).curvatureDerivativeNorm s
          (chartParametrization B.U B.isOpen_U (B.embedding k i) x) ≤ K)
    (hinitial : ∀ i V, IsCompact V → V ⊆ B.U i → ∀ m, ∃ Z : ℝ, 0 ≤ Z ∧
      ∀ᶠ k in atTop, ∀ x ∈ V,
        ‖iteratedFDeriv ℝ m
          (((B.flow k).metric 0).pullbackCoefficients
            (chartParametrization B.U B.isOpen_U (B.embedding k i))) x‖ ≤ Z) :
    Nonempty (PartialLimitWindowExport B.flow
      (fun k => B.embedding k B.base_index B.base_point) A) := by
  letI : ∀ i, Nonempty (Piece B.U i) := B.piece_nonempty
  letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece B.U i) :=
    fun i => (B.isOpen_U i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI : ∀ i, IsManifold (𝓡 3) ∞ (Piece B.U i) :=
    fun i => (B.isOpen_U i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let H : SelectedParabolicApplicationData (M := M) tau A := by
    refine {
      tau_pos := B.tau_pos
      U := B.U
      isOpen_U := B.isOpen_U
      convex_U := B.convex_U
      piece_nonempty := B.piece_nonempty
      embedding := B.embedding
      distance_limit := B.distance_limit
      distance_limit_spec := B.distance_limit_spec
      lipschitz_constant := B.lipschitz_constant
      lipschitz := B.lipschitz
      lower_constant := B.lower_constant
      lower_constant_pos := B.lower_constant_pos
      lower_distance := B.lower_distance
      open_embedding := B.open_embedding
      ball_preconnected := B.ball_preconnected
      smooth := B.smooth
      transition_bounds := B.transition_bounds
      base_index := B.base_index
      base_point := B.base_point
      radius_pos := hA
      range_bound := B.range_bound
      compact_cover := B.compact_cover
      flow := B.flow
      distance_eq := B.distance_eq
      metric_jets := ?_
      positive_ellipticity := ?_ }
    · intro i K hK hKU m
      let V : Set (EuclideanSpace ℝ (Fin 3)) := Prod.snd '' K
      have hV : IsCompact V := hK.image continuous_snd
      have hVU : V ⊆ B.U i := by
        rintro x ⟨z, hz, rfl⟩
        exact (hKU hz).2
      obtain ⟨a, ha, b, hb, hell⟩ := helliptic i V hV hVU
      have hmix :=
        eventually_within_bounds_closed_backward_of_curvature
          (l := atTop) B.tau_pos (F := B.flow)
          (U := fun _ : ℕ => B.U i) (V := fun _ : ℕ => V)
          (e := fun k => chartParametrization B.U B.isOpen_U (B.embedding k i))
          (fun _ => B.isOpen_U i) (fun _ => hVU)
          (fun k => contMDiffOn_chartParametrization B.U B.isOpen_U
            (B.smooth k i).contMDiff)
          (fun k x hx => hchart k i x hx) ha hb
          (hell.mono fun k hk t ht x hx v => hk t ht x hx v)
          (hcurvature i V hV hVU) (hinitial i V hV hVU)
      obtain ⟨bound, hbound, htail⟩ := hmix m
      refine ⟨bound, ?_⟩
      filter_upwards [htail] with k hk
      intro z hz
      have hzJ := hKU hz
      exact hk z ⟨hzJ.1, ⟨z, hz, rfl⟩⟩
    · intro t ht i x hx
      obtain ⟨a, ha, b, hb, htail⟩ :=
        helliptic i {x} isCompact_singleton (singleton_subset_iff.mpr hx)
      refine ⟨a, ha, ?_⟩
      filter_upwards [htail] with k hk v
      exact (hk t ht x (mem_singleton x) v).1
  exact H.partial_flow

end PoincareConjecture.M28
