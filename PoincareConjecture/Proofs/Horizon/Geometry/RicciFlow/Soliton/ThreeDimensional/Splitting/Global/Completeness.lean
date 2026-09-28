import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.SmoothCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Orientation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Complete
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RicciFlow.Splitting

theorem unitRicciKernelT2Space_of_covering
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] [T2Space B]
    {f : E → B} (hf : IsCoveringMap f) : T2Space E := by
  constructor
  intro a b hab
  by_cases he : f a = f b
  · obtain ⟨hd, U, haU, hU, hfU, H, hH⟩ := hf (f a)
    let : DiscreteTopology (f ⁻¹' {f a}) := hd
    let : T2Space (f ⁻¹' U) := H.symm.t2Space
    let a' : f ⁻¹' U := ⟨a, haU⟩
    let b' : f ⁻¹' U := ⟨b, by change f b ∈ U; rwa [← he]⟩
    have hne : a' ≠ b' := fun h => hab (congrArg Subtype.val h)
    obtain ⟨V, W, hV, hW, haV, hbW, hVW⟩ := t2_separation hne
    exact ⟨Subtype.val '' V, Subtype.val '' W,
      hfU.isOpenMap_subtype_val V hV, hfU.isOpenMap_subtype_val W hW,
      ⟨a', haV, rfl⟩, ⟨b', hbW, rfl⟩,
      disjoint_image_of_injective Subtype.val_injective hVW⟩
  · obtain ⟨V, W, hV, hW, haV, hbW, hVW⟩ := t2_separation he
    exact ⟨f ⁻¹' V, f ⁻¹' W, hV.preimage hf.continuous,
      hW.preimage hf.continuous, haV, hbW, hVW.preimage f⟩

private theorem isProperMap_of_finite_covering
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {f : E → B} (hf : IsCoveringMap f)
    (hfinite : ∀ x, Finite (f ⁻¹' {x})) : IsProperMap f := by
  choose U hxU hU hfU H hH using fun x => (hf x).2
  have hcover : TopologicalSpace.IsOpenCover (fun x => ⟨U x, hU x⟩) :=
    TopologicalSpace.IsOpenCover.of_sets hU (iUnion_eq_univ_iff.mpr fun x => ⟨x, hxU x⟩)
  have hclosed : IsClosedMap f := by
    apply hcover.isClosedMap_iff_restrictPreimage.mpr
    intro x
    let := hfinite x
    have heq : (U x).restrictPreimage f = Prod.fst ∘ H x := by
      funext p
      exact Subtype.ext (hH x p).symm
    rw [heq]
    exact isClosedMap_fst_of_compactSpace.comp (H x).isClosedMap
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨hf.continuous, hclosed, fun x => ?_⟩
  let := hfinite x
  exact (Set.toFinite (f ⁻¹' {x})).isCompact

theorem metricComplete_of_proper_metric_pullback
    {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N]
    [T3Space M] [T3Space N]
    (gM : RiemannianMetric n M) (gN : RiemannianMetric m N) {F : M → N}
    (hF : ContMDiff (𝓡 n) (𝓡 m) ∞ F) (hp : IsProperMap F)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (F x)
        (mfderiv (𝓡 n) (𝓡 m) F x v) (mfderiv (𝓡 n) (𝓡 m) F x w))
    (hc : MetricComplete gN) : MetricComplete gM := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨gM.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨gM.inner, gM.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : N → Type _) :=
    ⟨gN.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin m))
      (TangentSpace (𝓡 m) : N → Type _) :=
    ⟨⟨gN.inner, gN.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 m) N
  let : CompleteSpace N := hc
  have hLip : LipschitzWith 1 F := by
    intro x y
    change gN.edist (F x) (F y) ≤ (1 : ℝ≥0∞) * gM.edist x y
    simpa only [one_mul] using
      RiemannianMetric.edist_map_le_of_metric_pullback gM gN hF hinner x y
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete
    (hLip.uniformContinuous.comp_cauchySeq hu)
  have hyc : MapClusterPt y (map u atTop) F := by
    simpa only [MapClusterPt, map_map, Function.comp_def] using hy.mapClusterPt
  obtain ⟨x, _, hx⟩ := hp.clusterPt_of_mapClusterPt hyc
  exact ⟨x, le_nhds_of_cauchy_adhp hu hx⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem unitRicciKernelT3Space [T2Space M] (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D)) :
    T3Space (UnitRicciKernel D) := by
  let : T2Space (UnitRicciKernel D) := unitRicciKernelT2Space_of_covering hc
  let : T1Space (UnitRicciKernel D) := T2Space.t1Space
  let : T0Space (UnitRicciKernel D) := T1Space.t0Space
  let : R1Space (UnitRicciKernel D) := T2Space.r1Space
  let := unitRicciKernelChartedSpace D hc
  let : LocallyCompactSpace (UnitRicciKernel D) :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) (UnitRicciKernel D)
  exact { toRegularSpace :=
    RegularSpace.of_hasBasis isCompact_isClosed_basis_nhds (fun _ _ ⟨_, _, h⟩ => h) }

theorem unitRicciKernelProjection_isProperMap (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D))
    (hcard : ∀ x, Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2) :
    IsProperMap (unitRicciKernelProjection D) :=
  isProperMap_of_finite_covering hc fun x => Nat.finite_of_card_ne_zero (by rw [hcard x]; decide)

theorem unitRicciKernelMetric_complete [T3Space M] (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D))
    (hcard : ∀ x, Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2)
    (hcomplete : MetricComplete g) :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    letI := unitRicciKernelT3Space D hc
    MetricComplete (unitRicciKernelMetric D hc) := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  let := unitRicciKernelT3Space D hc
  exact metricComplete_of_proper_metric_pullback (unitRicciKernelMetric D hc) g
    (unitRicciKernelProjection_isLocalDiffeomorph D hc).contMDiff
    (unitRicciKernelProjection_isProperMap D hc hcard) (fun _ _ _ => rfl) hcomplete

end PoincareConjecture.RicciFlow.Splitting
