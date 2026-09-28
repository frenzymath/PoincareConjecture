import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.ReducedGeometry.OrdinaryProductPaths
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Noncollapse.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenInclusion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M]

def ordinaryMetricBallSource (g : RiemannianMetric n M) (p : M) (r : ℝ) :
    Opens M := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  exact ⟨g.ball p r, isOpen_lt (continuous_const.edist continuous_id) continuous_const⟩

namespace OrdinaryProductRicciGeometry

variable {I : SpacetimeInterval} {g : ℝ → RiemannianMetric n M}

theorem horizontalCurvatureNorm_eq (P : OrdinaryProductRicciGeometry g I)
    (c : MetricLeviCivitaFamily g) (p : P.product.spacetime.Point) :
    horizontalCurvatureNorm P.leafwiseConnection p =
      (c (P.product.spacetime.timeFunction p)).curvatureTensorNorm (P.pointMap p) := by
  obtain ⟨t, x⟩ := p
  have hs := (c t.val).curvatureTensorNorm_eq_of_local_isometry
    (P.leafwiseConnection.sliceConnection t.val) isOpen_univ
    (P.product.sliceIdentification t).contMDiff.contMDiffOn
    (fun y _ v w => (P.product.sliceMetric_eq t y v w).symm) (mem_univ x)
  have heq : P.product.sliceIdentification t x =
      (⟨(t, x), rfl⟩ : (P.product.slices t.val).Point) := by
    apply Subtype.ext
    exact P.product.sliceIdentification_eq t x
  rw [heq] at hs
  exact hs.symm

variable [T2Space M] [SecondCountableTopology M]

theorem exists_actualBallCylinder (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I)
    (T : ℝ) (hT : T ∈ I.domain) (p : M) (r : ℝ) (hr : 0 < r)
    (J : SpacetimeInterval) (hJ : J.domain = Icc (T - r ^ 2) T)
    (hJI : J.domain ⊆ I.domain)
    (hcurv : ∀ s ∈ Icc (T - r ^ 2) T, ∀ q ∈ (F.metric T).ball p r,
      (F.connection s).curvatureTensorNorm q ≤ r⁻¹ ^ 2) :
    Nonempty (M15ActualBallCylinder (P.ricciFlowLGeometry F) T
      (P.product.sliceIdentification ⟨T, hT⟩ p) r J
      (ordinaryMetricBallSource (F.metric T) p r)) := by
  let U := ordinaryMetricBallSource (F.metric T) p r
  let e := P.product.sliceIdentification ⟨T, hT⟩
  obtain ⟨ct, hct⟩ := P.product.compatible.cylinder_time_restrict M I J hJI
    P.product.productCylinder
  obtain ⟨cs, hcs⟩ := P.product.compatible.cylinder_open_restrict M J ct U
  obtain ⟨gm⟩ := P.product.compatible.cylinder_metric U J cs
  have hmap (s : (P.product.timeIntervals.interval J).Point) (q : U) :
      cs.toSpacetime (s, q) = (⟨s.val, hJI s.property⟩, q.val) := by
    rw [hcs, hct, P.product.productCylinder_eq]
    rfl
  have hbase : T ∈ J.domain := by rw [hJ]; exact ⟨by nlinarith [sq_nonneg r], le_rfl⟩
  refine ⟨{
    radius_pos := hr
    interval_domain := hJ
    base_mem := hbase
    embedding := cs
    metric := gm
    source_map := fun q : U => e q.val
    source_map_embedding := e.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    source_map_range := ?_
    based := ?_
    source_map_smooth := (e.contMDiff.comp contMDiff_subtype_val).contMDiffOn
    source_map_differential_injective := ?_
    curvature_bound := ?_ }⟩
  · change range (fun q : U => e q.val) = _
    rw [show range (fun q : U => e q.val) = e '' (F.metric T).ball p r by
      ext y; constructor
      · rintro ⟨q, rfl⟩; exact ⟨q.val, q.property, rfl⟩
      · rintro ⟨q, hq, rfl⟩; exact ⟨⟨q, hq⟩, rfl⟩]
    exact RiemannianMetric.image_ball_diffeomorph (F.metric T)
      (P.product.slices T).metricOnPoints e
      (fun q v w => (P.product.sliceMetric_eq ⟨T, hT⟩ q v w).symm) p r
  · intro q
    rw [hmap, P.product.sliceIdentification_eq]
  · intro q
    rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_restrict U e
      (e.contMDiff.mdifferentiable (by simp) q.val)]
    exact ((F.metric T).mfderiv_bijective_of_pullback_eq
      (P.product.slices T).metricOnPoints q.val
      (fun v w => P.product.sliceMetric_eq ⟨T, hT⟩ q.val v w)).injective
  · intro s q
    change horizontalCurvatureNorm P.leafwiseConnection (cs.toSpacetime (s, q)) ≤ _
    rw [hmap, P.horizontalCurvatureNorm_eq F.connection]
    exact hcurv s.val (hJ ▸ s.property) q.val q.property

end OrdinaryProductRicciGeometry
end PoincareConjecture
