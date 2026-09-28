import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Curvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem scalar_bilinear_eq_of_basis {n : ℕ}
    {B B' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (h : ∀ a b : Fin n, B (EuclideanSpace.basisFun (Fin n) ℝ a)
      (EuclideanSpace.basisFun (Fin n) ℝ b) =
        B' (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) :
    B = B' := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  intro a
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  exact h a

theorem SmoothSpacetimeEmbedding.scalarCurvature_eq_of_coordinate_germ
    {n : ℕ} {T' T : ℝ} {C D : FlowCarrier n}
    {F : BasedFlow n T' T C} {G : BasedFlow n T' T D} {U : Set C.carrier}
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U)) (hU : IsOpen U)
    (q : C.carrier) (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target ∧ (extChartAt (𝓡 n) q).symm p.2 ∈ U)
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
    (h : ∀ᶠ x in 𝓝 p.2, ∀ a b : Fin n,
      gE.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b) =
      C.coordinateCoefficient q (pullbackInnerValue F G e) a b (p.1, x)) :
    DE.scalarCurvature p.2 = (G.flow.connection p.1).scalarCurvature
      ((e.toFun (p.1, (extChartAt (𝓡 n) q).symm p.2)).2) := by
  let c := extChartAt (𝓡 n) q
  let f : C.carrier → D.carrier := fun y => (e.toFun (p.1, y)).2
  let W := c.target ∩ c.symm ⁻¹' U
  have hW : IsOpen W :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) hU
  have hc (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm x :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hx.1).contMDiffAt
      (extChartAt_target_mem_nhds' hx.1)
  have hf (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ f (c.symm x) :=
    e.spatialMap_contMDiffAt hU ht hx.2
  have hd (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W) :
      mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x =
        (mfderiv (𝓡 n) (𝓡 n) f (c.symm x)).comp
          (mfderiv (𝓡 n) (𝓡 n) c.symm x) :=
    mfderiv_comp x ((hf x hx).mdifferentiableAt (by simp))
      ((hc x hx).mdifferentiableAt (by simp))
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp (inter_mem (hW.mem_nhds hp) h)
  apply DE.scalarCurvature_eq_of_local_isometry (G.flow.connection p.1) hVo
    (fun x hx => ((hf x (hV hx).1).comp x (hc x (hV hx).1)).contMDiffWithinAt)
    (x := p.2) (hx := hpV)
  intro x hx
  have hB : gE.euclideanCoefficients x =
      (G.metricAt p.1).pullbackCoefficients (f ∘ c.symm) x := by
    apply scalar_bilinear_eq_of_basis
    intro a b
    rw [(hV hx).2 a b]
    change _ = (G.metricAt p.1).inner (f (c.symm x))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ a))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ b))
    rw [hd x (hV hx).1]
    rfl
  exact fun u v => congrArg (fun B => B u v) hB

namespace PointedGeometricConvergence

theorem tendsto_scalarCurvature
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (t : ℝ) (ht : t ∈ Ioo T' T)
    (x : G.limitCarrier.carrier) :
    Tendsto (fun k : ℕ => ((S.flow (G.subsequence k)).flow.connection t).scalarCurvature
      ((G.embedding k).toFun (t, x)).2) atTop
      (𝓝 ((G.limitFlow.flow.connection t).scalarCurvature x)) := by
  classical
  let c := extChartAt (𝓡 n) x
  let p := c x
  have hp : p ∈ c.target := c.map_source (mem_extChartAt_source x)
  have hcx : (extChartAt (𝓡 n) x).symm p = x := c.left_inv (mem_extChartAt_source x)
  obtain ⟨g, D, V, hVo, hpV, _, heq⟩ := G.limitCarrier.exists_local_coordinate_realization
    (G.limitFlow.metricAt t) x t p hp
  have hg : ∀ᶠ y in 𝓝 p, ∀ a b : Fin n,
      g.euclideanCoefficients y (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b) =
      G.limitCarrier.coordinateCoefficient x
        (fun _ y v w => G.limitCarrier.metricInner (G.limitFlow.metricAt t) y v w)
        a b (t, y) := Filter.Eventually.mono (hVo.mem_nhds hpV) heq
  have hreal : ∀ᶠ k : ℕ in atTop,
      ∃ gd : Σ g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)), LeviCivitaData g,
        ∀ᶠ y in 𝓝 p, ∀ a b : Fin n,
          gd.1.euclideanCoefficients y (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ b) =
          G.limitCarrier.coordinateCoefficient x
            (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k))
            a b (t, y) := by
    filter_upwards [G.eventually_exists_local_coordinate_realization x (t, p) ht hp]
      with k hk
    obtain ⟨gk, Dk, Vk, hVko, hpVk, heqk⟩ := hk
    exact ⟨⟨gk, Dk⟩, Filter.Eventually.mono (hVko.mem_nhds hpVk) heqk⟩
  obtain ⟨gd, hgd⟩ := hreal.choice
  have hscalar := LeviCivitaData.tendsto_scalarCurvature_of_scalar_metric_jets
    (l := atTop) (fun k => (gd k).2) D p (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (by
      intro r _ a b
      simp only [OrthonormalBasis.coe_toBasis]
      erw [G.limitCarrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        x _ t p g hg r a b]
      apply (G.tendsto_coordinate_spatial_metricJet x r a b (t, p) ht hp).congr'
      filter_upwards [hgd] with k hk
      exact (G.limitCarrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        x _ t p (gd k).1 hk r a b).symm)
  have hlim : D.scalarCurvature p = (G.limitFlow.flow.connection t).scalarCurvature x := by
    simpa only [hcx] using G.limitCarrier.scalarCurvature_eq_of_coordinate_germ
      (G.limitFlow.metricAt t) (G.limitFlow.flow.connection t) x t p hp g D hg
  rw [hlim] at hscalar
  apply hscalar.congr'
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (isCompact_singleton (x := x))
  filter_upwards [hgd, eventually_ge_atTop j] with k hk hjk
  simpa only [hcx] using (G.embedding k).scalarCurvature_eq_of_coordinate_germ
    (G.exhaustion_open k) x (t, p) ht
    ⟨hp, by rw [hcx]; exact G.exhaustion_monotone hjk (hj (mem_singleton x))⟩
    (gd k).1 (gd k).2 hk

theorem tendsto_scalarCurvature_at_zero_base
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (hzero : T' < 0 ∧ 0 < T) :
    Tendsto (fun k : ℕ => ((S.flow (G.subsequence k)).flow.connection 0).scalarCurvature
      (S.flow (G.subsequence k)).base) atTop
      (𝓝 ((G.limitFlow.flow.connection 0).scalarCurvature G.limitFlow.base)) := by
  simpa only [G.base_preserving] using G.tendsto_scalarCurvature 0 hzero G.limitFlow.base

end PointedGeometricConvergence

end PoincareConjecture
