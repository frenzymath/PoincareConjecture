import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence.LocalRealization
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.CurvatureBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem bilinear_eq_of_basis {n : ℕ}
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

namespace FlowCarrier

theorem curvatureTensorNorm_eq_of_coordinate_germ
    {n : ℕ} (C : FlowCarrier n) (gM : C.metric)
    (DM : @LeviCivitaData n C.carrier C.topologicalSpace C.chartedSpace C.isManifold gM)
    (q : C.carrier) (t : ℝ) (p : EuclideanSpace ℝ (Fin n))
    (hp :
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      p ∈ (extChartAt (𝓡 n) q).target)
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
    (h : ∀ᶠ x in 𝓝 p, ∀ a b : Fin n,
      gE.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b) =
      C.coordinateCoefficient q (fun _ y v w => C.metricInner gM y v w) a b (t, x)) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    DE.curvatureTensorNorm p = DM.curvatureTensorNorm ((extChartAt (𝓡 n) q).symm p) := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let c := extChartAt (𝓡 n) q
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp
    (inter_mem (extChartAt_target_mem_nhds' hp) h)
  apply DE.curvatureTensorNorm_eq_of_local_isometry DM hVo
    (fun x hx => (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q
      (hV hx).1).contMDiffAt (extChartAt_target_mem_nhds' (hV hx).1)
        |>.contMDiffWithinAt) (x := p) (hx := hpV)
  · intro x hx
    have hB : gE.euclideanCoefficients x = gM.pullbackCoefficients c.symm x :=
      bilinear_eq_of_basis (hV hx).2
    intro u v
    exact congrArg (fun B => B u v) hB

end FlowCarrier

namespace SmoothSpacetimeEmbedding

theorem curvatureTensorNorm_eq_of_coordinate_germ
    {n : ℕ} {T' T : ℝ} {C D : FlowCarrier n}
    {F : BasedFlow n T' T C} {G : BasedFlow n T' T D} {U : Set C.carrier}
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen C.carrier C.topologicalSpace U)
    (q : C.carrier) (p : ℝ × EuclideanSpace ℝ (Fin n))
    (ht : p.1 ∈ Ioo T' T)
    (hp :
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      p.2 ∈ (extChartAt (𝓡 n) q).target ∧ (extChartAt (𝓡 n) q).symm p.2 ∈ U)
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
    (h : ∀ᶠ x in 𝓝 p.2, ∀ a b : Fin n,
      gE.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b) =
      C.coordinateCoefficient q (pullbackInnerValue F G e) a b (p.1, x)) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
    DE.curvatureTensorNorm p.2 = (G.flow.connection p.1).curvatureTensorNorm
      ((e.toFun (p.1, (extChartAt (𝓡 n) q).symm p.2)).2) := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : TopologicalSpace D.carrier := D.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  let : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
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
  have hderiv (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W) :
      mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x =
        (mfderiv (𝓡 n) (𝓡 n) f (c.symm x)).comp
          (mfderiv (𝓡 n) (𝓡 n) c.symm x) :=
    mfderiv_comp x ((hf x hx).mdifferentiableAt (by simp))
      ((hc x hx).mdifferentiableAt (by simp))
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp (inter_mem (hW.mem_nhds hp) h)
  apply DE.curvatureTensorNorm_eq_of_local_isometry (G.flow.connection p.1) hVo
    (fun x hx => ((hf x (hV hx).1).comp x (hc x (hV hx).1)).contMDiffWithinAt)
    (x := p.2) (hx := hpV)
  · intro x hx
    have hcoeff := (hV hx).2
    have hB : gE.euclideanCoefficients x =
        (G.metricAt p.1).pullbackCoefficients (f ∘ c.symm) x := by
      apply bilinear_eq_of_basis
      intro a b
      rw [hcoeff a b]
      change _ = (G.metricAt p.1).inner (f (c.symm x))
        (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ a))
        (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ b))
      rw [hderiv x (hV hx).1]
      rfl
    intro u v
    exact congrArg (fun B => B u v) hB

end SmoothSpacetimeEmbedding

namespace PointedGeometricConvergence

theorem tendsto_curvatureTensorNorm
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (t : ℝ) (ht : t ∈ Ioo T' T)
    (x : G.limitCarrier.carrier) :
    letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
      G.limitCarrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
    Tendsto (fun k : ℕ =>
      let C := S.carrier (G.subsequence k)
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ((S.flow (G.subsequence k)).flow.connection t).curvatureTensorNorm
        ((G.embedding k).toFun (t, x)).2)
      atTop (𝓝 ((G.limitFlow.flow.connection t).curvatureTensorNorm x)) := by
  classical
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
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
  have hnorm := LeviCivitaData.tendsto_curvatureTensorNorm_of_scalar_metric_jets
    (l := atTop) (fun k => (gd k).2) D p (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (by
      intro r _ a b
      simp only [OrthonormalBasis.coe_toBasis]
      erw [G.limitCarrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        x _ t p g hg r a b]
      apply (G.tendsto_coordinate_spatial_metricJet x r a b (t, p) ht hp).congr'
      filter_upwards [hgd] with k hk
      exact (G.limitCarrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        x _ t p (gd k).1 hk r a b).symm)
  have hlim : D.curvatureTensorNorm p =
      (G.limitFlow.flow.connection t).curvatureTensorNorm x := by
    simpa only [hcx] using G.limitCarrier.curvatureTensorNorm_eq_of_coordinate_germ
      (G.limitFlow.metricAt t) (G.limitFlow.flow.connection t) x t p hp g D hg
  rw [hlim] at hnorm
  apply hnorm.congr'
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (isCompact_singleton (x := x))
  filter_upwards [hgd, eventually_ge_atTop j] with k hk hjk
  simpa only [hcx] using (G.embedding k).curvatureTensorNorm_eq_of_coordinate_germ
    (G.exhaustion_open k) x (t, p) ht
    ⟨hp, by rw [hcx]; exact G.exhaustion_monotone hjk (hj (mem_singleton x))⟩
    (gd k).1 (gd k).2 hk

theorem curvatureTensorNorm_le
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (G : PointedGeometricConvergence H.sequence) (A : ℝ) (hA : 0 < A) :
    letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
      G.limitCarrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Ioo T' T,
      ∀ x ∈ G.limitFlow.ballAt s A, ∀ t ∈ Ioo T' T,
        (G.limitFlow.flow.connection t).curvatureTensorNorm x ≤ K := by
  apply G.curvatureTensorNorm_le_of_tendsto H A hA
  intro s hs x hx t ht
  exact G.tendsto_curvatureTensorNorm t ht x

end PointedGeometricConvergence
end PoincareConjecture
