import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.UnscaledSource








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
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
  let f : C.carrier → D.carrier := fun y ↦ (e.toFun (p.1, y)).2
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
    (fun x hx ↦ ((hf x (hV hx).1).comp x (hc x (hV hx).1)).contMDiffWithinAt)
    (x := p.2) (hx := hpV)
  intro x hx
  have hB : gE.euclideanCoefficients x =
      (G.metricAt p.1).pullbackCoefficients (f ∘ c.symm) x := by
    apply bilinear_eq_of_basis
    intro a b
    rw [(hV hx).2 a b]
    change _ = (G.metricAt p.1).inner (f (c.symm x))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ a))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ b))
    rw [hd x (hV hx).1]
    rfl
  exact fun u v ↦ congrArg (fun B ↦ B u v) hB

namespace PointedGeometricConvergence



theorem tendsto_scalarCurvature
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (t : ℝ) (ht : t ∈ Ioo T' T)
    (x : G.limitCarrier.carrier) :
    Tendsto (fun k ↦ ((S.flow (G.subsequence k)).flow.connection t).scalarCurvature
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
        (fun _ y v w ↦ (G.limitFlow.metricAt t).inner y v w) a b (t, y) :=
    Filter.Eventually.mono (hVo.mem_nhds hpV) heq
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
    (l := atTop) (fun k ↦ (gd k).2) D p (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (by
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

end PointedGeometricConvergence

namespace AncientPointedGeometricConvergence



theorem tendsto_scalarCurvature
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {T : ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (Iio T)) {p : ∀ k, (C k).carrier}
    (G : AncientPointedGeometricConvergence C (fun k ↦ (F k).metric) p T)
    (hT : 0 < T) (t : ℝ) (ht : t < T) (x : G.limitCarrier.carrier) :
    Tendsto (fun k ↦ ((F (G.subsequence k)).connection t).scalarCurvature
      (G.embedding k x)) atTop (𝓝 ((G.limitFlow.connection t).scalarCurvature x)) := by
  obtain ⟨a, b, ha, hb, hbT, htime⟩ := exists_ancient_window_of_isCompact hT
    isCompact_singleton (singleton_subset_iff.mpr ht)
  have hsub : ∀ k : ℕ, Ioo a b ⊆ Iio T := fun _ _ hs ↦ hs.2.trans hbT
  let W := G.window F (ha.trans hb) hbT.le 0 hsub
  have h := W.tendsto_scalarCurvature t (htime (mem_singleton t)) x
  simpa only [W, window, sourceWindowSequence, FlowCarrier.basedWindow,
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow, SmoothSpacetimeEmbedding.of_spatial,
    Nat.add_zero, id_eq] using h



theorem scalarCurvature_lower_bound_of_source
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {T : ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (Iio T)) {p : ∀ k, (C k).carrier}
    (G : AncientPointedGeometricConvergence C (fun k ↦ (F k).metric) p T)
    (hT : 0 < T) (t : ℝ) (ht : t < T) {c : ℝ}
    (hlower : ∀ k, ∀ x : (C k).carrier, c ≤ ((F k).connection t).scalarCurvature x)
    (x : G.limitCarrier.carrier) : c ≤ (G.limitFlow.connection t).scalarCurvature x := by
  apply ge_of_tendsto (G.tendsto_scalarCurvature F hT t ht x)
  exact Eventually.of_forall fun k ↦ hlower (G.subsequence k) (G.embedding k x)

end AncientPointedGeometricConvergence

end PoincareConjecture

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)



theorem unscaledPointedLimit_scalar_lower_bound
    (hC : RicciFlowCurvatureTheory.{u}) (q : ℕ → M)
    (L : AncientPointedGeometricConvergence
      (fun _ ↦ AncientRescalingSequence.smallRescalingCarrier (M := M))
      (fun _ ↦ G.unscaledSourceFlow.shrink.metric)
      (fun k ↦ equivShrink M (q k)) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t < 1, ∀ x : L.limitCarrier.carrier,
      c / (1 - t) ≤ (L.limitFlow.connection t).scalarCurvature x := by
  obtain ⟨c, hc, hlower⟩ := G.unscaledSourceFlow_scalar_lower_bound hC
  refine ⟨c, hc, fun t ht x ↦ ?_⟩
  let F' (_k : ℕ) : RicciFlow 3
      (AncientRescalingSequence.smallRescalingCarrier (n := 3) (M := M)).carrier (Iio 1) :=
    G.unscaledSourceFlow.shrink
  have hs : ∀ k, ∀ y : (AncientRescalingSequence.smallRescalingCarrier (n := 3) (M := M)).carrier,
      c / (1 - t) ≤ ((F' k).connection t).scalarCurvature y := by
    intro k y
    change c / (1 - t) ≤ (G.unscaledSourceFlow.shrink.connection t).scalarCurvature y
    rw [RicciFlow.shrink_scalarCurvature]
    exact hlower t ht _
  exact AncientPointedGeometricConvergence.scalarCurvature_lower_bound_of_source
    (C := fun _ ↦ AncientRescalingSequence.smallRescalingCarrier (n := 3) (M := M))
    (p := fun k ↦ equivShrink M (q k)) F' L (by norm_num) t ht hs x

end PoincareConjecture.ShrinkingSolitonFlow
