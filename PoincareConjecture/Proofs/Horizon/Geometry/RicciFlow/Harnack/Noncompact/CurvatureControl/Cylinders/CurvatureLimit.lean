import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

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

namespace LeviCivitaData



theorem nonnegativeCurvatureOperator_of_scalar_metric_jets
    {n : ℕ} {α : Type*} {l : Filter α} [l.NeBot]
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ a, LeviCivitaData (gseq a)) (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ r : ℕ, r ≤ 2 → ∀ a c : ι,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) x) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x)))
    (hpos : ∀ᶠ i in l, (Dseq i).NonnegativeCurvatureOperator x) :
    D.NonnegativeCurvatureOperator x := by
  classical
  obtain ⟨hzero, hone, htwo⟩ :=
    RiemannianMetric.tendsto_euclideanCoefficients_of_scalar_jets x b h
  intro A hA
  let e := g.orthonormalBasis x
  have hquad : Tendsto (fun i => ∑ a, ∑ b, ∑ c, ∑ d,
      A a b * A c d * (Dseq i).curvatureTensor x (e a) (e b) (e c) (e d)) l
      (𝓝 (D.curvatureOperatorQuadratic x A)) := by
    unfold curvatureOperatorQuadratic
    apply tendsto_finsetSum
    intro a _
    apply tendsto_finsetSum
    intro b _
    apply tendsto_finsetSum
    intro c _
    apply tendsto_finsetSum
    intro d _
    exact tendsto_const_nhds.mul (tendsto_curvatureTensor_of_metric_jets Dseq D x
      (e a) (e b) (e c) (e d) hzero hone htwo)
  apply ge_of_tendsto hquad
  filter_upwards [hpos] with i hi
  exact (Dseq i).curvatureOperator_nonneg_in_frame x hi e A hA

end LeviCivitaData

namespace FlowCarrier



theorem nonnegativeCurvatureOperator_iff_of_coordinate_germ
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
    DE.NonnegativeCurvatureOperator p ↔
      DM.NonnegativeCurvatureOperator ((extChartAt (𝓡 n) q).symm p) := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let c := extChartAt (𝓡 n) q
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp
    (inter_mem (extChartAt_target_mem_nhds' hp) h)
  apply DE.nonnegativeCurvatureOperator_iff_of_local_isometry DM hVo
    (fun x hx => (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q
      (hV hx).1).contMDiffAt (extChartAt_target_mem_nhds' (hV hx).1)
        |>.contMDiffWithinAt) (x := p) (hx := hpV)
  intro x hx
  have hB : gE.euclideanCoefficients x = gM.pullbackCoefficients c.symm x :=
    bilinear_eq_of_basis (hV hx).2
  intro u v
  exact congrArg (fun B => B u v) hB

end FlowCarrier

namespace SmoothSpacetimeEmbedding



theorem nonnegativeCurvatureOperator_iff_of_coordinate_germ
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
    DE.NonnegativeCurvatureOperator p.2 ↔
      (G.flow.connection p.1).NonnegativeCurvatureOperator
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
  apply DE.nonnegativeCurvatureOperator_iff_of_local_isometry (G.flow.connection p.1) hVo
    (fun x hx => ((hf x (hV hx).1).comp x (hc x (hV hx).1)).contMDiffWithinAt)
    (x := p.2) (hx := hpV)
  intro x hx
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



theorem nonnegativeCurvatureOperator_of_eventually_at_embedding
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (t : ℝ) (ht : t ∈ Ioo T' T)
    (x : G.limitCarrier.carrier)
    (hpos : ∀ᶠ k : ℕ in atTop,
      let C := S.carrier (G.subsequence k)
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ((S.flow (G.subsequence k)).flow.connection t).NonnegativeCurvatureOperator
        ((G.embedding k).toFun (t, x)).2) :
    letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
      G.limitCarrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
    (G.limitFlow.flow.connection t).NonnegativeCurvatureOperator x := by
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
  have hposE : ∀ᶠ k in atTop, (gd k).2.NonnegativeCurvatureOperator p := by
    obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (isCompact_singleton (x := x))
    filter_upwards [hgd, hpos, eventually_ge_atTop j] with k hk hpk hjk
    apply ((G.embedding k).nonnegativeCurvatureOperator_iff_of_coordinate_germ
      (G.exhaustion_open k) x (t, p) ht
      ⟨hp, by rw [hcx]; exact G.exhaustion_monotone hjk (hj (mem_singleton x))⟩
      (gd k).1 (gd k).2 hk).2
    simpa only [hcx] using hpk
  have hlim := LeviCivitaData.nonnegativeCurvatureOperator_of_scalar_metric_jets
    (l := atTop) (fun k => (gd k).2) D p (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (by
      intro r _ a b
      simp only [OrthonormalBasis.coe_toBasis]
      erw [G.limitCarrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        x _ t p g hg r a b]
      apply (G.tendsto_coordinate_spatial_metricJet x r a b (t, p) ht hp).congr'
      filter_upwards [hgd] with k hk
      exact (G.limitCarrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        x _ t p (gd k).1 hk r a b).symm) hposE
  simpa only [hcx] using
    (G.limitCarrier.nonnegativeCurvatureOperator_iff_of_coordinate_germ
      (G.limitFlow.metricAt t) (G.limitFlow.flow.connection t) x t p hp g D hg).1 hlim



theorem nonnegativeCurvatureOperator_of_eventually
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (t : ℝ) (ht : t ∈ Ioo T' T)
    (hpos : ∀ᶠ k : ℕ in atTop,
      let C := S.carrier k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ x : C.carrier, ((S.flow k).flow.connection t).NonnegativeCurvatureOperator x) :
    letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
      G.limitCarrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
    ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.flow.connection t).NonnegativeCurvatureOperator x := by
  intro x
  apply G.nonnegativeCurvatureOperator_of_eventually_at_embedding t ht x
  filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hpos] with k hk
  exact hk _



theorem nonnegativeCurvatureOperator_of_eventually_on_balls
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (t : ℝ) (ht : t ∈ Ioo T' T)
    (hpos : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      let C := S.carrier k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ x ∈ (S.flow k).ballAt t A,
        ((S.flow k).flow.connection t).NonnegativeCurvatureOperator x) :
    letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
      G.limitCarrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
    ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.flow.connection t).NonnegativeCurvatureOperator x := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let : T3Space G.limitCarrier.carrier := G.limitCarrier.t3Space
  let : PreconnectedSpace G.limitCarrier.carrier :=
    ⟨G.limitCarrier.connected.isPreconnected⟩
  intro x
  let g := G.limitFlow.metricAt t
  let A := (g.edist G.limitFlow.base x).toReal + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hx : x ∈ G.limitFlow.ballAt t A := by
    change g.edist G.limitFlow.base x < ENNReal.ofReal A
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top G.limitFlow.base x)]
    exact ENNReal.ofReal_lt_ofReal_iff hA |>.mpr (by dsimp only [A]; linarith)
  apply G.nonnegativeCurvatureOperator_of_eventually_at_embedding t ht x
  filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually
    (hpos (2 * A) (by positivity)), G.eventually_mem_ballAt hT ht hx] with k hk hxk
  exact hk _ hxk

end PointedGeometricConvergence

namespace RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold



theorem nonnegativeCurvatureOperator_of_bufferedCylinderSequence
    {n : ℕ} (C : ℕ → FlowCarrier.{0} n) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow n (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (a δ : ℝ) (ha : a < 0)
    (hJ : ∀ k, Icc a 0 ⊆ interior (J k))
    (hoperator : ∀ k, ∀ t ∈ Icc a 0, ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (G : PointedGeometricConvergence (bufferedCylinderSequence C J F p a δ ha hJ)) :
    ∀ t ∈ Ioo (a + δ) δ, ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.flow.connection t).NonnegativeCurvatureOperator x := by
  intro t ht
  apply G.nonnegativeCurvatureOperator_of_eventually t ht
  apply Filter.Eventually.of_forall
  intro k
  change ∀ x : (C k).carrier, ((F k).connection (t - δ)).NonnegativeCurvatureOperator x
  intro x
  exact hoperator k (t - δ) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x

end RicciFlow
end PoincareConjecture
