import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence.SpatialJets

set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

namespace RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

set_option backward.isDefEq.respectTransparency false in
private theorem exists_local_pullback_realization
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (f : EuclideanSpace ℝ (Fin n) → M)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ U)
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hi : ∀ x ∈ U, Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    ∃ (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_D : LeviCivitaData g') (V : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
        ∀ x ∈ V, g'.euclideanCoefficients x = g.pullbackCoefficients f x := by
  apply exists_local_realization hU hp (g.pullbackCoefficients f)
  · intro x hx
    exact (g.contDiffAt_pullbackCoefficients (hf x hx)).contDiffWithinAt
  · intro x hx v w
    exact g.symm (f x) _ _
  · intro x hx v hv
    apply g.pos (f x)
    intro hzero
    apply hv
    apply hi x hx
    rw [map_zero]
    convert! hzero using 1

end RiemannianMetric

namespace FlowCarrier

theorem iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
    {n : ℕ} (C : FlowCarrier n) (q : C.carrier)
    (B : ∀ _t : ℝ, ∀ x : C.carrier, C.tangent x → C.tangent x → ℝ)
    (t : ℝ) (p : EuclideanSpace ℝ (Fin n))
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (h : ∀ᶠ x in 𝓝 p, ∀ a b : Fin n,
      g.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b) = C.coordinateCoefficient q B a b (t, x))
    (r : ℕ) (a b : Fin n) :
    iteratedFDeriv ℝ r (fun x => g.inner x (EuclideanSpace.basisFun (Fin n) ℝ a)
      (EuclideanSpace.basisFun (Fin n) ℝ b)) p =
    iteratedFDeriv ℝ r (fun x => C.coordinateCoefficient q B a b (t, x)) p := by
  have heq : (fun x => g.inner x (EuclideanSpace.basisFun (Fin n) ℝ a)
      (EuclideanSpace.basisFun (Fin n) ℝ b)) =ᶠ[𝓝 p]
      (fun x => C.coordinateCoefficient q B a b (t, x)) := by
    filter_upwards [h] with x hx
    exact hx a b
  exact (heq.iteratedFDeriv ℝ r).self_of_nhds

theorem exists_local_coordinate_realization {n : ℕ} (C : FlowCarrier n)
    (g : C.metric) (q : C.carrier) (t : ℝ) (p : EuclideanSpace ℝ (Fin n))
    (hp :
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      p ∈ (extChartAt (𝓡 n) q).target) :
    ∃ (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_D : LeviCivitaData g') (V : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen V ∧ p ∈ V ∧
        (letI : TopologicalSpace C.carrier := C.topologicalSpace
         letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
         V ⊆ (extChartAt (𝓡 n) q).target) ∧
        ∀ x ∈ V, ∀ a b : Fin n,
          g'.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ b) =
          C.coordinateCoefficient q (fun _ y v w => C.metricInner g y v w) a b (t, x) := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let c := extChartAt (𝓡 n) q
  obtain ⟨g', D, V, hVo, hpV, hV, heq⟩ := g.exists_local_pullback_realization c.symm
    (isOpen_extChartAt_target q) hp
    (fun x hx => (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hx).contMDiffAt
      (extChartAt_target_mem_nhds' hx))
    (fun x hx => by
      have h : (mfderiv (𝓡 n) (𝓡 n) c.symm x).IsInvertible := by
        simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
          isInvertible_mfderivWithin_extChartAt_symm hx
      exact h.injective)
  refine ⟨g', D, V, hVo, hpV, hV, ?_⟩
  intro x hx a b
  rw [heq x hx]
  rfl

end FlowCarrier

namespace SmoothSpacetimeEmbedding

theorem exists_local_coordinate_realization
    {n : ℕ} {T' T : ℝ} {C D : FlowCarrier n}
    {F : BasedFlow n T' T C} {G : BasedFlow n T' T D} {U : Set C.carrier}
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen C.carrier C.topologicalSpace U)
    (q : C.carrier) (p : ℝ × EuclideanSpace ℝ (Fin n))
    (ht : p.1 ∈ Ioo T' T)
    (hp :
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      p.2 ∈ (extChartAt (𝓡 n) q).target ∧ (extChartAt (𝓡 n) q).symm p.2 ∈ U) :
    ∃ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_D : LeviCivitaData g) (V : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen V ∧ p.2 ∈ V ∧
        (letI : TopologicalSpace C.carrier := C.topologicalSpace
         letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
         V ⊆ (extChartAt (𝓡 n) q).target ∩ (extChartAt (𝓡 n) q).symm ⁻¹' U) ∧
        ∀ x ∈ V, ∀ a b : Fin n,
          g.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ b) =
          C.coordinateCoefficient q (pullbackInnerValue F G e) a b (p.1, x) := by
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
  obtain ⟨g, Dg, V, hVo, hpV, hV, heq⟩ :=
    (G.metricAt p.1).exists_local_pullback_realization (f ∘ c.symm) hW hp
      (fun x hx => (hf x hx).comp x (hc x hx))
      (fun x hx => by
        rw [hderiv x hx]
        have hi : (mfderiv (𝓡 n) (𝓡 n) c.symm x).IsInvertible := by
          simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
            isInvertible_mfderivWithin_extChartAt_symm hx.1
        exact (e.spatialMap_mfderiv_injective hU ht hx.2).comp hi.injective)
  refine ⟨g, Dg, V, hVo, hpV, hV, ?_⟩
  intro x hx a b
  rw [heq x hx]
  change (G.metricAt p.1).inner (f (c.symm x))
    (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ a))
    (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ b)) = _
  rw [hderiv x (hV hx)]
  rfl

end SmoothSpacetimeEmbedding

namespace PointedGeometricConvergence

theorem eventually_exists_local_coordinate_realization
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S)
    (q : G.limitCarrier.carrier) (p : ℝ × EuclideanSpace ℝ (Fin n))
    (ht : p.1 ∈ Ioo T' T)
    (hp :
      letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
        G.limitCarrier.chartedSpace
      p.2 ∈ (extChartAt (𝓡 n) q).target) :
    ∀ᶠ k : ℕ in atTop,
      ∃ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (_D : LeviCivitaData g) (V : Set (EuclideanSpace ℝ (Fin n))),
        IsOpen V ∧ p.2 ∈ V ∧
          ∀ x ∈ V, ∀ a b : Fin n,
            g.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ a)
              (EuclideanSpace.basisFun (Fin n) ℝ b) =
            G.limitCarrier.coordinateCoefficient q
              (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k))
              a b (p.1, x) := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    (isCompact_singleton (x := (extChartAt (𝓡 n) q).symm p.2))
  filter_upwards [eventually_ge_atTop j] with k hk
  obtain ⟨g, D, V, hVo, hpV, _, heq⟩ :=
    (G.embedding k).exists_local_coordinate_realization (G.exhaustion_open k)
      q p ht ⟨hp, G.exhaustion_monotone hk (hj (mem_singleton _))⟩
  exact ⟨g, D, V, hVo, hpV, heq⟩

end PointedGeometricConvergence

end PoincareConjecture
