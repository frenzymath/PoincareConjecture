import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SpacetimeEmbedding
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.SmoothSpacetimeEmbedding

variable {n : ℕ} {T' T : ℝ} {C D : FlowCarrier n}
    (F : BasedFlow n T' T C) (G : BasedFlow n T' T D)
    {U : Set C.carrier}
    (hU : @IsOpen C.carrier C.topologicalSpace U) (f : C.carrier → D.carrier)
    (hemb : letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : TopologicalSpace D.carrier := D.topologicalSpace
      Topology.IsOpenEmbedding (fun x : U => f x))
    (hf : letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : TopologicalSpace D.carrier := D.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
      IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ f U)
    (I : Set ℝ) (q : C.carrier) (a b : Fin n)

theorem coordinateCoefficient_of_spatial
    (t : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hx : letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      x ∈ (extChartAt (𝓡 n) q).target ∧ (extChartAt (𝓡 n) q).symm x ∈ U) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
    C.coordinateCoefficient q (pullbackInnerValue F G (of_spatial F G hU f hemb hf I))
      a b (t, x) =
        (G.flow.metric t).pullbackCoefficients (f ∘ (extChartAt (𝓡 n) q).symm) x
          (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b) := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : TopologicalSpace D.carrier := D.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  let : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  let c := extChartAt (𝓡 n) q
  have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hx.1).contMDiffAt
    (extChartAt_target_mem_nhds' hx.1)
  have hd : mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x =
      (mfderiv (𝓡 n) (𝓡 n) f (c.symm x)).comp
        (mfderiv (𝓡 n) (𝓡 n) c.symm x) :=
    mfderiv_comp x ((hf ⟨c.symm x, hx.2⟩).contMDiffAt.mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp))
  change (G.flow.metric t).inner (f (c.symm x))
      (mfderiv (𝓡 n) (𝓡 n) f (c.symm x)
        (mfderiv (𝓡 n) (𝓡 n) c.symm x (EuclideanSpace.basisFun (Fin n) ℝ a)))
      (mfderiv (𝓡 n) (𝓡 n) f (c.symm x)
        (mfderiv (𝓡 n) (𝓡 n) c.symm x (EuclideanSpace.basisFun (Fin n) ℝ b))) =
    (G.flow.metric t).inner (f (c.symm x))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ a))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ b))
  erw [hd]
  rfl

theorem coordinateCoefficient_of_spatial_eqOn (J : Set ℝ) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
    EqOn
      (C.coordinateCoefficient q (pullbackInnerValue F G (of_spatial F G hU f hemb hf I)) a b)
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (G.flow.metric z.1).pullbackCoefficients (f ∘ (extChartAt (𝓡 n) q).symm) z.2
          (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b))
      {z | z.1 ∈ J ∧ z.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm z.2 ∈ U} := by
  intro z hz
  exact coordinateCoefficient_of_spatial F G hU f hemb hf I q a b z.1 z.2 hz.2

theorem iteratedFDeriv_coordinateCoefficient_of_spatial
    (r : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin n))
    (hp : letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      p.2 ∈ (extChartAt (𝓡 n) q).target ∧ (extChartAt (𝓡 n) q).symm p.2 ∈ U) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
    iteratedFDeriv ℝ r
      (C.coordinateCoefficient q (pullbackInnerValue F G (of_spatial F G hU f hemb hf I)) a b) p =
    iteratedFDeriv ℝ r
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (G.flow.metric z.1).pullbackCoefficients (f ∘ (extChartAt (𝓡 n) q).symm) z.2
          (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b)) p := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : TopologicalSpace D.carrier := D.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  let : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hp.1).contMDiffAt
    (extChartAt_target_mem_nhds' hp.1)
  have heq :
      (C.coordinateCoefficient q (pullbackInnerValue F G (of_spatial F G hU f hemb hf I)) a b)
        =ᶠ[𝓝 p]
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (G.flow.metric z.1).pullbackCoefficients (f ∘ (extChartAt (𝓡 n) q).symm) z.2
          (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b)) := by
    filter_upwards
      [continuousAt_snd.preimage_mem_nhds (extChartAt_target_mem_nhds' hp.1),
        (hc.continuousAt.comp continuousAt_snd).preimage_mem_nhds (hU.mem_nhds hp.2)]
      with z hz hUz
    exact coordinateCoefficient_of_spatial F G hU f hemb hf I q a b z.1 z.2 ⟨hz, hUz⟩
  exact (heq.iteratedFDeriv ℝ r).self_of_nhds

end PoincareConjecture.SmoothSpacetimeEmbedding
