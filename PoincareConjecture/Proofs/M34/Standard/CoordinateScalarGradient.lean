import PoincareConjecture.Proofs.M34.Standard.CoordinateGermHomothety
import PoincareConjecture.Proofs.M34.Standard.ScalarGradientHomothety











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.FlowCarrier



theorem scalarGradientNorm_eq_of_coordinate_germ
    (C : FlowCarrier 3) (gM : C.metric)
    (DM : @LeviCivitaData 3 C.carrier C.topologicalSpace C.chartedSpace C.isManifold gM)
    (q : C.carrier) (t : ℝ) (p : EuclideanSpace ℝ (Fin 3))
    (hp :
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
      p ∈ (extChartAt (𝓡 3) q).target)
    (gE : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (DE : LeviCivitaData gE)
    (h : ∀ᶠ x in 𝓝 p, ∀ a b : Fin 3,
      gE.euclideanCoefficients x (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      C.coordinateCoefficient q (fun _ y v w => C.metricInner gM y v w) a b (t, x)) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
    scalarGradientNorm gE DE p = scalarGradientNorm gM DM ((extChartAt (𝓡 3) q).symm p) := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  let : T2Space C.carrier := C.t2Space
  obtain ⟨V, hVo, hpV, hf, hm⟩ := C.exists_local_isometry_of_coordinate_germ
    gM q t p hp gE h
  simpa only [one_mul, Real.one_rpow, div_one] using
    scalarGradientNorm_eq_of_local_homothety DE DM (Q := 1) (by norm_num) hVo hf
      (fun x hx v w => (hm x hx v w).trans (one_mul _).symm) hpV

end PoincareConjecture.FlowCarrier

namespace PoincareConjecture.GeneralizedFlowCylinder




theorem scalarGradientNorm_eq_of_coordinate_germ
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {F : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} {K : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder F L.sliceCarrier origin scale K U)
    (hU : IsOpen U) (q : L.sliceCarrier.carrier)
    {s : ℝ} (hs : s ∈ K) (p : EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ (extChartAt (𝓡 3) q).target ∧ (extChartAt (𝓡 3) q).symm p ∈ U)
    (gE : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (DE : LeviCivitaData gE)
    (h : ∀ᶠ x in 𝓝 p, ∀ a b : Fin 3,
      gE.euclideanCoefficients x (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) = blowupPullbackCoefficient e q a b (s, x)) :
    let z := e.pointMap s hs ((extChartAt (𝓡 3) q).symm p)
    scalarGradientNorm gE DE p =
      scalarGradientNorm (F.metric z.1) (F.connection z.1) z.2 / scale ^ (3 / 2 : ℝ) := by
  obtain ⟨V, hVo, hpV, hf, hm⟩ := e.exists_local_homothety_of_coordinate_germ
    hU q hs p hp gE h
  exact scalarGradientNorm_eq_of_local_homothety DE (F.connection (origin + s / scale))
    e.scale_pos hVo hf hm hpV

end PoincareConjecture.GeneralizedFlowCylinder
