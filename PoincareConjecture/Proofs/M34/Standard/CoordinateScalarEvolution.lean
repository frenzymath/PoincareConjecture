import PoincareConjecture.Proofs.M34.Standard.CoordinateGermHomothety
import PoincareConjecture.Proofs.M34.Standard.ScalarEvolutionHomothety










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.FlowCarrier



theorem scalarEvolution_eq_of_coordinate_germ
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
    DE.laplacian DE.scalarCurvature p + 2 * DE.ricciNormSq p =
      DM.laplacian DM.scalarCurvature ((extChartAt (𝓡 n) q).symm p) +
        2 * DM.ricciNormSq ((extChartAt (𝓡 n) q).symm p) := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : T2Space C.carrier := C.t2Space
  obtain ⟨V, hVo, hpV, hf, hm⟩ := C.exists_local_isometry_of_coordinate_germ
    gM q t p hp gE h
  simpa only [one_mul, one_pow, div_one] using
    DE.scalarEvolutionNumerator_eq_of_local_homothety DM (Q := 1) (by norm_num) hVo hf
      (fun x hx v w => (hm x hx v w).trans (one_mul _).symm) hpV

end PoincareConjecture.FlowCarrier

namespace PoincareConjecture.GeneralizedFlowCylinder




theorem scalarEvolution_eq_of_coordinate_germ
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
    DE.laplacian DE.scalarCurvature p + 2 * DE.ricciNormSq p =
      ((F.connection z.1).laplacian (F.connection z.1).scalarCurvature z.2 +
        2 * (F.connection z.1).ricciNormSq z.2) / scale ^ 2 := by
  obtain ⟨V, hVo, hpV, hf, hm⟩ := e.exists_local_homothety_of_coordinate_germ
    hU q hs p hp gE h
  exact DE.scalarEvolutionNumerator_eq_of_local_homothety
    (F.connection (origin + s / scale)) e.scale_pos hVo hf hm hpV

end PoincareConjecture.GeneralizedFlowCylinder
