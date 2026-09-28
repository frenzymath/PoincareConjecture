import PoincareConjecture.Proofs.M25.AppA_1_Necks.RealizedCurvature
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.BilinearJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.PartialTraceEvolution












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck




theorem exists_realized_ricci_quadratic_control {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (D : LeviCivitaData h),
      h.euclideanCoefficients =ᶠ[𝓝 0] N.m25_normalizedEuclideanCoefficients q s →
      ∀ v : EuclideanSpace ℝ (Fin 3),
      |D.ricci 0 v v - roundCylinderEuclideanModelConnection.ricci 0 v v| ≤ α * ‖v‖ ^ 2 := by
  obtain ⟨epsilon0, hpos, hcap, hcontrol⟩ :=
    exists_realized_scalar_ricci_control.{u} (show 0 < α / 9 by positivity)
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N hepsilon q s hs h D heq v
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).reindex (finRotate 3).symm
  have hb (i : Fin 3) : b i = m25_roundCylinderEuclideanBasis i := by
    have hbb : b.toBasis = m25_roundCylinderEuclideanBasis := by
      simp only [b, OrthonormalBasis.reindex_toBasis, m25_roundCylinderEuclideanBasis]
    exact congrArg (fun c : Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) => c i) hbb
  let A : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
    RicciFlow.Splitting.ricciBilinear D 0 -
      RicciFlow.Splitting.ricciBilinear roundCylinderEuclideanModelConnection 0
  let B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    (LinearMap.toContinuousLinearMap.toLinearMap.comp A).toContinuousLinearMap
  have hB (a c : EuclideanSpace ℝ (Fin 3)) :
      B a c = D.ricci 0 a c - roundCylinderEuclideanModelConnection.ricci 0 a c := by
    change (RicciFlow.Splitting.ricciBilinear D 0 -
      RicciFlow.Splitting.ricciBilinear roundCylinderEuclideanModelConnection 0) a c = _
    simp only [LinearMap.sub_apply, RicciFlow.Splitting.ricciBilinear_apply]
  have hcomp (i j : Fin 3) :
      ‖iteratedFDeriv ℝ 0 (fun _ : ℝ => B (b i) (b j)) 0‖ ≤ α / 9 := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, hB, hb, hb]
    exact ((hcontrol N hepsilon q hs h D heq).2 i j).le
  have hnorm : ‖B‖ ≤ α := by
    have hbound := SpacetimeBounds.norm_iteratedFDeriv_bilinear_le_of_components
      b (F := fun _ : ℝ => B) (x := 0) contDiffAt_const 0 hcomp
    rw [norm_iteratedFDeriv_zero] at hbound
    norm_num at hbound
    linarith
  calc
    _ = ‖B v v‖ := by rw [Real.norm_eq_abs, hB]
    _ ≤ ‖B‖ * ‖v‖ ^ 2 := by simpa only [pow_two, mul_assoc] using B.le_opNorm₂ v v
    _ ≤ α * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hnorm (sq_nonneg _)

end PoincareConjecture.EpsilonNeck
