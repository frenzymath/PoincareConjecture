import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.EuclideanJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.CoordinateBounds




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem abs_realization_bundled_jet_component_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (heq : h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s)
    (r : ℕ) (hr : r ≤ 2) (i j : Fin 3) (a : Fin r → Fin 3) :
    |iteratedFDeriv ℝ r h.euclideanCoefficients 0
        (fun k => roundCylinderEuclideanBasis (a k))
        (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
      iteratedFDeriv ℝ r roundCylinderEuclideanMetric.euclideanCoefficients 0
        (fun k => roundCylinderEuclideanBasis (a k))
        (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)| ≤
      (if r = 0 then 2 else if r = 1 then 3 else 6) * N.epsilon := by
  have hjet := N.abs_realization_scalar_jet_component_le q hs h heq r hr i j a
  have hreg (h' : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) :
      ContDiffAt ℝ r (fun x => h'.inner x (roundCylinderEuclideanBasis i)
        (roundCylinderEuclideanBasis j)) 0 :=
    (((h'.contDiffAt_euclideanCoefficients 0).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const).of_le (by norm_cast; exact le_top)
  change |iteratedFDeriv ℝ r ((fun x => h.inner x
        (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) -
      (fun x => roundCylinderEuclideanMetric.inner x
        (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j))) 0
      (fun k => roundCylinderEuclideanBasis (a k))| ≤ _ at hjet
  rw [iteratedFDeriv_sub_apply (hreg h) (hreg roundCylinderEuclideanMetric)] at hjet
  simp only [sub_apply, LeviCivitaData.iteratedFDeriv_metric_inner] at hjet
  exact hjet

theorem abs_realization_first_jet_component_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (heq : h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s)
    (hzero : fderiv ℝ roundCylinderEuclideanMetric.euclideanCoefficients 0 = 0)
    (i j k : Fin 3) :
    |fderiv ℝ h.euclideanCoefficients 0 (roundCylinderEuclideanBasis i)
      (roundCylinderEuclideanBasis j) (roundCylinderEuclideanBasis k)| ≤ 3 * N.epsilon := by
  have hjet := N.abs_realization_bundled_jet_component_le q hs h heq 1 (by decide) j k ![i]
  simpa only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, hzero, zero_apply, sub_zero,
    show ¬(1 : ℕ) = 0 by decide, ite_false, ite_true] using hjet

theorem abs_realization_second_jet_component_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (heq : h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s)
    (i j k l : Fin 3) :
    |fderiv ℝ (fderiv ℝ h.euclideanCoefficients) 0
        (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)
        (roundCylinderEuclideanBasis k) (roundCylinderEuclideanBasis l) -
      fderiv ℝ (fderiv ℝ roundCylinderEuclideanMetric.euclideanCoefficients) 0
        (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)
        (roundCylinderEuclideanBasis k) (roundCylinderEuclideanBasis l)| ≤ 6 * N.epsilon := by
  have hjet := N.abs_realization_bundled_jet_component_le q hs h heq 2 (by decide) k l ![i,j]
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    show ¬(2 : ℕ) = 0 by decide, show ¬(2 : ℕ) = 1 by decide, ite_false] using hjet

end PoincareConjecture.EpsilonNeck
