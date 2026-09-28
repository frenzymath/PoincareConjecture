import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.RicciComparison.Contraction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.RealizationScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Ambient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem abs_realization_ricci_sub_le
    (N : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 200) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (D : LeviCivitaData h)
    (heq : h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s)
    (a b : Fin 3) :
    |D.ricci 0 (roundCylinderEuclideanBasis a) (roundCylinderEuclideanBasis b) -
      NeckCurvature.cylinderRicciDiagonal a b| ≤ NeckCurvature.cylinderRicciError a b := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
    h.inner 0 (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)
  let B := A⁻¹
  have hdet : A.det ≠ 0 := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : EuclideanSpace ℝ (Fin 3) → Type _) := ⟨h.toRiemannianMetric⟩
    change (Matrix.gram ℝ (show Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3)
      (0 : EuclideanSpace ℝ (Fin 3))) from roundCylinderEuclideanBasis)).det ≠ 0
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr roundCylinderEuclideanBasis.linearIndependent
  have hAB : A * B = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet)
  have hmetric (i j : Fin 3) : |A i j - NeckCurvature.cylinderGramDiagonal i j| ≤ 1 / 100 := by
    have hjet := N.abs_realization_bundled_jet_component_le q hs h heq 0 (by decide)
      i j (fun k => k.elim0)
    simp only [iteratedFDeriv_zero_apply, ite_true] at hjet
    have hm := congrFun (congrFun roundCylinderEuclideanMetric_gram_zero i) j
    change roundCylinderEuclideanMetric.inner 0 (roundCylinderEuclideanBasis i)
      (roundCylinderEuclideanBasis j) = NeckCurvature.cylinderGramDiagonal i j at hm
    change |h.inner 0 (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
      roundCylinderEuclideanMetric.inner 0 (roundCylinderEuclideanBasis i)
        (roundCylinderEuclideanBasis j)| ≤ _ at hjet
    rw [hm] at hjet
    exact hjet.trans (by linarith)
  have hinverse : (∑ i, ∑ j, |h.inverseCoefficients 0 i j|) ≤ 41 / 20 := by
    rw [h.sum_abs_inverseCoefficients_eq_cylinder_inverse_gram]
    exact NeckCurvature.inverse_sum_abs_le_forty_one_twentieths A B hAB hmetric
  have hbasis (i : Fin 3) : roundCylinderEuclideanBasis ((finRotate 3).symm i) =
      EuclideanSpace.basisFun (Fin 3) ℝ i := by
    simp only [roundCylinderEuclideanBasis, Module.Basis.reindex_apply,
      OrthonormalBasis.coe_toBasis, Equiv.symm_symm, Equiv.apply_symm_apply]
  have hfirst (i j k : Fin 3) : |fderiv ℝ h.euclideanCoefficients 0
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
      (EuclideanSpace.basisFun (Fin 3) ℝ k)| ≤ 3 / 200 := by
    rw [← hbasis i, ← hbasis j, ← hbasis k]
    exact (N.abs_realization_first_jet_component_le q hs h heq
      roundCylinderEuclideanMetric_first_jet_zero _ _ _).trans (by linarith)
  have hsecond (i j k l : Fin 3) :
      |fderiv ℝ (fderiv ℝ h.euclideanCoefficients) 0
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
          (EuclideanSpace.basisFun (Fin 3) ℝ k) (EuclideanSpace.basisFun (Fin 3) ℝ l) -
        fderiv ℝ (fderiv ℝ roundCylinderEuclideanMetric.euclideanCoefficients) 0
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
          (EuclideanSpace.basisFun (Fin 3) ℝ k) (EuclideanSpace.basisFun (Fin 3) ℝ l)| ≤ 3 / 100 := by
    rw [← hbasis i, ← hbasis j, ← hbasis k, ← hbasis l]
    exact (N.abs_realization_second_jet_component_le q hs h heq _ _ _ _).trans (by linarith)
  let D₀ := roundCylinderEuclideanMetric.euclideanLeviCivitaData
  have hcurv (i j k l : Fin 3) :
      |D.curvatureTensor 0 (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)
          (roundCylinderEuclideanBasis k) (roundCylinderEuclideanBasis l) -
        NeckCurvature.cylinderCurvatureComponent i j k l| ≤ 63 / 1000 := by
    rw [← roundCylinderEuclideanMetric_curvature_zero_basis D₀]
    have hb (a : Fin 3) : roundCylinderEuclideanBasis a =
        EuclideanSpace.basisFun (Fin 3) ℝ ((finRotate 3) a) := by
      simp only [roundCylinderEuclideanBasis, Module.Basis.reindex_apply,
        OrthonormalBasis.coe_toBasis, Equiv.symm_symm]
    simp only [hb]
    exact (D₀.abs_curvatureTensor_sub_le_of_centered_jets D 0 (by norm_num)
      roundCylinderEuclideanMetric_first_jet_zero hfirst hsecond hinverse _ _ _ _).trans
        (by norm_num)
  rw [D.ricci_eq_coordinate_gram 0 roundCylinderEuclideanBasis]
  apply NeckCurvature.abs_ricci_contraction_sub_le A B hAB hmetric _ ?_ ?_ hcurv a b
  · intro i k l
    have ht := D.curvatureTensor_swap_first 0 (roundCylinderEuclideanBasis i)
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis k)
      (roundCylinderEuclideanBasis l)
    linarith
  · intro i j k
    have ht := D.curvatureTensor_swap_last 0 (roundCylinderEuclideanBasis i)
      (roundCylinderEuclideanBasis j) (roundCylinderEuclideanBasis k)
      (roundCylinderEuclideanBasis k)
    linarith

theorem abs_ambient_ricci_coefficient_sub_le
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hε : N.epsilon ≤ 1 / 200)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (a b : Fin 3) :
    |D.ricci (N.centeredEuclideanParametrization q s 0)
        (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0
          (roundCylinderEuclideanBasis a))
        (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0
          (roundCylinderEuclideanBasis b)) -
      NeckCurvature.cylinderRicciDiagonal a b| ≤ NeckCurvature.cylinderRicciError a b := by
  obtain ⟨h, Dh, heq⟩ := N.exists_normalizedEuclideanCoefficients_realization q hs
  rw [← (N.normalized_realization_curvature D q hs Dh heq).2]
  exact N.abs_realization_ricci_sub_le hε q hs h Dh heq a b

end PoincareConjecture.EpsilonNeck
