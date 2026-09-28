import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Centered









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Topology Manifold ContDiff Bundle BigOperators InnerProductSpace

namespace PoincareConjecture

local instance : Bundle.RiemannianBundle
    (RoundCylinderTangent : RoundCylinderSpace → Type _) :=
  ⟨roundCylinderProductMetric.toRiemannianMetric⟩


theorem roundCylinderClose_iterated_normSquared_lt
    {ε : ℝ} {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose ε 0 B)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹)
    {k : ℕ} (hk : k ≤ ⌊ε⁻¹⌋₊) :
    roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
      (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        B k (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)) < ε ^ 2 := by
  obtain ⟨_, bound, hbound, hjet⟩ := hB
  apply lt_of_le_of_lt ?_ ((hjet z hz).trans_lt hbound)
  dsimp only [roundCylinderJetErrorSquared]
  apply Finset.single_le_sum (f := fun j =>
    roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
      (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        B j (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)))
  · intro j _
    exact roundCylinderTensorNormSquared_nonneg z.1 _ _
  · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)



theorem roundCylinderClose_first_derivative_apply_le
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose ε 0 B)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-ε⁻¹) ε⁻¹)
    (v : Fin 3 → RoundCylinderTangent
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q), s)) :
    |componentMultilinearMap
      (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        B 1 (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s))
      (roundCylinderChartBasis q (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s)) v| ≤
      ε * ∏ r, ‖v r‖ := by
  let b := roundCylinderChartBasis q (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s)
  let : FiniteDimensional ℝ (RoundCylinderTangent
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q), s)) := Module.Finite.of_basis b
  have hGram : Matrix.of (fun i j => inner ℝ (b i) (b j)) =
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) := by
    ext i j
    simp only [Matrix.of_apply, b]
    rw [roundCylinderChartBasis_apply, roundCylinderChartBasis_apply]
    change roundCylinderProductMetric.inner _ _ _ = _
    exact roundCylinderChartFrame_gram q _ i j
  apply abs_multilinear_apply_le_of_inverse_gram_contraction_le
    (componentMultilinearMap
      (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        B 1 (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s)) b) b hε.le
  have hk : 1 ≤ ⌊ε⁻¹⌋₊ := (Nat.one_le_floor_iff _).mpr ((one_le_inv₀ hε).mpr hεone)
  have hnorm := roundCylinderClose_iterated_normSquared_lt hB (z := (q, s)) hs hk
  rw [hGram]
  simpa only [componentMultilinearMap_basis, roundCylinderTensorNormSquared,
    Matrix.of_apply, b, roundCylinderChartBasis_apply] using hnorm.le



theorem roundCylinderClose_first_jet_center
    {ε : ℝ} {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose ε 0 B)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-ε⁻¹) ε⁻¹) (a : Fin 3 → Fin 3) :
    roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      B 1 (0, s) a =
      fderiv ℝ (fun p => roundCylinderTensorCoefficient B
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (a 1) (a 2)) (0, s)
        (roundCylinderCoordinateBasis (a 0)) := by
  have hd : DifferentiableAt ℝ (fun p => roundCylinderTensorCoefficient B
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (a 1) (a 2)) (0, s) := by
    apply ((hB.1 q (a 1) (a 2)).contDiffAt ?_).differentiableAt (by simp)
    rw [roundCylinder_sphereChart_target]
    exact (isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (0, s) ∈ (univ : Set (EuclideanSpace ℝ (Fin 2))) ×ˢ Ioo (-ε⁻¹) ε⁻¹ from
        ⟨mem_univ _, hs⟩)
  simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative,
    roundCylinderChristoffel_center, zero_mul, Finset.sum_const_zero, sub_zero]
  change (fderiv ℝ ((fun p => roundCylinderTensorCoefficient B
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (a 1) (a 2)) -
    (fun p => roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p
      (a 1) (a 2))) (0, s)) (roundCylinderCoordinateBasis (a 0)) = _
  rw [fderiv_sub hd ((contDiff_roundCylinderGram 0 q (a 1) (a 2)).differentiable
    (by simp) (0, s)), fderiv_roundCylinderGram_center]
  simp



theorem roundCylinderClose_coefficient_derivative_center_le
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose ε 0 B)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-ε⁻¹) ε⁻¹) (i j k : Fin 3) :
    |fderiv ℝ (fun p => roundCylinderTensorCoefficient B
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p j k) (0, s)
      (roundCylinderCoordinateBasis i)| ≤ 8 * ε := by
  let a : Fin 3 → Fin 3 := ![i, j, k]
  have h := roundCylinderClose_first_derivative_apply_le hε hεone hB q hs
    (fun r => roundCylinderChartBasis q
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) (a r))
  simp +instances only [componentMultilinearMap_basis, sphere_chart_center] at h
  rw [roundCylinderClose_first_jet_center hB q hs] at h
  change |fderiv ℝ (fun p => roundCylinderTensorCoefficient B
    (chartAt (EuclideanSpace ℝ (Fin 2)) q) p j k) (0, s)
    (roundCylinderCoordinateBasis i)| ≤ _ at h
  have hprod : (∏ r : Fin 3, ‖roundCylinderChartBasis q
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) (a r)‖) ≤ 8 := by
    calc
      _ ≤ ∏ _r : Fin 3, (2 : ℝ) := Finset.prod_le_prod
        (fun r _ => norm_nonneg _)
        (fun r _ => EpsilonNeck.norm_roundCylinderChartBasis_center_le_two q s (a r))
      _ = 8 := by norm_num
  exact h.trans (by nlinarith)

end PoincareConjecture
