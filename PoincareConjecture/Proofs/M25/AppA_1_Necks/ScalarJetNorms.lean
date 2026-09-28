import PoincareConjecture.Proofs.M25.AppA_1_Necks.SecondJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Coefficients










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.EpsilonNeck



theorem m25_exists_normalized_pullback_scalar_twoJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ},
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → ∀ r : ℕ, r ≤ 2 → ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ r (fun p =>
        roundCylinderTensorCoefficient N.normalized_pullback
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
        roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j)
        (0, s)‖ ≤ C * N.epsilon := by
  obtain ⟨C₂, hC₂, hsecond⟩ :=
    m25_exists_normalized_pullback_second_derivative_center_bound.{u}
  refine ⟨4 + 24 + 9 * C₂, by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ g N q s hs r hr i j
  have hε := N.epsilon_pos
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let E := fun p => roundCylinderTensorCoefficient N.normalized_pullback c p i j -
    roundCylinderGram 0 c p i j
  have hN : ContDiffAt ℝ ∞ (fun p =>
      roundCylinderTensorCoefficient N.normalized_pullback c p i j) (0, s) := by
    apply (N.normalized_pullback_close.1 q i j).contDiffAt
    rw [roundCylinder_sphereChart_target]
    exact (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hs⟩
  have hE : ContDiffAt ℝ ∞ E (0, s) :=
    hN.sub (contDiff_roundCylinderGram 0 q i j).contDiffAt
  have hzero : ‖iteratedFDeriv ℝ 0 E (0, s)‖ ≤ 4 * N.epsilon := by
    rw [norm_iteratedFDeriv_zero]
    have h := N.m25_abs_normalized_pullback_covariant_component_center_le q hs
      (k := 0) (Nat.zero_le _) ![i, j]
    norm_num only [Nat.add_zero, show (2 : ℝ) ^ 2 = 4 by norm_num] at h
    exact h
  have hfirst_component (k : Fin 3) :
      ‖fderiv ℝ E (0, s) (roundCylinderCoordinateBasis k)‖ ≤ 8 * N.epsilon := by
    dsimp only [E]
    rw [fderiv_fun_sub (hN.differentiableAt (by simp))
      ((contDiff_roundCylinderGram 0 q i j).differentiable (by simp) (0, s)),
      fderiv_roundCylinderGram_center, sub_zero]
    exact N.abs_normalized_pullback_coefficient_derivative_center_le q hs k i j
  have hone : ‖iteratedFDeriv ℝ 1 E (0, s)‖ ≤ 24 * N.epsilon := by
    rw [norm_iteratedFDeriv_one]
    have h := norm_le_of_cylinder_basis_bound (fderiv ℝ E (0, s))
      (show 0 ≤ 8 * N.epsilon by positivity) hfirst_component
    nlinarith
  have hEd : DifferentiableAt ℝ (fderiv ℝ E) (0, s) :=
    (hE.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hsecond_component (k l : Fin 3) :
      ‖fderiv ℝ (fderiv ℝ E) (0, s) (roundCylinderCoordinateBasis k)
        (roundCylinderCoordinateBasis l)‖ ≤ C₂ * N.epsilon := by
    have h := hsecond N q hs ![k, l, i, j]
    change |fderiv ℝ (fun p => fderiv ℝ E p
      (roundCylinderCoordinateBasis l)) (0, s) (roundCylinderCoordinateBasis k)| ≤
        C₂ * N.epsilon at h
    rw [fderiv_clm_apply hEd (differentiableAt_const _)] at h
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply, Real.norm_eq_abs] using h
  have hsecond_slot (k : Fin 3) :
      ‖fderiv ℝ (fderiv ℝ E) (0, s) (roundCylinderCoordinateBasis k)‖ ≤
        3 * (C₂ * N.epsilon) :=
    norm_le_of_cylinder_basis_bound _ (by positivity) (hsecond_component k)
  have htwo : ‖iteratedFDeriv ℝ 2 E (0, s)‖ ≤ 9 * C₂ * N.epsilon := by
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    have h := norm_le_of_cylinder_basis_bound
      (fderiv ℝ (fderiv ℝ E) (0, s))
      (show 0 ≤ 3 * (C₂ * N.epsilon) by positivity) hsecond_slot
    nlinarith
  change ‖iteratedFDeriv ℝ r E (0, s)‖ ≤ _
  interval_cases r <;> nlinarith

end PoincareConjecture.EpsilonNeck
