import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderRicciReadout
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderModelRicci
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckLengthComparison

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M28.tube

open PoincareConjecture.SpacetimeBounds PoincareConjecture.Proofs.M28.NeckLengthComparison

private abbrev CE := EuclideanSpace ℝ (Fin 3)
private abbrev SE := EuclideanSpace ℝ (Fin 2)
private abbrev cb := EuclideanSpace.basisFun (Fin 3) ℝ
private abbrev CI := (𝓡 2).prod 𝓘(ℝ, ℝ)

private theorem exists_cylinder_model_ricci_coefficient_modulus
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ J : MetricTwoJet 3,
      dist J cylinderModelTwoJet < eta → ∀ i j : Fin 3,
        |jetRicci J (cb i) (cb j) -
          inner ℝ (cylinderSphereProjection (cb i))
            (cylinderSphereProjection (cb j))| < delta := by
  let f : MetricTwoJet 3 → (Fin 3 × Fin 3) → ℝ :=
    fun J p => jetRicci J (cb p.1) (cb p.2)
  have hf : ContinuousAt f cylinderModelTwoJet := by
    apply continuousAt_pi.mpr
    intro p
    exact (contDiffAt_jetRicci cylinderModelMetricCoefficient_zero_isInvertible
      (cb p.1) (cb p.2)).continuousAt
  obtain ⟨eta, heta, hnear⟩ := (Metric.continuousAt_iff.mp hf) delta hdelta
  refine ⟨eta, heta, ?_⟩
  intro J hJ i j
  have h := (dist_le_pi_dist (f J) (f cylinderModelTwoJet) (i, j)).trans_lt
    (hnear hJ)
  simpa only [f, Real.dist_eq, cylinderModelTwoJet_ricci] using h

private theorem bilinear_quadratic_le_nine
    (E : CE →ₗ[ℝ] CE →ₗ[ℝ] ℝ) {delta : ℝ}
    (hentry : ∀ i j : Fin 3, |E (cb i) (cb j)| ≤ delta) (v : CE) :
    |E v v| ≤ 9 * delta * ‖v‖ ^ 2 := by
  have hrepr : (∑ i : Fin 3, v i • cb i) = v := by
    simpa only [EuclideanSpace.basisFun_repr] using cb.sum_repr v
  have hexp : E v v = ∑ i : Fin 3, ∑ j : Fin 3, v i * v j * E (cb i) (cb j) := by
    calc
      E v v = E (∑ i : Fin 3, v i • cb i) (∑ j : Fin 3, v j • cb j) := by
        rw [hrepr]
      _ = _ := by
        simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
          smul_eq_mul, Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hterm (i j : Fin 3) :
      |v i * v j * E (cb i) (cb j)| ≤ delta * ‖v‖ ^ 2 := by
    rw [abs_mul, abs_mul]
    have hi : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
    have hj : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v j
    have hmul := mul_le_mul
      (mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)) (hentry i j)
      (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simpa only [pow_two, mul_comm delta, mul_assoc] using hmul
  rw [hexp]
  calc
    _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, v i * v j * E (cb i) (cb j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, delta * ‖v‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j _ => hterm i j))
    _ = _ := by simp; ring

private theorem norm_sq_le_cylinder_metric (z : RoundCylinderSpace) (v : CE) :
    ‖v‖ ^ 2 ≤ EvolvingRoundCylinderMetric 0 z
      (cylinderScalarCoordinateEquiv v) (cylinderScalarCoordinateEquiv v) := by
  rw [show EvolvingRoundCylinderMetric 0 = RoundCylinderMetric from rfl,
    roundCylinderMetric_self_eq, cylinderScalarCoordinateEquiv_apply]
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

private theorem cylinder_ricci_model_quadratic (z : RoundCylinderSpace) (v : CE) :
    (1 / 2 : ℝ) * (EvolvingRoundCylinderMetric 0 z
      (cylinderScalarCoordinateEquiv v) (cylinderScalarCoordinateEquiv v) -
        (cylinderScalarCoordinateEquiv v).2 ^ 2) =
      inner ℝ (cylinderSphereProjection v) (cylinderSphereProjection v) := by
  rw [show EvolvingRoundCylinderMetric 0 = RoundCylinderMetric from rfl,
    roundCylinderMetric_self_eq, real_inner_self_eq_norm_sq]
  change (1 / 2 : ℝ) *
    (2 * ‖(cylinderScalarCoordinateEquiv v).1‖ ^ 2 +
      (cylinderScalarCoordinateEquiv v).2 ^ 2 - (cylinderScalarCoordinateEquiv v).2 ^ 2) =
    ‖(cylinderScalarCoordinateEquiv v).1‖ ^ 2
  ring

theorem exists_neck_ricci_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (N : EpsilonNeck g), N.epsilon ≤ epsilon₀ →
        ∀ z ∈ N.cylinderDomain, ∀ v : RoundCylinderTangent z,
          |D.ricci (N.coordinate_map z)
            (mfderiv CI (𝓡 3) N.coordinate_map z v)
            (mfderiv CI (𝓡 3) N.coordinate_map z v) -
              (1 / 2 : ℝ) * (EvolvingRoundCylinderMetric 0 z v v - v.2 ^ 2)| ≤
            (1 / 100 : ℝ) * EvolvingRoundCylinderMetric 0 z v v := by
  obtain ⟨eta, heta, hmodulus⟩ :=
    exists_cylinder_model_ricci_coefficient_modulus (delta := 1 / 900) (by norm_num)
  obtain ⟨L, hL, hjet⟩ := exists_cylinder_metricTwoJet_bound.{u}
  refine ⟨min (1 / 200) (eta / (2 * L)),
    lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  intro M _ _ _ _ g D N hN z hz v
  have heps : N.epsilon ≤ (1 / 200 : ℝ) := hN.trans (min_le_left _ _)
  have horder : 2 ≤ ⌊N.epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [inv_eq_one_div, le_div_iff₀ N.epsilon_pos]
    norm_num
    linarith
  have hdist : L * N.epsilon < eta := by
    have h := hN.trans (min_le_right _ _)
    have hm := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hL)).mp h
    nlinarith
  have hentries := hmodulus _ ((hjet M g N horder z hz.2).trans_lt hdist)
  let f : CE →L[ℝ] TangentSpace (𝓡 3) (N.coordinate_map z) :=
    (mfderiv CI (𝓡 3) N.coordinate_map z).comp
      cylinderScalarCoordinateEquiv.toContinuousLinearMap
  let E : CE →ₗ[ℝ] CE →ₗ[ℝ] ℝ :=
    (M13.ricciLinear D (N.coordinate_map z)).compl₁₂ f.toLinearMap f.toLinearMap -
      (innerₗ SE).compl₁₂ cylinderSphereProjection.toLinearMap
        cylinderSphereProjection.toLinearMap
  have hE (a b : CE) : E a b =
      D.ricci (N.coordinate_map z)
        (mfderiv CI (𝓡 3) N.coordinate_map z (cylinderScalarCoordinateEquiv a))
        (mfderiv CI (𝓡 3) N.coordinate_map z (cylinderScalarCoordinateEquiv b)) -
      inner ℝ (cylinderSphereProjection a) (cylinderSphereProjection b) := rfl
  have hEbound (i j : Fin 3) : |E (cb i) (cb j)| ≤ (1 / 900 : ℝ) := by
    rw [hE, ← cylinderNeckCoefficients_ricci_zero N D z.1 hz.2]
    exact (hentries i j).le
  let w : CE := cylinderScalarCoordinateEquiv.symm v
  have hw : cylinderScalarCoordinateEquiv w = v :=
    cylinderScalarCoordinateEquiv.apply_symm_apply v
  have hbound := bilinear_quadratic_le_nine E hEbound w
  rw [hE, ← cylinder_ricci_model_quadratic z w, hw] at hbound
  have hnorm := norm_sq_le_cylinder_metric z w
  rw [hw] at hnorm
  exact hbound.trans (by nlinarith)

end PoincareConjecture.M28.tube
