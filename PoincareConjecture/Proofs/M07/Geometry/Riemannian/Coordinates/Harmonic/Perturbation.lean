import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Harmonic.DivergenceBounds









noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Matrix

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ}



lemma norm_bilinear_le_of_quadratic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hsymm : ∀ u v, B u v = B v u)
    (hquad : ∀ v, |B v v| ≤ ε * ‖v‖ ^ 2) : ‖B‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε
  intro u hu
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε
  intro v hv
  have hpolar : 4 * B u v = B (u + v) (u + v) - B (u - v) (u - v) := by
    simp only [map_add, add_apply, map_sub, sub_apply, hsymm v u]
    ring
  have hpar := parallelogram_law_with_norm ℝ u v
  rw [hu, hv] at hpar
  have hbound := (abs_sub (B (u + v) (u + v)) (B (u - v) (u - v))).trans
    (add_le_add (hquad (u + v)) (hquad (u - v)))
  rw [← hpolar, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hbound
  change |B u v| ≤ ε
  nlinarith



theorem exists_divergence_coefficient_tolerance {ε : ℝ} (hε : 0 < ε) :
    let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (x : EuclideanSpace ℝ (Fin n)),
        ‖g.euclideanCoefficients x - B₀‖ < δ →
        ‖g.pullbackVolumeDensity id x •
          ((g.euclideanCoefficients x).inverse.comp B₀) -
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ < ε := by
  let E := EuclideanSpace ℝ (Fin n)
  let V := E →L[ℝ] E →L[ℝ] ℝ
  let B₀ : V := innerSL ℝ
  let ρ : V → ℝ := fun B => Real.sqrt
    (Matrix.det (fun i j : Fin n => B (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)))
  let A : V → E →L[ℝ] E := fun B => ρ B • B.inverse.comp B₀
  have hρ : Continuous ρ := by
    unfold ρ
    fun_prop
  have hB : B₀.IsInvertible := by
    refine ⟨(InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv, ?_⟩
    rfl
  have hA : ContinuousAt A B₀ := by
    exact hρ.continuousAt.smul
      ((hB.contDiffAt_map_inverse (n := 1)).continuousAt.clm_comp continuousAt_const)
  have hρ₀ : ρ B₀ = 1 := by
    have hm : (fun i j : Fin n => B₀ (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) =
        (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      change inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) = _
      exact (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite i j
    dsimp only [ρ]
    rw [hm, Matrix.det_one, Real.sqrt_one]
  have hA₀ : A B₀ = ContinuousLinearMap.id ℝ E := by
    ext v
    simp only [A, hρ₀, one_smul, ContinuousLinearMap.comp_apply,
      hB.inverse_apply_self, ContinuousLinearMap.id_apply]
  obtain ⟨δ, hδ, htolerance⟩ := Metric.continuousAt_iff.mp hA ε hε
  refine ⟨δ, hδ, fun g x hx => ?_⟩
  have hρg : ρ (g.euclideanCoefficients x) = g.pullbackVolumeDensity id x := by
    unfold ρ RiemannianMetric.pullbackVolumeDensity
    apply congrArg Real.sqrt
    apply congrArg Matrix.det
    ext i j
    simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply, Matrix.of_apply]
    rfl
  have h := htolerance (show dist (g.euclideanCoefficients x) B₀ < δ by
    simpa only [dist_eq_norm, B₀] using hx)
  rw [hA₀, dist_eq_norm] at h
  simpa only [A, hρg, B₀] using h



theorem exists_divergence_coefficient_tolerance_of_quadratic {ε : ℝ} (hε : 0 < ε) :
    let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (x : EuclideanSpace ℝ (Fin n)),
        (∀ v, |g.euclideanCoefficients x v v - ‖v‖ ^ 2| ≤ δ * ‖v‖ ^ 2) →
        ‖g.pullbackVolumeDensity id x •
          ((g.euclideanCoefficients x).inverse.comp B₀) -
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ < ε := by
  let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  obtain ⟨δ, hδ, htolerance⟩ := exists_divergence_coefficient_tolerance (n := n) hε
  refine ⟨δ / 2, by positivity, fun g x hquad => htolerance g x ?_⟩
  have hnorm : ‖g.euclideanCoefficients x - B₀‖ ≤ δ / 2 := by
    apply norm_bilinear_le_of_quadratic _ (by positivity)
    · intro u v
      change g.inner x u v - inner ℝ u v = g.inner x v u - inner ℝ v u
      rw [g.symm, real_inner_comm]
    · intro v
      change |g.euclideanCoefficients x v v - inner ℝ v v| ≤ δ / 2 * ‖v‖ ^ 2
      simpa only [real_inner_self_eq_norm_sq] using hquad v
  exact hnorm.trans_lt (by linarith)

end PoincareConjecture.HarmonicCoordinates
