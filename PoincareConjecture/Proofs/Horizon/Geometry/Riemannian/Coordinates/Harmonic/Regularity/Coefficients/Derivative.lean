import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Perturbation

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Matrix Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ}

def euclideanDivergenceOperator
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  g.pullbackVolumeDensity id x • (g.euclideanCoefficients x).inverse.comp (innerSL ℝ)

theorem euclideanDivergenceOperator_basis_apply
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    (g.euclideanDivergenceOperator x (EuclideanSpace.basisFun (Fin n) ℝ j)) i =
      LeviCivitaData.Dirichlet.divergenceCoefficients g
        (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n))) x i j := by
  have hb : g.pullbackCoefficients
      (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n))) x =
      g.euclideanCoefficients x := by
    ext u v
    simp [pullbackCoefficients]
    rfl
  have hdual : innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j) =
      EuclideanSpace.proj (𝕜 := ℝ) j := by
    ext v
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  simp only [euclideanDivergenceOperator, smul_apply, ContinuousLinearMap.comp_apply,
    hdual, PiLp.smul_apply, smul_eq_mul,
    LeviCivitaData.Dirichlet.divergenceCoefficients, hb]
  rfl

theorem contDiff_euclideanDivergenceOperator
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
    ContDiff ℝ ∞ g.euclideanDivergenceOperator := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hginv : (g.euclideanCoefficients x).IsInvertible := by
    convert! g.inner_isInvertible x
  have hρ := (g.contDiffAt_pullbackVolumeDensity (x := x) contMDiffAt_id
    (by simpa using Function.injective_id)).1
  exact hρ.smul ((hginv.contDiffAt_map_inverse.comp x
    (g.contDiffAt_euclideanCoefficients x)).clm_comp contDiffAt_const)

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.HarmonicCoordinates

theorem exists_divergence_operator_derivative_bound {n : ℕ} :
    let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (x : EuclideanSpace ℝ (Fin n)),
        ‖g.euclideanCoefficients x - B₀‖ < δ →
        ‖fderiv ℝ g.euclideanDivergenceOperator x‖ ≤
          L * ‖fderiv ℝ g.euclideanCoefficients x‖ := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let V := E →L[ℝ] E →L[ℝ] ℝ
  let B₀ : V := innerSL ℝ
  let d : V → ℝ := fun B =>
    Matrix.det (fun i j : Fin n => B (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j))
  let ρ : V → ℝ := fun B => Real.sqrt (d B)
  let A : V → E →L[ℝ] E := fun B => ρ B • B.inverse.comp B₀
  have hd₀ : d B₀ = 1 := by
    have hm : (fun i j : Fin n => B₀ (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) =
        (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      change inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) = _
      exact (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite i j
    dsimp only [d]
    rw [hm, Matrix.det_one]
  have hd : ContDiffAt ℝ ∞ d B₀ := by
    have heq : d = fun B : V =>
        ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) *
          ∏ i, B (EuclideanSpace.basisFun (Fin n) ℝ (σ i))
            (EuclideanSpace.basisFun (Fin n) ℝ i) := by
      funext B
      simp [d, Matrix.det_apply, Units.smul_def]
    rw [heq]
    apply ContDiffAt.sum
    intro σ _
    apply contDiffAt_const.mul
    apply contDiffAt_prod
    intro i _
    fun_prop
  have hB : B₀.IsInvertible := by
    refine ⟨(InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv, ?_⟩
    rfl
  have hA : ContDiffAt ℝ ∞ A B₀ :=
    (hd.sqrt (by rw [hd₀]; norm_num)).smul
      ((hB.contDiffAt_map_inverse (n := ∞)).clm_comp contDiffAt_const)
  have hbound : ∀ᶠ B in 𝓝 B₀,
      ‖fderiv ℝ A B‖ < ‖fderiv ℝ A B₀‖ + 1 :=
    (hA.continuousAt_fderiv (by simp)).norm.eventually
      (gt_mem_nhds (by linarith))
  have hdiff : ∀ᶠ B in 𝓝 B₀, ContDiffAt ℝ 1 A B :=
    (hA.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by simp)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp (hbound.and hdiff)
  refine ⟨δ, ‖fderiv ℝ A B₀‖ + 1, hδ, by positivity, fun g x hx => ?_⟩
  have hnear := hδbound (y := g.euclideanCoefficients x)
    (by simpa only [E, V, B₀, dist_eq_norm] using hx)
  have hρg (y : E) : ρ (g.euclideanCoefficients y) = g.pullbackVolumeDensity id y := by
    unfold ρ d RiemannianMetric.pullbackVolumeDensity
    apply congrArg Real.sqrt
    apply congrArg Matrix.det
    ext i j
    simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply, Matrix.of_apply]
    rfl
  have heq : g.euclideanDivergenceOperator = A ∘ g.euclideanCoefficients := by
    funext y
    simp only [Function.comp_apply, A, hρg, RiemannianMetric.euclideanDivergenceOperator, B₀]
  rw [heq, fderiv_comp x ((hnear.2).differentiableAt (by norm_num))
    ((g.contDiffAt_euclideanCoefficients x).differentiableAt (by simp))]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right hnear.1.le (norm_nonneg _))

end PoincareConjecture.HarmonicCoordinates
