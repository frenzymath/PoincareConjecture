import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Density











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem tangentNorm_mfderiv_radial_eq
    (g : RiemannianMetric n M) {e : EuclideanSpace ℝ (Fin n) → M}
    {v : EuclideanSpace ℝ (Fin n)} (he : MDifferentiableAt (𝓡 n) (𝓡 n) e v) :
    g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v v) =
      g.tangentNorm (e ((1 : ℝ) • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun t : ℝ => e (t • v)) 1 1) := by
  have hline : HasDerivAt (fun t : ℝ => t • v) v 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const v
  have he' : MDifferentiableAt (𝓡 n) (𝓡 n) e ((1 : ℝ) • v) := by
    simpa only [one_smul] using he
  have hd := mfderiv_comp (1 : ℝ) he' hline.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv] at hd
  have hd1 := congrArg (fun A => A (1 : ℝ)) hd
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun t : ℝ => e (t • v)) 1 1 =
    mfderiv (𝓡 n) (𝓡 n) e ((1 : ℝ) • v)
      (fderiv ℝ (fun t : ℝ => t • v) 1 1) at hd1
  simp only [TangentSpace] at hd1
  rw [fderiv_eq_smul_deriv, one_smul, hline.deriv, one_smul] at hd1
  unfold tangentNorm
  simp only [TangentSpace]
  rw [one_smul, hd1]

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] in


theorem pullbackVolumeDensity_eq_one_of_radial_speed
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
    (g : RiemannianMetric 1 M)
    {e : EuclideanSpace ℝ (Fin 1) → M} {v : EuclideanSpace ℝ (Fin 1)}
    (hv : v ≠ 0)
    (hspeed : g.tangentNorm (e v) (mfderiv (𝓡 1) (𝓡 1) e v v) = ‖v‖) :
    g.pullbackVolumeDensity e v = 1 := by
  let b := EuclideanSpace.basisFun (Fin 1) ℝ
  let a := b.repr v 0
  have hva : a • b 0 = v := by
    simpa only [Fin.sum_univ_one] using b.sum_repr v
  have ha : a ≠ 0 := by
    intro ha
    apply hv
    simpa only [ha, zero_smul] using hva.symm
  have hn : ‖v‖ = |a| := by
    rw [← hva, norm_smul, b.norm_eq_one, mul_one, Real.norm_eq_abs]
  have ht : ∀ (c : ℝ) (w : EuclideanSpace ℝ (Fin 1)),
      g.tangentNorm (e v) (c • w) = |c| * g.tangentNorm (e v) w := by
    intro c w
    simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  have hs : g.tangentNorm (e v) (mfderiv (𝓡 1) (𝓡 1) e v (b 0)) = 1 := by
    have hmap : mfderiv (𝓡 1) (𝓡 1) e v v =
        a • mfderiv (𝓡 1) (𝓡 1) e v (b 0) := by
      exact (congrArg (mfderiv (𝓡 1) (𝓡 1) e v) hva.symm).trans
        ((mfderiv (𝓡 1) (𝓡 1) e v).map_smul a (b 0))
    have hh := hspeed
    rw [hmap, ht, hn] at hh
    exact mul_left_cancel₀ (abs_ne_zero.mpr ha) (by simpa only [mul_one] using hh)
  simpa only [pullbackVolumeDensity, Matrix.det_fin_one, Matrix.of_apply, tangentNorm, b]
    using hs

end PoincareConjecture.RiemannianMetric
