import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Operator








noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


lemma abs_ricci_le_tangentNorm (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    |D.ricci x u v| ≤ (n : ℝ) * D.curvatureTensorNorm x *
      g.tangentNorm x u * g.tangentNorm x v := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hb (i) : g.tangentNorm x (b i) = 1 := by
    change Real.sqrt (inner ℝ (b i) (b i)) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one]
    norm_num
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simp
  calc
    |D.ricci x u v| = |∑ i, D.curvatureTensor x u (b i) v (b i)| := rfl
    _ ≤ ∑ i, |D.curvatureTensor x u (b i) v (b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, D.curvatureTensorNorm x * g.tangentNorm x u * g.tangentNorm x v := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [hb, mul_one] using D.abs_curvatureTensor_le_tangentNorm x u (b i) v (b i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim, nsmul_eq_mul]
      ring



lemma abs_ricci_le_of_upper_ellipticity (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) {b K : ℝ} (hb : 0 ≤ b)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ b * ‖v‖ ^ 2)
    (hcurv : D.curvatureTensorNorm x ≤ K) (u v : EuclideanSpace ℝ (Fin n)) :
    |D.ricci x u v| ≤ (n : ℝ) * K * b * ‖u‖ * ‖v‖ := by
  have hN : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
  have hK : 0 ≤ K := hN.trans hcurv
  have hnu : 0 ≤ g.tangentNorm x u := Real.sqrt_nonneg _
  have hnv : 0 ≤ g.tangentNorm x v := Real.sqrt_nonneg _
  have hnorm (w : EuclideanSpace ℝ (Fin n)) :
      g.tangentNorm x w ≤ Real.sqrt b * ‖w‖ := by
    have h := Real.sqrt_le_sqrt (hupper w)
    simpa only [RiemannianMetric.tangentNorm, Real.sqrt_mul hb,
      Real.sqrt_sq (norm_nonneg w)] using h
  calc
    _ ≤ (n : ℝ) * D.curvatureTensorNorm x * g.tangentNorm x u * g.tangentNorm x v :=
      D.abs_ricci_le_tangentNorm x u v
    _ ≤ (n : ℝ) * K * (Real.sqrt b * ‖u‖) * (Real.sqrt b * ‖v‖) := by
      gcongr <;> exact hnorm _
    _ = (n : ℝ) * K * (Real.sqrt b * Real.sqrt b) * ‖u‖ * ‖v‖ := by ring
    _ = _ := by rw [Real.mul_self_sqrt hb]

end PoincareConjecture.LeviCivitaData
