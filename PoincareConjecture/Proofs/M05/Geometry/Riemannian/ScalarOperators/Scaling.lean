import PoincareConjecture.Definitions.Ch01.ScalarOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
lemma mvfderiv_const_mul (c : ℝ) (f : M → ℝ) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => c * f y) x v = c * mvfderiv (𝓡 n) f x v := by
  by_cases hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x
  · rw [mvfderiv_fun_mul mdifferentiableAt_const hf]
    simp [mvfderiv]
  · by_cases hc : c = 0
    · subst c
      have he : (fun y => (0 : ℝ) * f y) = fun _ => (0 : ℝ) := funext fun _ => zero_mul _
      rw [he]
      simp [mvfderiv]
    · have hcf : ¬ MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => c * f y) x := by
        intro h
        apply hf
        have h' : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => c⁻¹ * (c * f y)) x :=
          mdifferentiableAt_const.mul h
        simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using h'
      simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hf,
        mfderiv_zero_of_not_mdifferentiableAt hcf]

lemma LeviCivitaData.hessian_const_mul {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (c : ℝ) (f : M → ℝ) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => c * f y) x u v = c * D.hessian f x u v := by
  simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields, mvfderiv_const_mul]
  ring

lemma LeviCivitaData.laplacian_const_mul {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (c : ℝ) (f : M → ℝ) (x : M) :
    D.laplacian (fun y => c * f y) x = c * D.laplacian f x := by
  simp only [LeviCivitaData.laplacian, D.hessian_const_mul, Finset.mul_sum]

end PoincareConjecture
