import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.TimeDerivative

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem sum_mvfderiv_mul_eq_inner_gradient (D : LeviCivitaData g)
    (f h : M → ℝ) (x : M) :
    (∑ i, mvfderiv (𝓡 n) f x (g.orthonormalBasis x i) *
      mvfderiv (𝓡 n) h x (g.orthonormalBasis x i)) =
        g.inner x (D.gradient f x) (D.gradient h x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp_rw [← D.inner_gradient]
  have hp := (g.orthonormalBasis x).sum_inner_mul_inner (D.gradient f x) (D.gradient h x)
  convert hp using 1 <;> try rfl
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (D.gradient f x) (g.orthonormalBasis x i) *
    inner ℝ (D.gradient h x) (g.orthonormalBasis x i) = _
  rw [real_inner_comm (D.gradient h x)]

theorem gradient_normSq_eq_sum_mvfderiv_sq (D : LeviCivitaData g)
    (f : M → ℝ) (x : M) :
    g.inner x (D.gradient f x) (D.gradient f x) =
      ∑ i, (mvfderiv (𝓡 n) f x (g.orthonormalBasis x i)) ^ 2 := by
  simpa only [pow_two] using (D.sum_mvfderiv_mul_eq_inner_gradient f f x).symm

theorem hasDerivAt_gradient_normSq_of_time_derivative (D : LeviCivitaData g)
    {F : ℝ × M → ℝ} {dF : M → ℝ} {t : ℝ} {x : M}
    (hF : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x))
    (hdF : ∀ y, HasDerivAt (fun s => F (s, y)) (dF y) t) :
    HasDerivAt
      (fun s => g.inner x (D.gradient (fun y => F (s, y)) x)
        (D.gradient (fun y => F (s, y)) x))
      (2 * mvfderiv (𝓡 n) dF x (D.gradient (fun y => F (t, y)) x)) t := by
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (Poincare.Manifold.hasDerivAt_mvfderiv_time hF hdF (g.orthonormalBasis x i)).pow 2)
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at hsum
  have heq : (∑ i, (fun s => mvfderiv (𝓡 n) (fun y => F (s, y)) x
      (g.orthonormalBasis x i)) ^ 2) =
      (fun s => g.inner x (D.gradient (fun y => F (s, y)) x)
        (D.gradient (fun y => F (s, y)) x)) := by
    funext s
    simp only [Finset.sum_apply, Pi.pow_apply]
    exact (D.gradient_normSq_eq_sum_mvfderiv_sq _ _).symm
  rw [heq] at hsum
  apply hsum.congr_deriv
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have hp := D.sum_mvfderiv_mul_eq_inner_gradient (fun y => F (t, y)) dF x
  rw [hp, g.symm, D.inner_gradient]

theorem hasDerivAt_gradient_normSq (D : LeviCivitaData g)
    {F : ℝ × M → ℝ}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F)
    (t : ℝ) (x : M) :
    HasDerivAt
      (fun s => g.inner x (D.gradient (fun y => F (s, y)) x)
        (D.gradient (fun y => F (s, y)) x))
      (2 * mvfderiv (𝓡 n) (fun y => deriv (fun s => F (s, y)) t) x
        (D.gradient (fun y => F (t, y)) x)) t := by
  apply D.hasDerivAt_gradient_normSq_of_time_derivative (hF (t, x))
  intro y
  have hs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => F (s, y)) t :=
    (hF (t, y)).comp t (contMDiffAt_id.prodMk contMDiffAt_const)
  exact (hs.contDiffAt.differentiableAt (by simp)).hasDerivAt

end PoincareConjecture.LeviCivitaData
