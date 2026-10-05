import PoincareLib.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareLib.Geometry.Manifold.ContDiff.TimeDerivative

/-!
# Time differentiation of the metric gradient norm

The metric is fixed in time. Mixed scalar derivatives commute by chart
calculus, and Parseval's identity expresses the squared gradient norm using
those scalar derivatives. This is the time derivative in Chow et al.,
Part III, Proposition 26.49, Step 2, between (26.143) and (26.144),
printed p. 381 (PDF p. 402).
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Parseval's identity pairs two differentials through the retained metric. -/
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

/-- The squared gradient norm is the sum of squared directional derivatives. -/
theorem gradient_normSq_eq_sum_mvfderiv_sq (D : LeviCivitaData g)
    (f : M → ℝ) (x : M) :
    g.inner x (D.gradient f x) (D.gradient f x) =
      ∑ i, (mvfderiv (𝓡 n) f x (g.orthonormalBasis x i)) ^ 2 := by
  simpa only [pow_two] using (D.sum_mvfderiv_mul_eq_inner_gradient f f x).symm

/-- Local joint smoothness differentiates the gradient norm using the actual
scalar time derivative, with no gradient commutation hypothesis. -/
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

/-- Joint smoothness alone gives the time derivative of the retained gradient norm. -/
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

end PoincareMT.LeviCivitaData
