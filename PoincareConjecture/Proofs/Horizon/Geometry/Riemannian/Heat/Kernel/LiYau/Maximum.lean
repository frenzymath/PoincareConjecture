import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Product
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema








set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem neg_two_mvfderiv_cutoff_le (D : LeviCivitaData g)
    (η f : M → ℝ) (x : M) {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ)
    (hη : 0 ≤ η x)
    (hg : g.inner x (D.gradient η x) (D.gradient η x) ≤ A * η x) :
    -2 * mvfderiv (𝓡 n) η x (D.gradient f x) ≤
      η x * g.inner x (D.gradient f x) (D.gradient f x) / δ + δ * A := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let w := g.inner x (D.gradient f x) (D.gradient f x)
  let d := mvfderiv (𝓡 n) η x (D.gradient f x)
  have hw : 0 ≤ w := by
    change 0 ≤ inner ℝ (D.gradient f x) (D.gradient f x)
    exact real_inner_self_nonneg
  have hd : d ^ 2 ≤ A * (η x * w) := by
    rw [show d = g.inner x (D.gradient η x) (D.gradient f x) from
      (D.inner_gradient η x (D.gradient f x)).symm]
    have h := real_inner_mul_inner_self_le (D.gradient η x) (D.gradient f x)
    change g.inner x (D.gradient η x) (D.gradient f x) *
      g.inner x (D.gradient η x) (D.gradient f x) ≤
      g.inner x (D.gradient η x) (D.gradient η x) * w at h
    nlinarith [mul_le_mul_of_nonneg_right hg hw]
  let a := η x * w / δ
  let b := δ * A
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hη hw) hδ.le
  have hb : 0 ≤ b := mul_nonneg hδ.le hA
  have hab : a * b = A * (η x * w) := by dsimp [a, b]; field_simp
  have hs : (-2 * d) ^ 2 ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  change -2 * d ≤ a + b
  nlinarith [sq_nonneg (-2 * d - (a + b))]



theorem cutoff_laplacian_drift_le_of_isLocalMax (D : LeviCivitaData g)
    {η q f : M → ℝ} (hηs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hqs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q) {x : M}
    (hmax : IsLocalMax (fun y => η y * q y) x)
    (hη : 0 < η x) (hq : 0 ≤ q x) {A B δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ)
    (hg : g.inner x (D.gradient η x) (D.gradient η x) ≤ A * η x)
    (hl : -B ≤ D.laplacian η x) :
    η x ^ 2 * (D.laplacian q x +
      2 * mvfderiv (𝓡 n) q x (D.gradient f x)) ≤
      (B + 2 * A + δ * A) * (η x * q x) +
        (η x * q x) * (η x * g.inner x (D.gradient f x) (D.gradient f x) / δ) := by
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => η y * q y) := by
    simpa only [Pi.mul_def] using hηs.mul hqs
  have hcrit := mvfderiv_eq_zero_of_isLocalMax hs hmax
  have hv (v : TangentSpace (𝓡 n) x) :
      η x * mvfderiv (𝓡 n) q x v + q x * mvfderiv (𝓡 n) η x v = 0 := by
    have h := congrArg (fun L => L v) hcrit
    rw [mvfderiv_fun_mul ((hηs x).mdifferentiableAt (by simp))
      ((hqs x).mdifferentiableAt (by simp))] at h
    simpa only [add_apply, smul_apply, smul_eq_mul, zero_apply] using h
  have hcross := hv (D.gradient η x)
  rw [← D.inner_gradient, ← D.inner_gradient,
    g.symm x (D.gradient q x) (D.gradient η x)] at hcross
  have hLap := D.laplacian_nonpos_of_isLocalMax hs hmax
  rw [D.laplacian_mul hηs hqs] at hLap
  have hLap' := mul_nonpos_of_nonneg_of_nonpos hη.le hLap
  have hgrad := mul_le_mul_of_nonneg_left hg hq
  have hlow := mul_le_mul_of_nonneg_left hl (mul_nonneg hη.le hq)
  have hd := D.neg_two_mvfderiv_cutoff_le η f x hA hδ hη.le hg
  have hd' := mul_le_mul_of_nonneg_left hd (mul_nonneg hη.le hq)
  have hdf := hv (D.gradient f x)
  have hdf' := congrArg (fun z : ℝ => η x * z) hdf
  nlinarith



theorem liYau_cutoff_deriv_le_of_isLocalMax (D : LeviCivitaData g)
    (hn : 0 < n) {η q f : M → ℝ}
    (hηs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hqs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q) {x : M}
    (hmax : IsLocalMax (fun y => η y * q y) x)
    (hη : 0 < η x) (hη1 : η x ≤ 1) (hq : 0 ≤ q x) {A B k qt : ℝ}
    (hA : 0 ≤ A) (hk : 0 ≤ k)
    (hg : g.inner x (D.gradient η x) (D.gradient η x) ≤ A * η x)
    (hl : -B ≤ D.laplacian η x)
    (heq : q x = -2 * D.laplacian f x -
      g.inner x (D.gradient f x) (D.gradient f x))
    (hevol : qt - D.laplacian q x ≤
      2 * mvfderiv (𝓡 n) q x (D.gradient f x) -
        (2 / (n : ℝ)) * D.laplacian f x ^ 2 +
        2 * k * g.inner x (D.gradient f x) (D.gradient f x)) :
    η x ^ 2 * qt ≤ (B + ((n : ℝ) + 2) * A) * (η x * q x) -
      (η x * q x) ^ 2 / (2 * (n : ℝ)) + 2 * (n : ℝ) * k ^ 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let w := g.inner x (D.gradient f x) (D.gradient f x)
  have hw : 0 ≤ w := by
    by_cases hv : D.gradient f x = 0
    · simp [w, hv]
    · exact (g.pos x _ hv).le
  have hd := D.cutoff_laplacian_drift_le_of_isLocalMax hηs hqs hmax hη hq
    hA hn' hg hl (f := f)
  have ht := mul_le_mul_of_nonneg_left hevol (sq_nonneg (η x))
  have hcurv : 2 * k * η x ^ 2 * w ≤ 2 * k * (η x * w) := by
    have hηsq : η x ^ 2 ≤ η x := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hηsq (mul_nonneg (by positivity : 0 ≤ 2 * k) hw)]
  have hid : η x ^ 2 * ((2 / (n : ℝ)) * D.laplacian f x ^ 2) =
      ((η x * q x) + η x * w) ^ 2 / (2 * (n : ℝ)) := by
    rw [heq]
    dsimp [w]
    field_simp
    ring
  have hbound : η x ^ 2 * qt ≤
      (B + ((n : ℝ) + 2) * A) * (η x * q x) +
        (η x * q x) * (η x * w / (n : ℝ)) -
        ((η x * q x) + η x * w) ^ 2 / (2 * (n : ℝ)) + 2 * k * (η x * w) := by
    dsimp only [w] at hid ⊢
    nlinarith
  have hs := sq_nonneg (η x * w - 2 * (n : ℝ) * k)
  have hscale := mul_le_mul_of_nonneg_left hbound (le_of_lt (show 0 < 2 * (n : ℝ) by positivity))
  have hc : (2 * (n : ℝ)) *
      ((B + ((n : ℝ) + 2) * A) * (η x * q x) -
        (η x * q x) ^ 2 / (2 * (n : ℝ)) + 2 * (n : ℝ) * k ^ 2) -
      (2 * (n : ℝ)) * (η x ^ 2 * qt) ≥ 0 := by
    field_simp at hscale ⊢
    nlinarith
  nlinarith

end PoincareConjecture.LeviCivitaData
