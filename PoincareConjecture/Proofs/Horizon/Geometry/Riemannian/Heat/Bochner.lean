import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Bochner
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.GradientTime
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Ricci
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Product

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem gradient_normSq_gradient_normSq_le (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) :
    let q := fun y => g.inner y (D.gradient f y) (D.gradient f y)
    g.inner x (D.gradient q x) (D.gradient q x) ≤
      4 * q x * (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  rw [D.gradient_normSq_eq_sum_mvfderiv_sq]
  simp_rw [D.mvfderiv_gradient_normSq hf, D.sum_hessian_sq_eq_inner_connection_gradient hf,
    D.hessian_eq_inner_connection_gradient hf]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := real_inner_mul_inner_self_le
    (D.connection (D.gradient f) x (g.orthonormalBasis x i)) (D.gradient f x)
  change (2 * inner ℝ (D.connection (D.gradient f) x (g.orthonormalBasis x i))
      (D.gradient f x)) ^ 2 ≤
    4 * inner ℝ (D.gradient f x) (D.gradient f x) *
      inner ℝ (D.connection (D.gradient f) x (g.orthonormalBasis x i))
        (D.connection (D.gradient f) x (g.orthonormalBasis x i))
  nlinarith only [h]

theorem heat_square_identity (D : LeviCivitaData g)
    {F : ℝ × M → ℝ} {t : ℝ}
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x))
    (hheat : ∀ x, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t) (x : M) :
    deriv (fun s => F (s, x) ^ 2) t -
      D.laplacian (fun y => F (t, y) ^ 2) x =
      -2 * g.inner x (D.gradient (fun y => F (t, y)) x)
        (D.gradient (fun y => F (t, y)) x) := by
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => F (t, y)) := by
    intro y
    exact (hF y).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  have hd := (hheat x).pow 2
  simp only [Pi.pow_def] at hd
  rw [hd.deriv, D.laplacian_sq hs]
  norm_num

theorem heat_bochner_identity (D : LeviCivitaData g)
    {F : ℝ × M → ℝ} {t : ℝ}
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x))
    (hheat : ∀ x, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t) (x : M) :
    deriv (fun s => g.inner x (D.gradient (fun y => F (s, y)) x)
        (D.gradient (fun y => F (s, y)) x)) t -
      D.laplacian (fun y => g.inner y (D.gradient (fun z => F (t, z)) y)
        (D.gradient (fun z => F (t, z)) y)) x =
      -2 * (∑ i, ∑ j, (D.hessian (fun y => F (t, y)) x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) -
      2 * D.ricci x (D.gradient (fun y => F (t, y)) x)
        (D.gradient (fun y => F (t, y)) x) := by
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => F (t, y)) := by
    intro y
    exact (hF y).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  rw [(D.hasDerivAt_gradient_normSq_of_time_derivative (hF x) hheat).deriv,
    D.bochner_identity hs]
  ring

theorem heat_gradient_normSq_subsolution (D : LeviCivitaData g)
    {F : ℝ × M → ℝ} {t : ℝ} {k : ℝ}
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x))
    (hheat : ∀ x, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t)
    (x : M)
    (hRic : -k * g.inner x (D.gradient (fun y => F (t, y)) x)
        (D.gradient (fun y => F (t, y)) x) ≤
      D.ricci x (D.gradient (fun y => F (t, y)) x)
        (D.gradient (fun y => F (t, y)) x)) :
    deriv (fun s => g.inner x (D.gradient (fun y => F (s, y)) x)
        (D.gradient (fun y => F (s, y)) x)) t -
      D.laplacian (fun y => g.inner y (D.gradient (fun z => F (t, z)) y)
        (D.gradient (fun z => F (t, z)) y)) x ≤
      2 * k * g.inner x (D.gradient (fun y => F (t, y)) x)
        (D.gradient (fun y => F (t, y)) x) := by
  rw [D.heat_bochner_identity hF hheat]
  have hnonneg : 0 ≤ ∑ i, ∑ j, (D.hessian (fun y => F (t, y)) x
      (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  nlinarith

theorem heat_regularized_gradient_norm_subsolution (D : LeviCivitaData g)
    {F : ℝ × M → ℝ} {t k ε : ℝ} (hk : 0 ≤ k) (hε : 0 < ε)
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x))
    (hheat : ∀ x, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t)
    (x : M)
    (hRic : -k * g.inner x (D.gradient (fun y => F (t, y)) x)
        (D.gradient (fun y => F (t, y)) x) ≤
      D.ricci x (D.gradient (fun y => F (t, y)) x)
        (D.gradient (fun y => F (t, y)) x)) :
    let w := fun s y => Real.sqrt (g.inner y (D.gradient (fun z => F (s, z)) y)
      (D.gradient (fun z => F (s, z)) y) + ε)
    deriv (fun s => w s x) t - D.laplacian (w t) x ≤ k * w t x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let q := fun s y => g.inner y (D.gradient (fun z => F (s, z)) y)
    (D.gradient (fun z => F (s, z)) y)
  let w := fun s y => Real.sqrt (q s y + ε)
  let H := ∑ i, ∑ j, (D.hessian (fun y => F (t, y)) x
    (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2
  have hH : 0 ≤ H :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hqpos (s : ℝ) (y : M) : 0 ≤ q s y := by
    change 0 ≤ inner ℝ (D.gradient (fun z => F (s, z)) y)
      (D.gradient (fun z => F (s, z)) y)
    exact real_inner_self_nonneg
  have hpos (s : ℝ) (y : M) : 0 < q s y + ε := add_pos_of_nonneg_of_pos (hqpos s y) hε
  have hwpos (s : ℝ) (y : M) : 0 < w s y := Real.sqrt_pos.mpr (hpos s y)
  have hwsq (s : ℝ) (y : M) : w s y ^ 2 = q s y + ε := Real.sq_sqrt (hpos s y).le
  have hs (y : M) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun z => F (t, z)) y :=
    (hF y).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  have hq (y : M) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q t) y := by
    have hg := D.contMDiffAt_gradient (hs y)
    have hi := ((g.contMDiff y).clm_bundle_apply hg).clm_bundle_apply hg
    exact (Bundle.contMDiffAt_totalSpace.mp hi).2
  have hw (y : M) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (w t) y :=
    (Real.contDiffAt_sqrt (hpos t y).ne').contMDiffAt.comp y
      ((hq y).add contMDiffAt_const)
  have hshift (y : M) : mvfderiv (𝓡 n) (fun z => q t z + ε) y =
      mvfderiv (𝓡 n) (q t) y := by
    simp only [mvfderiv_fun_add ((hq y).mdifferentiableAt (by simp)) mdifferentiableAt_const,
      mvfderiv_const, add_zero]
  have hgshift : D.gradient (fun y => q t y + ε) x = D.gradient (q t) x := by
    simp only [gradient, hshift]
  have hlshift : D.laplacian (fun y => q t y + ε) x = D.laplacian (q t) x := by
    simp only [laplacian, hessian, hessianOnFields, hshift]
  have hgrad := D.gradient_mul ((hw x).mdifferentiableAt (by simp))
    ((hw x).mdifferentiableAt (by simp))
  simp only [← pow_two, hwsq, hgshift] at hgrad
  have hgradSq : g.inner x (D.gradient (q t) x) (D.gradient (q t) x) =
      4 * w t x ^ 2 * g.inner x (D.gradient (w t) x) (D.gradient (w t) x) := by
    rw [hgrad]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  have hKato := D.gradient_normSq_gradient_normSq_le (hs x)
  change g.inner x (D.gradient (q t) x) (D.gradient (q t) x) ≤ 4 * q t x * H at hKato
  rw [hgradSq] at hKato
  have hgradle : g.inner x (D.gradient (w t) x) (D.gradient (w t) x) ≤ H := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * w t x ^ 2 from
      mul_pos (by norm_num) (sq_pos_of_pos (hwpos t x)))).mp
    nlinarith only [hKato, congrArg (fun z => 4 * z * H) (hwsq t x),
      mul_nonneg hε.le hH]
  have hlap := D.laplacian_sq hw x
  simp only [hwsq, hlshift] at hlap
  have hdq := D.hasDerivAt_gradient_normSq_of_time_derivative (hF x) hheat
  have hdw := (hdq.add_const ε).sqrt (hpos t x).ne'
  change HasDerivAt (fun s => w s x) _ t at hdw
  have htime : 2 * w t x * deriv (fun s => w s x) t = deriv (fun s => q s x) t := by
    rw [hdw.deriv, hdq.deriv]
    change 2 * w t x * (_ / (2 * w t x)) = _
    field_simp [(hwpos t x).ne']
  have hBochner := D.heat_bochner_identity hF hheat x
  change deriv (fun s => q s x) t - D.laplacian (q t) x = -2 * H - _ at hBochner
  change deriv (fun s => w s x) t - D.laplacian (w t) x ≤ k * w t x
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * w t x from
    mul_pos (by norm_num) (hwpos t x))).mp
  nlinarith only [htime, hlap, hBochner, hgradle, hRic,
    congrArg (fun z => 2 * k * z) (hwsq t x), mul_nonneg hk hε.le]

theorem heat_gradient_normSq_subsolution_of_abs_sectionalCurvature_le [T2Space M]
    (D : LeviCivitaData g) {F : ℝ × M → ℝ} {t K : ℝ}
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x))
    (hheat : ∀ x, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t)
    (x : M)
    (hsec : ∀ u w : TangentSpace (𝓡 n) x, |D.sectionalCurvature x u w| ≤ K) :
    deriv (fun s => g.inner x (D.gradient (fun y => F (s, y)) x)
        (D.gradient (fun y => F (s, y)) x)) t -
      D.laplacian (fun y => g.inner y (D.gradient (fun z => F (t, z)) y)
        (D.gradient (fun z => F (t, z)) y)) x ≤
      2 * (((n : ℝ) - 1) * K) *
        g.inner x (D.gradient (fun y => F (t, y)) x)
          (D.gradient (fun y => F (t, y)) x) := by
  apply D.heat_gradient_normSq_subsolution hF hheat x
  simpa only [neg_mul] using
    D.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le x K hsec
      (D.gradient (fun y => F (t, y)) x)

theorem weighted_heat_gradient_normSq_subsolution [T2Space M]
    (D : LeviCivitaData g) {F : ℝ × M → ℝ} {t K : ℝ}
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x))
    (hheat : ∀ x, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t)
    (x : M)
    (hsec : ∀ u w : TangentSpace (𝓡 n) x, |D.sectionalCurvature x u w| ≤ K) :
    let q := fun s y => g.inner y (D.gradient (fun z => F (s, z)) y)
      (D.gradient (fun z => F (s, z)) y)
    deriv (fun s => Real.exp (-2 * (((n : ℝ) - 1) * K) * s) * q s x) t -
      D.laplacian (fun y => Real.exp (-2 * (((n : ℝ) - 1) * K) * t) * q t y) x ≤ 0 := by
  let q := fun s y => g.inner y (D.gradient (fun z => F (s, z)) y)
    (D.gradient (fun z => F (s, z)) y)
  let k := ((n : ℝ) - 1) * K
  have hq := D.hasDerivAt_gradient_normSq_of_time_derivative (hF x) hheat
  have hw := (((hasDerivAt_id t).const_mul (-2 * k)).exp).mul hq
  simp only [Pi.mul_def, id_eq, mul_one] at hw
  have hsub := D.heat_gradient_normSq_subsolution_of_abs_sectionalCurvature_le hF hheat x hsec
  change deriv (fun s => Real.exp (-2 * k * s) * q s x) t -
    D.laplacian (fun y => Real.exp (-2 * k * t) * q t y) x ≤ 0
  dsimp only [q]
  rw [hw.deriv, D.laplacian_const_mul]
  rw [hq.deriv] at hsub
  have h := mul_le_mul_of_nonneg_left hsub (Real.exp_nonneg (-2 * k * t))
  dsimp [q, k] at *
  nlinarith

end PoincareConjecture.LeviCivitaData
