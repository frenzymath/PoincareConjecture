import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Logarithm
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Laplacian.TimeDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Bochner
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.TraceBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Ricci













set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem neg_laplacian_logarithmic_heat_evolution (D : LeviCivitaData g)
    {f : ℝ × M → ℝ} {t : ℝ}
    (hf : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, x))
    (heq : ∀ x, HasDerivAt (fun s => f (s, x))
      (D.laplacian (fun y => f (t, y)) x +
        g.inner x (D.gradient (fun y => f (t, y)) x)
          (D.gradient (fun y => f (t, y)) x)) t) (x : M) :
    let q := fun s y => -D.laplacian (fun z => f (s, z)) y
    deriv (fun s => q s x) t - D.laplacian (q t) x =
      2 * mvfderiv (𝓡 n) (q t) x (D.gradient (fun y => f (t, y)) x) -
        2 * (∑ i, ∑ j, D.hessian (fun y => f (t, y)) x
          (g.orthonormalBasis x i) (g.orthonormalBasis x j) ^ 2) -
        2 * D.ricci x (D.gradient (fun y => f (t, y)) x)
          (D.gradient (fun y => f (t, y)) x) := by
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f (t, y)) :=
    fun y => (hf y).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  have hd := (D.hasDerivAt_laplacian_of_time_derivative hf heq x).neg
  simp only [Pi.neg_def] at hd
  dsimp only
  rw [hd.deriv, D.laplacian_add (D.contMDiff_laplacian hs)
    (D.contMDiff_inner_gradient hs hs)]
  have hneg : D.laplacian (fun y => -D.laplacian (fun z => f (t, z)) y) x =
      -D.laplacian (D.laplacian (fun z => f (t, z))) x := by
    simpa only [neg_one_mul] using D.laplacian_const_mul (-1)
      (D.laplacian (fun z => f (t, z))) x
  rw [hneg, D.bochner_identity hs, mvfderiv_fun_neg]
  simp only [neg_apply]
  ring



theorem neg_laplacian_logarithmic_heat_evolution_le (D : LeviCivitaData g)
    (hn : 0 < n) {f : ℝ × M → ℝ} {t k : ℝ}
    (hf : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, x))
    (heq : ∀ x, HasDerivAt (fun s => f (s, x))
      (D.laplacian (fun y => f (t, y)) x +
        g.inner x (D.gradient (fun y => f (t, y)) x)
          (D.gradient (fun y => f (t, y)) x)) t)
    (x : M) (hRic : ∀ v : TangentSpace (𝓡 n) x,
      -k * g.inner x v v ≤ D.ricci x v v) :
    let q := fun s y => -D.laplacian (fun z => f (s, z)) y
    deriv (fun s => q s x) t - D.laplacian (q t) x ≤
      2 * mvfderiv (𝓡 n) (q t) x (D.gradient (fun y => f (t, y)) x) -
        (2 / (n : ℝ)) * q t x ^ 2 +
        2 * k * g.inner x (D.gradient (fun y => f (t, y)) x)
          (D.gradient (fun y => f (t, y)) x) := by
  dsimp only
  have hid := D.neg_laplacian_logarithmic_heat_evolution hf heq x
  dsimp only at hid
  rw [hid]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have htrace : D.laplacian (fun y => f (t, y)) x ^ 2 / (n : ℝ) ≤
      ∑ i, ∑ j, D.hessian (fun y => f (t, y)) x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j) ^ 2 := by
    apply (div_le_iff₀ hn').mpr
    rw [mul_comm]
    exact D.laplacian_sq_le_dim_mul_hessian_normSq (fun y => f (t, y)) x
  have hr := hRic (D.gradient (fun y => f (t, y)) x)
  rw [neg_sq]
  have he : (2 / (n : ℝ)) * D.laplacian (fun y => f (t, y)) x ^ 2 =
      2 * (D.laplacian (fun y => f (t, y)) x ^ 2 / (n : ℝ)) := by ring
  rw [he]
  linarith



theorem gradient_normSq_logarithmic_heat_evolution (D : LeviCivitaData g)
    {f : ℝ × M → ℝ} {t : ℝ}
    (hf : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, x))
    (heq : ∀ x, HasDerivAt (fun s => f (s, x))
      (D.laplacian (fun y => f (t, y)) x +
        g.inner x (D.gradient (fun y => f (t, y)) x)
          (D.gradient (fun y => f (t, y)) x)) t) (x : M) :
    let w := fun s y => g.inner y (D.gradient (fun z => f (s, z)) y)
      (D.gradient (fun z => f (s, z)) y)
    deriv (fun s => w s x) t - D.laplacian (w t) x =
      2 * mvfderiv (𝓡 n) (w t) x (D.gradient (fun y => f (t, y)) x) -
        2 * (∑ i, ∑ j, D.hessian (fun y => f (t, y)) x
          (g.orthonormalBasis x i) (g.orthonormalBasis x j) ^ 2) -
        2 * D.ricci x (D.gradient (fun y => f (t, y)) x)
          (D.gradient (fun y => f (t, y)) x) := by
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f (t, y)) :=
    fun y => (hf y).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  dsimp only
  rw [(D.hasDerivAt_gradient_normSq_of_time_derivative (hf x) heq).deriv,
    D.bochner_identity hs,
    mvfderiv_fun_add ((D.contMDiff_laplacian hs x).mdifferentiableAt (by simp))
      ((D.contMDiff_inner_gradient hs hs x).mdifferentiableAt (by simp))]
  simp only [add_apply]
  ring



theorem liYau_logarithmic_heat_evolution (D : LeviCivitaData g)
    {f : ℝ × M → ℝ} {t : ℝ}
    (hf : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, x))
    (heq : ∀ x, HasDerivAt (fun s => f (s, x))
      (D.laplacian (fun y => f (t, y)) x +
        g.inner x (D.gradient (fun y => f (t, y)) x)
          (D.gradient (fun y => f (t, y)) x)) t) (α : ℝ) (x : M) :
    let q := fun s y => α * (-D.laplacian (fun z => f (s, z)) y) +
      (1 - α) * g.inner y (D.gradient (fun z => f (s, z)) y)
        (D.gradient (fun z => f (s, z)) y)
    deriv (fun s => q s x) t - D.laplacian (q t) x =
      2 * mvfderiv (𝓡 n) (q t) x (D.gradient (fun y => f (t, y)) x) -
        2 * (∑ i, ∑ j, D.hessian (fun y => f (t, y)) x
          (g.orthonormalBasis x i) (g.orthonormalBasis x j) ^ 2) -
        2 * D.ricci x (D.gradient (fun y => f (t, y)) x)
          (D.gradient (fun y => f (t, y)) x) := by
  let q := fun s y => -D.laplacian (fun z => f (s, z)) y
  let w := fun s y => g.inner y (D.gradient (fun z => f (s, z)) y)
    (D.gradient (fun z => f (s, z)) y)
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f (t, y)) :=
    fun y => (hf y).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  have hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q t) := (D.contMDiff_laplacian hs).neg
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (w t) := D.contMDiff_inner_gradient hs hs
  have hdq : DifferentiableAt ℝ (fun s => q s x) t :=
    (D.hasDerivAt_laplacian_of_time_derivative hf heq x).neg.differentiableAt
  have hdw : DifferentiableAt ℝ (fun s => w s x) t :=
    (D.hasDerivAt_gradient_normSq_of_time_derivative (hf x) heq).differentiableAt
  have hd := (hdq.hasDerivAt.const_mul α).add (hdw.hasDerivAt.const_mul (1 - α))
  have hqα : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => α * q t y) :=
    contMDiff_const.mul hq
  have hwα : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => (1 - α) * w t y) :=
    contMDiff_const.mul hw
  have h₁ := D.neg_laplacian_logarithmic_heat_evolution hf heq x
  have h₂ := D.gradient_normSq_logarithmic_heat_evolution hf heq x
  change deriv (fun s => α * q s x + (1 - α) * w s x) t -
    D.laplacian (fun y => α * q t y + (1 - α) * w t y) x =
      2 * mvfderiv (𝓡 n) (fun y => α * q t y + (1 - α) * w t y) x
        (D.gradient (fun y => f (t, y)) x) - _ - _
  simp only [Pi.add_def] at hd
  rw [hd.deriv, D.laplacian_add hqα hwα, D.laplacian_const_mul,
    D.laplacian_const_mul,
    mvfderiv_fun_add ((hqα x).mdifferentiableAt (by simp))
      ((hwα x).mdifferentiableAt (by simp))]
  simp only [add_apply, mvfderiv_const_mul]
  change deriv (fun s => q s x) t - D.laplacian (q t) x = _ at h₁
  change deriv (fun s => w s x) t - D.laplacian (w t) x = _ at h₂
  linear_combination α * h₁ + (1 - α) * h₂



theorem liYau_evolution_inequality (D : LeviCivitaData g)
    (hn : 0 < n) {k : ℝ}
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {u : ℝ × M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (Ioi 0 ×ˢ univ))
    (hpos : ∀ t, 0 < t → ∀ x, 0 < u (t, x))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => u (s, x))
      (D.laplacian (fun y => u (t, y)) x) t) (α : ℝ) :
    let f := fun s y => Real.log (u (s, y))
    let w := fun s y => g.inner y (D.gradient (f s) y) (D.gradient (f s) y)
    let q := fun s y => α * (-D.laplacian (f s) y) + (1 - α) * w s y
    (∀ t, 0 < t → ∀ x, q t x = w t x - α * deriv (fun s => f s x) t) ∧
    (∀ t, 0 < t → ∀ x,
      deriv (fun s => q s x) t - D.laplacian (q t) x ≤
        2 * mvfderiv (𝓡 n) (q t) x (D.gradient (f t) x) -
          (2 / (n : ℝ)) * D.laplacian (f t) x ^ 2 + 2 * k * w t x) := by
  let f : ℝ × M → ℝ := fun p => Real.log (u p)
  have huat (t : ℝ) (ht : 0 < t) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (t, x) :=
    hu.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  have hf (t : ℝ) (ht : 0 < t) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, x) :=
    contMDiffAt_log_of_pos (huat t ht x) (hpos t ht x)
  have heq (t : ℝ) (ht : 0 < t) :=
    D.hasDerivAt_log_heat (huat t ht) (hpos t ht) (hheat t ht)
  dsimp only
  constructor
  · intro t ht x
    rw [(heq t ht x).deriv]
    ring
  · intro t ht x
    have hid := D.liYau_logarithmic_heat_evolution (hf t ht) (heq t ht) α x
    dsimp only [f] at hid
    rw [hid]
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have htrace : D.laplacian (fun y => f (t, y)) x ^ 2 / (n : ℝ) ≤
        ∑ i, ∑ j, D.hessian (fun y => f (t, y)) x
          (g.orthonormalBasis x i) (g.orthonormalBasis x j) ^ 2 := by
      apply (div_le_iff₀ hn').mpr
      rw [mul_comm]
      exact D.laplacian_sq_le_dim_mul_hessian_normSq (fun y => f (t, y)) x
    have hr := hRic x (D.gradient (fun y => f (t, y)) x)
    have he : (2 / (n : ℝ)) * D.laplacian (fun y => f (t, y)) x ^ 2 =
        2 * (D.laplacian (fun y => f (t, y)) x ^ 2 / (n : ℝ)) := by ring
    change _ ≤ _ - (2 / (n : ℝ)) * D.laplacian (fun y => f (t, y)) x ^ 2 + _
    rw [he]
    dsimp only [f] at htrace hr
    linarith



theorem liYau_evolution_inequality_of_abs_sectionalCurvature_le [T2Space M]
    (D : LeviCivitaData g) (hn : 0 < n) {K : ℝ}
    (hsec : ∀ x v w, |D.sectionalCurvature x v w| ≤ K)
    {u : ℝ × M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (Ioi 0 ×ˢ univ))
    (hpos : ∀ t, 0 < t → ∀ x, 0 < u (t, x))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => u (s, x))
      (D.laplacian (fun y => u (t, y)) x) t) (α : ℝ) :
    let f := fun s y => Real.log (u (s, y))
    let w := fun s y => g.inner y (D.gradient (f s) y) (D.gradient (f s) y)
    let q := fun s y => α * (-D.laplacian (f s) y) + (1 - α) * w s y
    (∀ t, 0 < t → ∀ x, q t x = w t x - α * deriv (fun s => f s x) t) ∧
    (∀ t, 0 < t → ∀ x,
      deriv (fun s => q s x) t - D.laplacian (q t) x ≤
        2 * mvfderiv (𝓡 n) (q t) x (D.gradient (f t) x) -
          (2 / (n : ℝ)) * D.laplacian (f t) x ^ 2 +
          2 * (((n : ℝ) - 1) * K) * w t x) := by
  apply D.liYau_evolution_inequality hn
  intro x v
  simpa only [neg_mul] using
    D.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le x K (hsec x) v
  exact hu
  exact hpos
  exact hheat

end PoincareConjecture.LeviCivitaData
