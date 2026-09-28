import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.ScalarComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Density
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv











noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.RiemannianMetric


theorem contDiffAt_radialDensityRoot {a : ℝ → ℝ} {t : ℝ} (m : ℕ)
    (ha : ContDiffAt ℝ ∞ a t) (hpos : 0 < a t) :
    ContDiffAt ℝ ∞ (fun s => s * a s ^ (1 / (m : ℝ))) t :=
  contDiffAt_id.mul (ha.rpow_const_of_ne hpos.ne')



theorem antitoneOn_density_div_modelS_pow
    {m : ℕ} (hm : 0 < m) {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R)
    {a : ℝ → ℝ}
    (ha : ∀ t ∈ Icc (0 : ℝ) R, ContDiffAt ℝ ∞ a t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) R, 0 < a t)
    (hle : ∀ t ∈ Ioo (0 : ℝ) R,
      deriv (deriv (fun s => s * a s ^ (1 / (m : ℝ)))) t ≤
        κ * (t * a t ^ (1 / (m : ℝ)))) :
    AntitoneOn (fun t => t ^ m * a t / modelS κ t ^ m) (Ioo (0 : ℝ) R) := by
  let y := fun t => t * a t ^ (1 / (m : ℝ))
  have hy (t : ℝ) (ht : t ∈ Icc (0 : ℝ) R) : ContDiffAt ℝ ∞ y t :=
    contDiffAt_radialDensityRoot m (ha t ht) (hpos t ht)
  have hmono : AntitoneOn (fun t => y t / modelS κ t) (Ioo (0 : ℝ) R) := by
    apply antitoneOn_div_modelS_of_second_derivative_le hκ hR
      (y' := deriv y) (y'' := deriv (deriv y))
    · exact fun t ht => ((hy t ht).differentiableAt (by simp)).hasDerivAt
    · exact fun t ht => ((hy t ht).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt
    · exact fun t ht => (((hy t ⟨ht.1.le, ht.2.le⟩).derivWithin (m := ∞)
        (by simp)).differentiableAt (by simp)).hasDerivAt
    · simp [y]
    · exact hle
  have heq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R) :
      (y t / modelS κ t) ^ m = t ^ m * a t / modelS κ t ^ m := by
    rw [div_pow]
    dsimp only [y]
    rw [mul_pow, one_div, Real.rpow_inv_natCast_pow (hpos t ⟨ht.1.le, ht.2.le⟩).le hm.ne']
  intro t ht s hs hts
  dsimp only
  rw [← heq t ht, ← heq s hs]
  apply pow_le_pow_left₀ _ (hmono ht hs hts)
  exact div_nonneg (mul_nonneg hs.1.le (Real.rpow_nonneg (hpos s ⟨hs.1.le, hs.2.le⟩).le _))
    (modelS_nonneg hκ hs.1.le)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem contDiffAt_pullbackVolumeDensity_radialRoot
    (g : RiemannianMetric n M) (m : ℕ)
    {e : EuclideanSpace ℝ (Fin n) → M} (v : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e (t • v))
    (hinj : Function.Injective (mfderiv (𝓡 n) (𝓡 n) e (t • v))) :
    ContDiffAt ℝ ∞ (fun s => s * g.pullbackVolumeDensity e (s • v) ^
      (1 / (m : ℝ))) t := by
  obtain ⟨hc, hp⟩ := g.contDiffAt_pullbackVolumeDensity he hinj
  have hcomp : ContDiffAt ℝ ∞ (fun s : ℝ => g.pullbackVolumeDensity e (s • v)) t :=
    hc.comp (f := fun s : ℝ => s • v) t (by fun_prop)
  exact contDiffAt_radialDensityRoot m hcomp hp

end PoincareConjecture.RiemannianMetric
