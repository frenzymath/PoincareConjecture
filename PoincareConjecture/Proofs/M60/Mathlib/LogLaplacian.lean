import PoincareConjecture.Proofs.M60.Mathlib.LocalScalarChain
import PoincareConjecture.Proofs.M60.Mathlib.IntegralRegularization
import PoincareConjecture.Proofs.M04.ScalarEstimates
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem laplacian_log_add (D : LeviCivitaData g) {q : M → ℝ}
    (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q) (ε : ℝ) (x : M)
    (hpos : 0 < q x + ε) :
    D.laplacian (fun y => Real.log (q y + ε)) x =
      D.laplacian q x / (q x + ε) - M04.scalarGradientSq g q x / (q x + ε) ^ 2 := by
  let φ : ℝ → ℝ := fun t => Real.log (t + ε)
  have hφ : ContDiffOn ℝ ∞ φ (Ioi (-ε)) := by
    intro t ht
    change -ε < t at ht
    exact ((contDiffAt_id.add contDiffAt_const).log (by dsimp; linarith)).contDiffWithinAt
  have hfirst {t : ℝ} (ht : -ε < t) : deriv φ t = (t + ε)⁻¹ := by
    have h := ((hasDerivAt_id t).add_const ε).log (by linarith : t + ε ≠ 0)
    simpa [φ] using h.deriv
  have hfirst_germ : deriv φ =ᶠ[𝓝 (q x)] fun t => (t + ε)⁻¹ := by
    filter_upwards [isOpen_Ioi.mem_nhds (by change -ε < q x; linarith : q x ∈ Ioi (-ε))]
      with t ht
    exact hfirst ht
  have hsecond : deriv (deriv φ) (q x) = -(1 / (q x + ε) ^ 2) := by
    rw [hfirst_germ.deriv_eq]
    convert! (((hasDerivAt_id (q x)).add_const ε).inv hpos.ne').deriv using 1
    simp only [neg_div, id_eq]
  have h := laplacian_comp_of_contDiffOn D hq isOpen_Ioi hφ
    (by change -ε < q x; linarith : q x ∈ Ioi (-ε))
  rw [hfirst (by linarith), hsecond] at h
  simpa only [φ, div_eq_mul_inv, one_mul, mul_one, neg_mul, sub_eq_add_neg, mul_comm] using h

theorem laplacian_log_add_lower_bound (D : LeviCivitaData g) {q k : M → ℝ}
    (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q) (hnonneg : ∀ x, 0 ≤ q x)
    (hreg : ∀ x, 0 < q x →
      M04.scalarGradientSq g q x / q x + 2 * q x - 2 * q x * k x ≤ D.laplacian q x)
    {ε : ℝ} (he : 0 < ε) (x : M) :
    2 * q x / (q x + ε) - 2 * q x * k x / (q x + ε) ≤
      D.laplacian (fun y => Real.log (q y + ε)) x := by
  by_cases hx : 0 < q x
  · rw [laplacian_log_add D hq ε x (add_pos hx he)]
    exact log_regularization_inequality hx he
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hreg x hx)
  · have hz : q x = 0 := le_antisymm (le_of_not_gt hx) (hnonneg x)
    have hlog : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => Real.log (q y + ε)) := by
      intro y
      exact (Real.contDiffAt_log.mpr
        (add_pos_of_nonneg_of_pos (hnonneg y) he).ne').contMDiffAt.comp y
        ((hq y).add contMDiffAt_const)
    have hmin : IsLocalMin (fun y => Real.log (q y + ε)) x := by
      apply Eventually.of_forall
      intro y
      dsimp
      rw [hz, zero_add]
      exact Real.strictMonoOn_log.monotoneOn he
        (add_pos_of_nonneg_of_pos (hnonneg y) he)
        (le_add_of_nonneg_left (hnonneg y))
    simpa only [hz, mul_zero, zero_mul, zero_div, sub_self] using
      D.laplacian_nonneg_of_isLocalMin (hlog x) hmin

end PoincareConjecture.M60
