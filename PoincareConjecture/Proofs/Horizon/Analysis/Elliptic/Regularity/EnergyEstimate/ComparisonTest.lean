import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.WeakInequalityLipschitz
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.LipschitzDerivatives









noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)



theorem compact_lipschitz_comparison_test
    {O : Set E} {u v φ : E → ℝ} {A B ε : ℝ≥0}
    (hu : LipschitzOnWith A u O) (hv : LipschitzOnWith B v O)
    (herr : ∀ x ∈ O, |u x - v x| ≤ ε)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) :
    (∀ x, 0 ≤ φ x * (v x - u x + ε)) ∧
      ∃ D : ℝ≥0, LipschitzWith D (fun x => φ x * (v x - u x + ε)) := by
  have hdiff : LipschitzOnWith (B + A) (fun x => v x - u x + (ε : ℝ)) O := by
    simpa using (hv.sub hu).add (LipschitzWith.const (ε : ℝ)).lipschitzOnWith
  obtain ⟨w, hw, heq⟩ := hdiff.extend_real
  let z : E → ℝ := fun x => max 0 (min (2 * (ε : ℝ)) (w x))
  have hz : LipschitzWith (B + A) z := (hw.const_min _).const_max _
  have hz0 (x) : 0 ≤ z x := le_max_left _ _
  have hzB (x) : z x ≤ 2 * (ε : ℝ) :=
    max_le (by positivity) (min_le_left _ _)
  have hprod : (fun x => φ x * z x) = (fun x => φ x * (v x - u x + ε)) := by
    funext x
    by_cases hx : φ x = 0
    · simp only [hx, zero_mul]
    · have hxO := hφO (subset_tsupport _ hx)
      have hb := abs_le.mp (herr x hxO)
      have hlo : 0 ≤ v x - u x + (ε : ℝ) := by linarith
      have hhi : v x - u x + (ε : ℝ) ≤ 2 * (ε : ℝ) := by linarith
      simp only [z, ← heq hxO, min_eq_right hhi, max_eq_right hlo]
  constructor
  · intro x
    rw [← congrFun hprod x]
    exact mul_nonneg (hφ0 x) (hz0 x)
  rw [← hprod]
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by simp)
  refine ⟨B + A + 2 * ε * C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hp := hC.dist_le_mul x y
  have hq := hz.dist_le_mul x y
  simp only [Real.dist_eq] at hp hq ⊢
  calc
    |φ x * z x - φ y * z y| = |φ x * (z x - z y) + z y * (φ x - φ y)| := by ring_nf
    _ ≤ |φ x * (z x - z y)| + |z y * (φ x - φ y)| := abs_add_le _ _
    _ = φ x * |z x - z y| + z y * |φ x - φ y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hφ0 x), abs_of_nonneg (hz0 y)]
    _ ≤ 1 * ((B + A : ℝ≥0) * dist x y) + (2 * (ε : ℝ)) * (C * dist x y) :=
      add_le_add (mul_le_mul (hφ1 x) hq (abs_nonneg _) (by norm_num))
        (mul_le_mul (hzB y) hp (abs_nonneg _) (by positivity))
    _ = ((B + A + 2 * ε * C : ℝ≥0) : ℝ) * dist x y := by push_cast; ring



theorem weakInequality_comparison_test
    {O : Set E} (hO : IsOpen O) {F : Fin d → E → ℝ} {f u v φ : E → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict O))
    (hf : MemLp f 2 (volume.restrict O))
    (hle : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ O → (∀ x, 0 ≤ ψ x) →
      (∫ x in O, ∑ i, F i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) ≤
        ∫ x in O, f x * ψ x)
    {A B ε : ℝ≥0} (hu : LipschitzOnWith A u O) (hv : LipschitzOnWith B v O)
    (herr : ∀ x ∈ O, |u x - v x| ≤ ε)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) :
    (∫ x in O, ∑ i, F i x *
      (φ x * (fderiv ℝ v x (EuclideanSpace.single i 1) -
        fderiv ℝ u x (EuclideanSpace.single i 1)) +
        (v x - u x + ε) * fderiv ℝ φ x (EuclideanSpace.single i 1))) ≤
      ∫ x in O, f x * (φ x * (v x - u x + ε)) := by
  obtain ⟨hψ0, C, hψ⟩ := compact_lipschitz_comparison_test hu hv herr hφ hφc hφO hφ0 hφ1
  have h := weakInequality_of_nonneg_compact_lipschitz hO hF hf hle hψ hψ0
    hφc.mul_right ((tsupport_mul_subset_left (f := φ)).trans hφO)
  convert h using 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hO.measurableSet,
    ae_restrict_of_ae (hu.ae_differentiableWithinAt_of_mem (μ := volume)),
    ae_restrict_of_ae (hv.ae_differentiableWithinAt_of_mem (μ := volume))] with x hx hux hvx
  have du := (hux hx).differentiableAt (hO.mem_nhds hx)
  have dv := (hvx hx).differentiableAt (hO.mem_nhds hx)
  rw [fderiv_fun_mul (d := fun x => v x - u x + (ε : ℝ))
    (hφ.differentiable (by simp) x) ((dv.sub du).add_const _),
    fderiv_add_const, fderiv_fun_sub dv du]
  simp only [add_apply, smul_apply, sub_apply, smul_eq_mul]

end Poincare.Analysis.Elliptic
