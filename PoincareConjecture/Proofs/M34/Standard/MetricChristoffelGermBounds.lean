import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.ChristoffelBounds
import PoincareConjecture.Proofs.M34.Mathlib.BilinearPullbackJetBound

set_option autoImplicit false

set_option maxSynthPendingDepth 8

open Set
open scoped ContDiff
open Poincare.Analysis.Calculus

namespace PoincareConjecture.CoordinateTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_inverse_metric_germ_jet_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) {a K : ℝ} (ha : 0 < a) (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A : F → E →L[ℝ] E →L[ℝ] ℝ) (x : F),
      ContDiffAt ℝ ∞ A x →
      (∀ j ≤ n, ‖iteratedFDeriv ℝ j A x‖ ≤ K) →
      (∀ v, a * ‖v‖ ^ 2 ≤ A x v v) →
      ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun y => (A y).inverse) x‖ ≤ C := by
  have hj := hasUniformJetBoundsOn_inverse_elliptic (E := E) ha K n
  choose B hB using fun j : Fin (n + 1) => hj j.val (by omega)
  obtain ⟨B0, hB0⟩ := Finite.exists_le B
  let B1 := max 1 B0
  have hB1 : 0 ≤ B1 := zero_le_one.trans (le_max_left _ _)
  refine ⟨max 1 (n.factorial * B1 * K ^ n), le_max_left _ _, ?_⟩
  intro A x hA hjets hell j hjn
  have hx : ‖A x‖ ≤ K ∧ ∀ v, a * ‖v‖ ^ 2 ≤ A x v v :=
    ⟨by simpa only [norm_iteratedFDeriv_zero] using hjets 0 (Nat.zero_le n), hell⟩
  have hinv : ContDiffAt ℝ ∞
      (ContinuousLinearMap.inverse : (E →L[ℝ] E →L[ℝ] ℝ) → (E →L[ℝ] ℝ) →L[ℝ] E)
      (A x) := (isInvertible_of_uniformEllipticity ha hell).contDiffAt_map_inverse
  have hb := Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_le_of_contDiffAt hA hinv j
    (A := B1) (B := K) (fun l hl => ?_)
    (fun l hl hlj => (hjets l (hlj.trans hjn)).trans (le_self_pow₀ hK (by omega)))
  · change ‖iteratedFDeriv ℝ j (ContinuousLinearMap.inverse ∘ A) x‖ ≤ _
    refine hb.trans ((le_trans ?_ (le_max_right _ _)))
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hjn) hB1)
      (pow_le_pow_right₀ hK hjn) (pow_nonneg (zero_le_one.trans hK) _) (by positivity)
  · let li : Fin (n + 1) := ⟨l, by omega⟩
    exact (hB li () (A x) hx).trans ((hB0 li).trans (le_max_right _ _))

private noncomputable def germKoszulOperator :
    (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap
  let flipT :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toLinearIsometry.toContinuousLinearMap
  let C := ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ)
    (E →L[ℝ] E →L[ℝ] ℝ) flipL
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ + flipT.comp C - C.comp flipT)

private noncomputable def germChristoffelContraction :
    ((E →L[ℝ] ℝ) →L[ℝ] E) →L[ℝ]
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E)).comp
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)

theorem exists_christoffel_germ_jet_bound (n : ℕ) {a K : ℝ}
    (ha : 0 < a) (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E),
      ContDiffAt ℝ ∞ A x →
      (∀ j ≤ n + 1, ‖iteratedFDeriv ℝ j A x‖ ≤ K) →
      (∀ v, a * ‖v‖ ^ 2 ≤ A x v v) →
      ∀ j ≤ n, ‖iteratedFDeriv ℝ j (CoordinateExponential.christoffelBilinear A) x‖ ≤ C := by
  obtain ⟨B, hB, hBb⟩ := exists_inverse_metric_germ_jet_bound (E := E) (F := E) n ha hK
  let op := germKoszulOperator (E := E)
  let pair := germChristoffelContraction (E := E)
  let D := ‖op‖ * K
  have hD : 0 ≤ D := mul_nonneg (norm_nonneg op) (zero_le_one.trans hK)
  refine ⟨max 1 (‖pair‖ * 2 ^ n * B * D), le_max_left _ _, ?_⟩
  intro A x hA hjets hell j hj
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ A) x := hA.fderiv_right (by simp)
  have hkos : ContDiffAt ℝ ∞ (fun y => op (fderiv ℝ A y)) x :=
    op.contDiff.contDiffAt.comp x hd
  have hinv : ContDiffAt ℝ ∞ (fun y => (A y).inverse) x :=
    (isInvertible_of_uniformEllipticity ha hell).contDiffAt_map_inverse.comp x hA
  have hkosj (l : ℕ) (hl : l ≤ j) :
      ‖iteratedFDeriv ℝ l (fun y => op (fderiv ℝ A y)) x‖ ≤ D := by
    have h := op.norm_iteratedFDeriv_comp_left hd (by exact_mod_cast le_top : (l : ℕ∞ω) ≤ ∞)
    rw [norm_iteratedFDeriv_fderiv] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hjets (l + 1) (by omega)) (norm_nonneg op))
  have hb := norm_iteratedFDeriv_bilinear_le_of_jet_bounds pair hinv hkos j
    (zero_le_one.trans hB)
    (fun l hl => hBb A x hA (fun k hk => hjets k (by omega)) hell l (hl.trans hj)) hkosj
  have heq : CoordinateExponential.christoffelBilinear A =
      (fun y => pair (A y).inverse (op (fderiv ℝ A y))) := rfl
  rw [heq]
  refine hb.trans ((le_trans ?_ (le_max_right _ _)))
  gcongr
  norm_num

end PoincareConjecture.CoordinateTransition
