import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeDilationOperator









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def normalizedDilationLp (J : V →L[ℝ] H) {a b T B : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hT : 0 ≤ T) (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → V →L[ℝ] V) (hA : ContDiffOn ℝ ∞ A (Icc 0 B)) (s : ℝ) :
    Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T) :=
  (ContinuousLinearMap.id ℝ V - J.adjoint.comp J).compLpL 2 (timeMeasure T) +
    s • dilatedCoefficientLp ha hab hT hBT hB A hA s

theorem contDiffOn_normalizedDilationLp (J : V →L[ℝ] H) {a b T B : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hT : 0 ≤ T) (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → V →L[ℝ] V) (hA : ContDiffOn ℝ ∞ A (Icc 0 B)) :
    ContDiffOn ℝ ∞ (normalizedDilationLp J ha hab.le hT hBT hB A hA) (Icc a b) :=
  contDiffOn_const.add
    (contDiffOn_id.smul (contDiffOn_dilatedCoefficientLp ha hab hT hBT hB A hA))

theorem normalizedDilationLp_generator (J : V →L[ℝ] H) {a b T B : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hT : 0 ≤ T) (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → V →L[ℝ] V) (hA : ContDiffOn ℝ ∞ A (Icc 0 B))
    {s : ℝ} (hs : s ∈ Icc a b) (u : Lp V 2 (timeMeasure T)) :
    ∀ᵐ t ∂timeMeasure T,
      normalizedDilationLp J ha hab hT hBT hB A hA s u t - u t + J.adjoint (J (u t)) =
        s • A (s * t) (u t) := by
  let P := ContinuousLinearMap.id ℝ V - J.adjoint.comp J
  let D := dilatedCoefficientLp ha hab hT hBT hB A hA s
  filter_upwards [P.coeFn_compLpL (p := 2) (μ := timeMeasure T) u,
    dilatedCoefficientLp_coe ha hab hT hBT hB A hA hs u,
    Lp.coeFn_add (P.compLpL 2 (timeMeasure T) u) (s • D u), Lp.coeFn_smul s (D u)]
      with t hp hd hsum hsmul
  change (P.compLpL 2 (timeMeasure T) u + s • D u) t - u t + J.adjoint (J (u t)) = _
  rw [hsum, Pi.add_apply, hsmul, Pi.smul_apply, hp, hd]
  change (u t - J.adjoint (J (u t)) + s • A (s * t) (u t)) - u t + J.adjoint (J (u t)) = _
  abel

end PoincareConjecture.M35.Uniqueness.Heat
