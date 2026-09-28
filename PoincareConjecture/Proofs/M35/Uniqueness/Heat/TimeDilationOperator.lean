import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeDilationFamily
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CompactTimeMultiplier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def dilatedCoefficientLp {a b T B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hT : 0 ≤ T) (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → E →L[ℝ] F) (hA : ContDiffOn ℝ ∞ A (Icc 0 B)) (s : ℝ) :
    Lp E 2 (SpectralHeatNative.timeMeasure T) →L[ℝ]
      Lp F 2 (SpectralHeatNative.timeMeasure T) :=
  compactTimeLp hT (compactDilationJet ha hab hBT hB A hA 0 s)

theorem contDiffOn_dilatedCoefficientLp {a b T B : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hT : 0 ≤ T) (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → E →L[ℝ] F) (hA : ContDiffOn ℝ ∞ A (Icc 0 B)) :
    ContDiffOn ℝ ∞ (dilatedCoefficientLp ha hab.le hT hBT hB A hA) (Icc a b) :=
  (compactTimeLp (E := E) (F := F) hT).contDiff.comp_contDiffOn
    (contDiffOn_compactDilation ha hab hBT hB A hA)

theorem dilatedCoefficientLp_coe {a b T B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hT : 0 ≤ T) (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → E →L[ℝ] F) (hA : ContDiffOn ℝ ∞ A (Icc 0 B))
    {s : ℝ} (hs : s ∈ Icc a b) (u : Lp E 2 (SpectralHeatNative.timeMeasure T)) :
    ∀ᵐ t ∂SpectralHeatNative.timeMeasure T,
      dilatedCoefficientLp ha hab hT hBT hB A hA s u t = A (s * t) (u t) := by
  filter_upwards [compactTimeLp_coe hT (compactDilationJet ha hab hBT hB A hA 0 s) u,
    ae_restrict_mem measurableSet_Ioc] with t ht htime
  have he := ht (Ioc_subset_Icc_self htime)
  rw [compactDilationJet_apply ha hab hBT hB A hA 0 hs, pow_zero, one_smul,
    iteratedDerivWithin_zero] at he
  exact he

end PoincareConjecture.M35.Uniqueness.Heat
