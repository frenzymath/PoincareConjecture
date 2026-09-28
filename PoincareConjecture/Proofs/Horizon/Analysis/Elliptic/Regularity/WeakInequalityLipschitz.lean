import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.WeakInequalityExtension
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Lipschitz

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Poincare.Analysis.Sobolev.Weak

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memLp_lineDeriv_of_hasCompactSupport {v : E → ℝ} {C : ℝ≥0}
    (hv : LipschitzWith C v) (hvc : HasCompactSupport v) (p : ℝ≥0∞) (w : E) :
    MemLp (fun x => lineDeriv ℝ v x w) p volume := by
  let K := tsupport v
  let q := fun x => lineDeriv ℝ v x w
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hvc.measure_lt_top (μ := volume)⟩
  have hq : MemLp q p (volume.restrict K) :=
    (hv.memLp_lineDeriv (μ := volume.restrict K) w).mono_exponent le_top
  have heq : K.indicator q = q := by
    funext x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      have hgerm : v =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
      have hz := hgerm.lineDeriv_eq (𝕜 := ℝ) (v := w)
      simpa only [q, lineDeriv, Pi.zero_apply, deriv_const] using hz.symm
  have hi : MemLp (K.indicator q) p volume :=
    (memLp_indicator_iff_restrict hvc.measurableSet).mpr hq
  rwa [heq] at hi

end Poincare.Analysis.Sobolev.Weak

namespace Poincare.Analysis.Elliptic

open Poincare.Analysis.Sobolev.Weak

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weakInequality_of_nonneg_compact_lipschitz
    {O : Set E} (hO : IsOpen O) {F : Fin d → E → ℝ} {f v : E → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict O))
    (hf : MemLp f 2 (volume.restrict O))
    (hle : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ O → (∀ x, 0 ≤ φ x) →
      (∫ x in O, ∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) ≤
        ∫ x in O, f x * φ x)
    {C : ℝ≥0} (hv : LipschitzWith C v) (hv0 : ∀ x, 0 ≤ v x)
    (hvc : HasCompactSupport v) (hvO : tsupport v ⊆ O) :
    (∫ x in O, ∑ i, F i x * fderiv ℝ v x (EuclideanSpace.single i 1)) ≤
      ∫ x in O, f x * v x := by
  have h := weakInequality_of_nonneg_compact_memW1p_univ hO hF hf hle
    (hv.continuous.memLp_of_hasCompactSupport hvc)
    (fun i => memLp_lineDeriv_of_hasCompactSupport hv hvc 2 (EuclideanSpace.single i 1))
    (fun i => hasWeakPartialDeriv_lineDeriv_of_lipschitz hv i) hv0 hvc hvO
  convert h using 1
  apply integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_of_ae hv.ae_differentiableAt] with x hx
  simp only [hx.lineDeriv_eq_fderiv]

end Poincare.Analysis.Elliptic
