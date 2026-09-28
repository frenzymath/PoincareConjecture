import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.L2Pairing
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.NonnegativeApproximation








noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal
open Poincare.Analysis.Sobolev.Weak

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)



theorem weakInequality_of_nonneg_compact_memW1p_univ
    {O : Set E} (hO : IsOpen O) {F : Fin d → E → ℝ} {f v : E → ℝ}
    {q : Fin d → E → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict O))
    (hf : MemLp f 2 (volume.restrict O))
    (hle : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ O → (∀ x, 0 ≤ φ x) →
      (∫ x in O, ∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) ≤
        ∫ x in O, f x * φ x)
    (hv : MemLp v 2 volume) (hq : ∀ i, MemLp (q i) 2 volume)
    (hwq : ∀ i, HasWeakPartialDeriv i (q i) v univ)
    (hv0 : ∀ x, 0 ≤ v x) (hvc : HasCompactSupport v) (hvO : tsupport v ⊆ O) :
    (∫ x in O, ∑ i, F i x * q i x) ≤ ∫ x in O, f x * v x := by
  obtain ⟨K, φ, hK, hKO, _, hφ, hφK, hφ0, hφlim, hgradlim⟩ :=
    exists_nonneg_smooth_compactSupport_approx (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num) hv hq hwq hv0 hvc hO hvO
  have hφc (k : ℕ) : HasCompactSupport (φ k) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hφK k)
  have hφLp (k : ℕ) : MemLp (φ k) 2 (volume.restrict O) :=
    ((hφ k).continuous.memLp_of_hasCompactSupport (hφc k)).restrict O
  have hdφLp (k : ℕ) (i : Fin d) :
      MemLp (fun x => fderiv ℝ (φ k) x (EuclideanSpace.single i 1))
        2 (volume.restrict O) := by
    have hdφ := ((hφ k).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply
      (contDiff_const (c := EuclideanSpace.single i (1 : ℝ)))
    exact (hdφ.continuous.memLp_of_hasCompactSupport
      ((hφc k).fderiv_apply (𝕜 := ℝ) _)).restrict O
  have hrestrict {a : ℕ → E → ℝ}
      (ha : Tendsto (fun k => eLpNorm (a k) 2 volume) atTop (𝓝 0)) :
      Tendsto (fun k => eLpNorm (a k) 2 (volume.restrict O)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ha (fun _ => bot_le)
      (fun k => eLpNorm_mono_measure (a k) Measure.restrict_le_self)
  have hlim (i : Fin d) : Tendsto
      (fun k => ∫ x in O, F i x * fderiv ℝ (φ k) x (EuclideanSpace.single i 1))
      atTop (𝓝 (∫ x in O, F i x * q i x)) :=
    tendsto_integral_mul_of_eLpNorm_sub (hF i) ((hq i).restrict O)
      (fun k => hdφLp k i) (hrestrict (hgradlim i))
  have hleft : Tendsto
      (fun k => ∫ x in O, ∑ i, F i x * fderiv ℝ (φ k) x (EuclideanSpace.single i 1))
      atTop (𝓝 (∫ x in O, ∑ i, F i x * q i x)) := by
    have hsumq : (∫ x in O, ∑ i, F i x * q i x) =
        ∑ i, ∫ x in O, F i x * q i x := by
      simpa using integral_finsetSum Finset.univ
        (fun i _ => (hF i).integrable_mul ((hq i).restrict O))
    rw [hsumq]
    convert tendsto_finsetSum Finset.univ (fun i _ => hlim i) using 1
    ext k
    simpa using integral_finsetSum Finset.univ
      (fun i _ => (hF i).integrable_mul (hdφLp k i))
  have hright := tendsto_integral_mul_of_eLpNorm_sub hf (hv.restrict O) hφLp
    (hrestrict hφlim)
  exact le_of_tendsto_of_tendsto hleft hright <|
    Filter.Eventually.of_forall fun k => hle _ (hφ k) (hφc k) ((hφK k).trans hKO) (hφ0 k)

end Poincare.Analysis.Elliptic
