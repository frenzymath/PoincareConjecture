import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.DifferenceQuotient.WeakDerivative
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.CrossTerms.Principal
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Iterated.WeakDerivatives
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.L2

noncomputable section

open Set MeasureTheory
open scoped ENNReal
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memW1p_of_integral_diffQuot_bound
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    {p : Fin d → E → ℝ} (hp : ∀ i, MemLp (p i) 2 volume)
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (hbound : ∀ k : Fin d, ∃ C : ℝ, ∀ h : ℝ, h ≠ 0 → |h| ≤ h₀ →
      (∫ x in V, ∑ i, diffQuot k h (p i) x ^ 2) ≤ C) :
    ∀ i, MemW1p 2 (p i) V := by
  intro i
  refine ⟨(hp i).restrict V, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hbound k
  have hb (h : ℝ) (hh : 0 < |h|) (hle : |h| ≤ h₀) :
      eLpNorm (diffQuot k h (p i)) 2 (volume.restrict V) ≤
        ENNReal.ofReal (Real.sqrt C) := by
    have hq (j : Fin d) := (memLp_diffQuot_two k h (hp j)).restrict V
    have hsq (j : Fin d) : Integrable (fun x => diffQuot k h (p j) x ^ 2)
        (volume.restrict V) := by
      simpa only [pow_two, Pi.mul_def] using (hq j).integrable_mul (hq j)
    apply eLpNorm_two_le_sqrt_of_integral_sq_le (hq i)
    apply le_trans _ (hC h (abs_pos.mp hh) hle)
    apply integral_mono (hsq i)
      (integrable_finsetSum _ (fun j _ => hsq j))
    intro x
    exact Finset.single_le_sum (fun j _ => sq_nonneg (diffQuot k h (p j) x))
      (Finset.mem_univ i)
  obtain ⟨q, hq, hweak, _⟩ := hasWeakPartialDeriv_of_diffQuot_uniform_bound_loc
    isOpen_univ hV hVc hh₀ (subset_univ _) (by simpa using hp i)
    k (Real.sqrt_nonneg C) hb
  exact ⟨q, hq, hweak⟩

theorem memWkp_two_of_integral_diffQuot_bound
    [NeZero d] {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    {u : E → ℝ} {p : Fin d → E → ℝ}
    (hu : MemLp u 2 volume) (hp : ∀ i, MemLp (p i) 2 volume)
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u univ)
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (hbound : ∀ k : Fin d, ∃ C : ℝ, ∀ h : ℝ, h ≠ 0 → |h| ≤ h₀ →
      (∫ x in V, ∑ i, diffQuot k h (p i) x ^ 2) ≤ C) :
    MemWkp 2 2 u V := by
  apply memWkp_succ_of_weakDerivatives hV (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (hu.restrict V) (g := p)
  · intro i
    exact MemWkp.one_iff_memW1p.mpr
      (memW1p_of_integral_diffQuot_bound hV hVc hp hh₀ hbound i)
  · intro i
    exact (hw i).restrict hV (subset_univ V)

end Poincare.Analysis.Elliptic
