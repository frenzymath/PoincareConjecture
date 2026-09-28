import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMetricDifferences
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.DifferentiatedEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal
open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean

namespace PoincareConjecture

theorem m64TangentialHessian_of_integral_diffQuot_bound
    {n : ℕ} {O : Set LoopPlane} (hO : IsOpen O) (hc : IsCompact (closure O))
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    (hV : ∀ i, MemLp (V i) 2 volume)
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) O)
    {h0 : ℝ} (hh0 : 0 < h0) (C : Fin n → ℝ)
    (hbound : ∀ j h, h ≠ 0 → |h| ≤ h0 →
      (∫ p in O, ∑ i : Fin 2, diffQuot 0 h (fun q => V i q j) p ^ 2) ≤ C j) :
    ∃ Q : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n),
      (∀ i, MemLp (Q i) 2 (volume.restrict O)) ∧
      (∀ i j, HasWeakPartialDeriv 0 (fun p => Q i p j) (fun p => V i p j) O) ∧
      ∀ j, MemW1p 2 (fun p => V 0 p j) O := by
  have hnorm (j : Fin n) (i : Fin 2) (h : ℝ) (hh : 0 < |h|) (hle : |h| ≤ h0) :
      eLpNorm (diffQuot 0 h (fun p => V i p j)) 2 (volume.restrict O) ≤
        ENNReal.ofReal (Real.sqrt (C j)) := by
    have hq (k : Fin 2) :=
      (M60.suWeakMap_diffQuot_memLp ((hV k).eval_piLp j) 0 h).restrict O
    have hsquare (k : Fin 2) := (hq k).integrable_sq
    apply eLpNorm_two_le_sqrt_of_integral_sq_le (hq i)
    apply le_trans ?_ (hbound j h (abs_pos.mp hh) hle)
    apply integral_mono (hsquare i) (integrable_finsetSum _ (fun k _ => hsquare k))
    intro p
    exact Finset.single_le_sum
      (f := fun k : Fin 2 => diffQuot 0 h (fun q => V k q j) p ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  choose Q hQ hQw _hQnorm using fun (j : Fin n) (i : Fin 2) =>
    hasWeakPartialDeriv_of_diffQuot_uniform_bound_loc isOpen_univ hO hc hh0
      (subset_univ _) (by simpa only [Measure.restrict_univ] using (hV i).eval_piLp j)
      0 (Real.sqrt_nonneg (C j)) (hnorm j i)
  refine ⟨fun i p => WithLp.toLp 2 (fun j => Q j i p), ?_, ?_, ?_⟩
  · intro i
    exact MemLp.of_eval_piLp (fun j => hQ j i)
  · intro i j
    exact hQw j i
  · intro j
    refine ⟨((hV 0).eval_piLp j).restrict O, fun i => ⟨Q j i, hQ j i, ?_⟩⟩
    fin_cases i
    · exact hQw j 0
    · exact BoundaryTangential.weakPartial_commute 1 0 (hw 1 j) (hw 0 j) (hQw j 1)

end PoincareConjecture
