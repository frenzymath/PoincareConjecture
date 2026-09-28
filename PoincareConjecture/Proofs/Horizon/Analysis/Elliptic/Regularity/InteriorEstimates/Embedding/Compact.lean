import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Embedding.Ball
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.ProfileCalculus
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.L2

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal ContDiff

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem derivativeProfile_ne_top_on_precompact {V : Set E}
    (hVc : IsCompact (closure V)) (r : ℕ) {u : E → ℝ} (hu : ContDiff ℝ ∞ u) :
    derivativeProfile 2 V r u ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro j hj
  have hm : MemLp (fun x => ‖iteratedFDeriv ℝ j u x‖) 2 (volume.restrict V) :=
    (continuous_memLp_on_compact
      (hu.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm hVc).mono_measure
        (Measure.restrict_mono subset_closure le_rfl)
  exact hm.eLpNorm_ne_top

theorem smooth_jet_le_l2_derivativeProfile_on_compact
    {K V : Set E} (hK : IsCompact K) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hKV : K ⊆ V) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : E → ℝ}, ContDiff ℝ ∞ u → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m u x‖ ≤ C * (derivativeProfile 2 V (m + 1 + d) u).toReal := by
  classical
  have hballs : ∀ x : K, ∃ R : ℝ, 0 < R ∧ ball (x : E) R ⊆ V := by
    intro x
    exact Metric.isOpen_iff.mp hV x (hKV x.property)
  choose R hR hRV using hballs
  choose A hA hbound using fun x : K =>
    smooth_jet_le_l2_derivativeProfile (d := d) (x₀ := (x : E)) (hR x) m
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : E) (R x / 2))
    (fun _ => isOpen_ball) (fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (half_pos (hR ⟨x, hx⟩))⟩)
  have hsnonneg : 0 ≤ ∑ x ∈ s, A x := Finset.sum_nonneg (fun x _ => hA x)
  refine ⟨1 + ∑ x ∈ s, A x, add_pos_of_pos_of_nonneg zero_lt_one hsnonneg, ?_⟩
  intro u hu x hx
  obtain ⟨y, hys, hxy⟩ := mem_iUnion₂.mp (hs hx)
  have hprofile : (derivativeProfile 2 (ball (y : E) (R y)) (m + 1 + d) u).toReal ≤
      (derivativeProfile 2 V (m + 1 + d) u).toReal :=
    ENNReal.toReal_mono (derivativeProfile_ne_top_on_precompact hVc _ hu)
      (derivativeProfile_mono_set (hRV y) 2 _ u)
  apply (hbound y hu x hxy).trans
  apply mul_le_mul
  · exact (Finset.single_le_sum (fun z hz => hA z) hys).trans (le_add_of_nonneg_left zero_le_one)
  · exact hprofile
  · exact ENNReal.toReal_nonneg
  · exact add_nonneg zero_le_one hsnonneg

end Poincare.Analysis.Elliptic.InteriorEstimates
