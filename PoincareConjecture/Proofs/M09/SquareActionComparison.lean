import PoincareConjecture.Proofs.M09.BrokenActionComparison
import PoincareConjecture.Proofs.M09.ActionCongruence
import PoincareConjecture.Definitions.Ch06.ReducedLength

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem backwardLLength_smoothSquare_eq_integral {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (α : ℝ → M) (D : Set ℝ) (hD : IsOpen D)
    (hI : Set.Icc 0 (Real.sqrt b) ⊆ D) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α D) :
    backwardLLength F T 0 b (fun t ↦ α (Real.sqrt t)) =
      ∫ s in 0..Real.sqrt b, squareCurveActionDensity F T α s := by
  exact backwardLLength_comp_sqrt_eq F T b hb α (fun s hs ↦
    (hα.contMDiffAt (hD.mem_nhds (hI (Set.Ioo_subset_Icc_self hs)))).mdifferentiableAt (by simp))

theorem minimizing_action_le_broken_action {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax : ℝ) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (c b : ℝ) (hc : 0 < c) (hcb : c < b) (hmax : b < τmax)
    (P : BackwardTimePath F T 0 b) (hmin : IsMinimizingBackwardLPath F T 0 b P)
    (α β : ℝ → M) (D : Set ℝ) (hD : IsOpen D) (hI : Set.Icc 0 (Real.sqrt b) ⊆ D)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α D)
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β D)
    (heq : α (Real.sqrt c) = β (Real.sqrt c))
    (hleft : α 0 = P.curve 0) (hright : β (Real.sqrt b) = P.curve b) :
    backwardLLength F T 0 b P.curve ≤
      backwardLLength F T 0 c (fun t ↦ α (Real.sqrt t)) +
        backwardLLength F T 0 b (fun t ↦ β (Real.sqrt t)) -
          backwardLLength F T 0 c (fun t ↦ β (Real.sqrt t)) := by
  have hb : 0 < b := hc.trans hcb
  have hIc : Set.Icc 0 (Real.sqrt c) ⊆ D :=
    (Set.Icc_subset_Icc le_rfl (Real.sqrt_le_sqrt hcb.le)).trans hI
  have hcomp := minimizing_action_le_broken_square_action F hM04 T τmax hτmax hwindow
    b hb hmax P hmin α β D hD hI hα hβ (Real.sqrt c)
    ⟨Real.sqrt_pos.mpr hc, Real.sqrt_lt_sqrt hc.le hcb⟩ heq hleft hright
  have hi := squareCurveActionDensity_intervalIntegrable F hM04 T τmax hτmax hwindow
    b hb hmax β D hD hI hβ
  have hi0c : IntervalIntegrable (squareCurveActionDensity F T β) MeasureTheory.volume 0 (Real.sqrt c) :=
    hi.mono_set (by
      rw [Set.uIcc_of_le (Real.sqrt_nonneg c), Set.uIcc_of_le (Real.sqrt_nonneg b)]
      exact Set.Icc_subset_Icc le_rfl (Real.sqrt_le_sqrt hcb.le))
  have hicb : IntervalIntegrable (squareCurveActionDensity F T β) MeasureTheory.volume
      (Real.sqrt c) (Real.sqrt b) := hi.mono_set (by
    rw [Set.uIcc_of_le (Real.sqrt_le_sqrt hcb.le), Set.uIcc_of_le (Real.sqrt_nonneg b)]
    exact Set.Icc_subset_Icc (Real.sqrt_nonneg c) le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi0c hicb
  rw [backwardLLength_smoothSquare_eq_integral F T c hc α D hD hIc hα,
    backwardLLength_smoothSquare_eq_integral F T b hb β D hD hI hβ,
    backwardLLength_smoothSquare_eq_integral F T c hc β D hD hIc hβ]
  linarith

theorem lExponentialFamily_action_comp_sqrt_eq_of_eqOn {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax : ℝ} {p : M} (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (α : ℝ → M) (heq : Set.EqOn α (A.squareFamily Z) (Set.Icc 0 (Real.sqrt b))) :
    backwardLLength F T 0 b (fun t ↦ α (Real.sqrt t)) = A.action Z b := by
  apply backwardLLength_congr_Ioo F T 0 b hb.le
  intro t ht
  have hs : Real.sqrt t ∈ Set.Icc 0 (Real.sqrt b) :=
    ⟨Real.sqrt_nonneg t, Real.sqrt_le_sqrt ht.2.le⟩
  apply (heq hs).trans
  have hsq := A.square_agrees Z (Real.sqrt t)
    ⟨hs.1, hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  simpa only [Real.sq_sqrt ht.1.le] using hsq

end PoincareConjecture.Proofs.M09
