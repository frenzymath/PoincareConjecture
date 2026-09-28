import PoincareConjecture.Definitions.M28BoundedDistance
import PoincareConjecture.Proofs.M28.Mathlib.LogPinching









set_option autoImplicit false

universe u

namespace PoincareConjecture

open Filter
open scoped Topology



theorem generalizedHamiltonIveyPinched.weak
    {F : GeneralizedRicciFlowData.{u}} (h : generalizedHamiltonIveyPinched F) :
    generalizedWeakHamiltonIveyPinched F := by
  intro t ht x
  obtain ⟨_, ht0, hscalar, hpinch⟩ := h t ht
  constructor
  · have hden : 0 < 1 + 4 * t := by positivity
    have hlower : (-6 : ℝ) ≤ -6 / (1 + 4 * t) :=
      (le_div_iff₀ hden).mpr (by nlinarith)
    exact hlower.trans (hscalar x)
  · intro hv
    have hlog : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
    have hmul := mul_nonneg (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) hv)) hlog
    have hfull := hpinch x hv
    nlinarith




theorem generalizedWeakHamiltonIveyPinched.negative_part_lt
    {F : GeneralizedRicciFlowData.{u}}
    (h : generalizedWeakHamiltonIveyPinched F)
    {eta B Q t : ℝ} (heta : 0 < eta) (hB : 0 ≤ B)
    (hQ : Real.exp (3 + (B + 1) / (2 * eta)) / eta ≤ Q)
    (ht : t ∈ F.interval) (x : (F.slice t).carrier)
    (hscalar : F.scalar ⟨t, x⟩ ≤ B * Q) :
    (F.connection t).negativeCurvaturePart x < eta * Q := by
  exact Real.lt_mul_of_log_pinching heta hB hQ hscalar (h t ht x).2





theorem GeneralizedBlowupSequence.negative_part_tendsto_zero
    (S : GeneralizedBlowupSequence.{u})
    (hpinch : ∀ k, generalizedWeakHamiltonIveyPinched (S.flow k))
    (p : ∀ k, (S.flow k).point) {B : ℝ} (hB : 0 ≤ B)
    (hscalar : ∀ᶠ k in atTop, (S.flow k).scalar (p k) ≤ B * S.scale k) :
    Tendsto (fun k ↦ ((S.flow k).connection (p k).1).negativeCurvaturePart (p k).2 /
      S.scale k) atTop (𝓝 0) := by
  apply Real.tendsto_zero_of_log_pinching hB S.scalar_diverges
  · exact Filter.Eventually.of_forall fun k ↦ le_max_right _ _
  · exact hscalar
  · apply Filter.Eventually.of_forall
    intro k
    have ht : (p k).1 ∈ (S.flow k).interval :=
      ((S.flow k).slice_nonempty_iff _).mp ⟨(p k).2⟩
    exact (hpinch k _ ht (p k).2).2

end PoincareConjecture
