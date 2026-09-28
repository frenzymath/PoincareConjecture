import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc
import Mathlib.Tactic.Linarith









set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem exists_disjoint_inward_phase_collar_radius
    {E X : Type*} (p : ℝ) [Fact (0 < p)]
    (q : X → AddCircle p) (K : Bool → Set E) (c : Bool → E × ℝ → X)
    {rho a b : ℝ} (hrho : 0 < rho) (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hleft : ∀ z ∈ K false ×ˢ Icc (-rho) rho, q (c false z) = ((a + z.2 : ℝ) : AddCircle p))
    (hright : ∀ z ∈ K true ×ˢ Icc (-rho) rho, q (c true z) = ((b - z.2 : ℝ) : AddCircle p)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ rho ∧ r < a ∧ 2 * r < b - a ∧ r < p - b ∧
      (∀ side : Bool, K side ×ˢ Icc (-r) r ⊆ K side ×ˢ Icc (-rho) rho) ∧
      Disjoint (c false '' (K false ×ˢ Icc (-r) r)) (c true '' (K true ×ˢ Icc (-r) r)) ∧
      ∀ side : Bool, ∀ z ∈ K side ×ˢ Icc (-r) r,
        c side z ∈ q ⁻¹' AddCircle.closedIntervalArc p a b ↔ 0 ≤ z.2 := by
  let r := min rho (min (a / 3) (min ((b - a) / 3) ((p - b) / 3)))
  have hr : 0 < r := lt_min hrho (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hrrho : r ≤ rho := min_le_left _ _
  have hra : r ≤ a / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hrgap : r ≤ (b - a) / 3 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrp : r ≤ (p - b) / 3 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsub (side : Bool) : K side ×ˢ Icc (-r) r ⊆ K side ×ˢ Icc (-rho) rho := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hleftI (t : ℝ) (ht : t ∈ Icc (-r) r) : a + t ∈ Ico (0 : ℝ) (0 + p) := by
    constructor <;> linarith [ht.1, ht.2]
  have hrightI (t : ℝ) (ht : t ∈ Icc (-r) r) : b - t ∈ Ico (0 : ℝ) (0 + p) := by
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨r, hr, hrrho, by linarith, by linarith, by linarith, hsub, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨z, hz, hzx⟩ := hx
    obtain ⟨w, hw, hwx⟩ := hy
    have heq : ((a + z.2 : ℝ) : AddCircle p) = ((b - w.2 : ℝ) : AddCircle p) := by
      rw [← hleft z (hsub false hz), ← hright w (hsub true hw), hzx, hwx]
    have hreal := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (hleftI z.2 hz.2) (hrightI w.2 hw.2)).mp heq
    linarith [hz.2.2, hw.2.2]
  · intro side z hz
    cases side with
    | false =>
      change q (c false z) ∈ AddCircle.closedIntervalArc p a b ↔ _
      rw [hleft z (hsub false hz), AddCircle.coe_mem_closedIntervalArc_iff p ha.le hb
        (by simpa only [zero_add] using hleftI z.2 hz.2)]
      constructor
      · intro h
        linarith [h.1]
      · intro h
        exact ⟨by linarith, by linarith [hz.2.2]⟩
    | true =>
      change q (c true z) ∈ AddCircle.closedIntervalArc p a b ↔ _
      rw [hright z (hsub true hz), AddCircle.coe_mem_closedIntervalArc_iff p ha.le hb
        (by simpa only [zero_add] using hrightI z.2 hz.2)]
      constructor
      · intro h
        linarith [h.2]
      · intro h
        exact ⟨by linarith [hz.2.2], by linarith⟩

end PoincareConjecture.M76
