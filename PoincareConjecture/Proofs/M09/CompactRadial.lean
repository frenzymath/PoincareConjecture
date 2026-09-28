import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.Proofs.M09

theorem isCompact_of_compact_approximation {X : Type*} [MetricSpace X]
    [CompleteSpace X] {S : Set X} (hS : IsClosed S)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ K : Set X, IsCompact K ∧
      ∀ y ∈ S, ∃ z ∈ K, dist y z < ε) : IsCompact S := by
  apply isCompact_iff_totallyBounded_isComplete.mpr
  refine ⟨Metric.totallyBounded_iff.mpr ?_, hS.isComplete⟩
  intro ε hε
  obtain ⟨K, hK, hnear⟩ := happrox (ε / 2) (half_pos hε)
  obtain ⟨C, hC, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded
    (ε / 2) (half_pos hε)
  refine ⟨C, hC, ?_⟩
  intro y hy
  obtain ⟨z, hz, hyz⟩ := hnear y hy
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp (hcover hz)
  apply Set.mem_iUnion₂.mpr ⟨w, hw, ?_⟩
  change dist y w < ε
  have hzw' : dist z w < ε / 2 := hzw
  have htri := dist_triangle y z w
  linarith

theorem properSpace_of_approximate_radial_projection {X : Type*} [MetricSpace X]
    [CompleteSpace X] [LocallyCompactSpace X]
    (hproject : ∀ (x : X) (R r ε : ℝ), 0 ≤ r → r ≤ R → 0 < ε →
      closedBall x R ⊆ thickening (R - r + ε) (closedBall x r)) : ProperSpace X := by
  have hincrease (x : X) (r : ℝ) (hr : 0 ≤ r)
      (hcompact : IsCompact (closedBall x r)) :
      ∃ R : ℝ, r < R ∧ IsCompact (closedBall x R) := by
    obtain ⟨δ, hδ, hthick⟩ := hcompact.exists_isCompact_cthickening
    refine ⟨r + δ / 2, by linarith, ?_⟩
    have hsub := hproject x (r + δ / 2) r (δ / 2) hr (by linarith) (half_pos hδ)
    rw [show r + δ / 2 - r + δ / 2 = δ by ring] at hsub
    exact hthick.of_isClosed_subset isClosed_closedBall
      (hsub.trans (thickening_subset_cthickening δ _))
  have hlimit (x : X) (R : ℝ) (hR : 0 ≤ R)
      (hbelow : ∀ r : ℝ, 0 ≤ r → r < R → IsCompact (closedBall x r)) :
      IsCompact (closedBall x R) := by
    by_cases hR0 : R = 0
    · subst R
      simpa using isCompact_singleton (x := x)
    have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    apply isCompact_of_compact_approximation isClosed_closedBall
    intro ε hε
    let r := max 0 (R - ε / 2)
    have hr : 0 ≤ r := le_max_left _ _
    have hrlt : r < R := max_lt hRpos (by linarith)
    refine ⟨closedBall x r, hbelow r hr hrlt, ?_⟩
    intro y hy
    obtain ⟨z, hz, hyz⟩ := Metric.mem_thickening_iff.mp
      (hproject x R r (ε / 2) hr hrlt.le (half_pos hε) hy)
    refine ⟨z, hz, hyz.trans_le ?_⟩
    have hgap : R - ε / 2 ≤ r := le_max_right _ _
    linarith
  apply ProperSpace.of_isCompact_closedBall_of_le 0
  intro x R0 _hR0
  by_contra hbad
  let A : Set ℝ := {r | 0 ≤ r ∧ IsCompact (closedBall x r)}
  have hzero : (0 : ℝ) ∈ A := ⟨le_rfl, by simpa using isCompact_singleton (x := x)⟩
  have hnonempty : A.Nonempty := ⟨0, hzero⟩
  have hbounded : BddAbove A := by
    refine ⟨R0, ?_⟩
    intro r hr
    by_contra hnot
    exact hbad (hr.2.of_isClosed_subset isClosed_closedBall
      (closedBall_subset_closedBall (le_of_lt (lt_of_not_ge hnot))))
  have hsup_nonneg : 0 ≤ sSup A := le_csSup hbounded hzero
  have hsup_compact : IsCompact (closedBall x (sSup A)) := by
    apply hlimit x (sSup A) hsup_nonneg
    intro r hr hrlt
    obtain ⟨s, hs, hrs⟩ := exists_lt_of_lt_csSup hnonempty hrlt
    exact hs.2.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hrs.le)
  obtain ⟨R, hR, hcompact⟩ := hincrease x (sSup A) hsup_nonneg hsup_compact
  have hmem : R ∈ A := ⟨hsup_nonneg.trans hR.le, hcompact⟩
  exact (not_le_of_gt hR) (le_csSup hbounded hmem)

end PoincareConjecture.Proofs.M09
