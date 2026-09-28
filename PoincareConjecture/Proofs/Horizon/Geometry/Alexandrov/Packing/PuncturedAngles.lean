import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.Net
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Comparison.NearVertex
import Mathlib.Data.Finset.Lattice.Fold










noncomputable section
set_option autoImplicit false

namespace Poincare.Alexandrov

theorem ComparisonAnglePackingBound.exists_pos_near_opposite
    {X : Type*} [MetricSpace X] {α : ℝ} {N : ℕ}
    (h : ComparisonAnglePackingBound X α N)
    (hα : 0 < α) (hαpi : α < Real.pi / 2) (p : X) :
    ∃ r : ℝ, 0 < r ∧ ∀ y : X, 0 < dist p y → dist p y < r →
      ∃ q : X, q ≠ y ∧ Real.pi - 2 * α <
        comparisonAngle (dist y p) (dist y q) (dist p q) := by
  classical
  obtain ⟨s, _, hp, hcover⟩ := h.exists_angle_net hα.le p
  have hqpos (q : s) : 0 < dist p q :=
    dist_pos.mpr (fun heq => hp (heq.symm ▸ q.property))
  have hlocal (q : s) := exists_pos_comparisonAngle_near_vertex (hqpos q) hα hαpi
  choose ε hε hεangle using hlocal
  let ρ : s → ℝ := fun q => min (ε q) (dist p q / 2)
  have hρ (q : s) : 0 < ρ q := lt_min (hε q) (half_pos (hqpos q))
  by_cases hs : s.Nonempty
  · let : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
    let r := Finset.univ.inf' Finset.univ_nonempty ρ
    have hr : 0 < r := by simpa only [r, Finset.lt_inf'_iff] using (fun q _ => hρ q)
    refine ⟨r, hr, ?_⟩
    intro y hpy hyr
    obtain ⟨q, hqs, hangle⟩ := hcover y (dist_pos.mp hpy).symm
    let q' : s := ⟨q, hqs⟩
    have hle : r ≤ ρ q' := Finset.inf'_le _ (Finset.mem_univ q')
    have hye : dist p y < ε q' := hyr.trans_le (hle.trans (min_le_left _ _))
    have hyq : dist p y < dist p q / 2 := hyr.trans_le (hle.trans (min_le_right _ _))
    have hqy : q ≠ y := by
      intro heq
      subst q
      linarith
    refine ⟨q, hqy, ?_⟩
    have hlow : |dist p y - dist p q| ≤ dist y q := by
      simpa only [dist_comm y p, dist_comm q p] using abs_dist_sub_le y q p
    have hupp : dist y q ≤ dist p y + dist p q := by
      simpa only [dist_comm y p] using dist_triangle y p q
    simpa only [dist_comm y p] using
      hεangle q' (dist p y) (dist y q) hpy hye hlow hupp hangle
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y hpy _
    obtain ⟨q, hq, _⟩ := hcover y (dist_pos.mp hpy).symm
    exact (hs ⟨q, hq⟩).elim

end Poincare.Alexandrov
