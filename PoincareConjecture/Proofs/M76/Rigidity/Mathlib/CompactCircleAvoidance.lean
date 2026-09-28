import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc

set_option autoImplicit false

open Set

namespace AddCircle

theorem exists_closed_phase_arcs_disjoint (p : ℝ) [Fact (0 < p)]
    {K : Set (AddCircle p)} (hK : IsCompact K) {a b r : ℝ}
    (ha : (a : AddCircle p) ∉ K) (hb : (b : AddCircle p) ∉ K)
    (hr : 0 < r) :
    ∃ rho : ℝ, 0 < rho ∧ rho < r ∧
      Disjoint K (closedIntervalArc p (a - rho) (a + rho)) ∧
      Disjoint K (closedIntervalArc p (b - rho) (b + rho)) := by
  let U : Set ℝ :=
    (fun t : ℝ => ((a + t : ℝ) : AddCircle p)) ⁻¹' Kᶜ ∩
      (fun t : ℝ => ((b + t : ℝ) : AddCircle p)) ⁻¹' Kᶜ
  have hU : IsOpen U :=
    (hK.isClosed.isOpen_compl.preimage
      ((AddCircle.continuous_mk' p).comp (continuous_const.add continuous_id))).inter
      (hK.isClosed.isOpen_compl.preimage
        ((AddCircle.continuous_mk' p).comp (continuous_const.add continuous_id)))
  have hzero : (0 : ℝ) ∈ U := by
    change ((a + 0 : ℝ) : AddCircle p) ∉ K ∧ ((b + 0 : ℝ) : AddCircle p) ∉ K
    exact ⟨by simpa only [add_zero] using ha, by simpa only [add_zero] using hb⟩
  obtain ⟨l, u, hlu, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hzero)
  have hmin : 0 < min r (min (-l) u) :=
    lt_min hr (lt_min (neg_pos.mpr hlu.1) hlu.2)
  obtain ⟨rho, hrho, hsmall⟩ := exists_between hmin
  have hrr : rho < r := hsmall.trans_le (min_le_left _ _)
  have hrl : rho < -l := hsmall.trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hru : rho < u := hsmall.trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨rho, hrho, hrr, disjoint_left.mpr ?_, disjoint_left.mpr ?_⟩
  · rintro y hy ⟨z, hz, rfl⟩
    have hzU : z - a ∈ Ioo l u := by constructor <;> linarith [hz.1, hz.2]
    have hnot : ((a + (z - a) : ℝ) : AddCircle p) ∉ K := (hsub hzU).1
    apply hnot
    simpa only [show a + (z - a) = z by ring] using hy
  · rintro y hy ⟨z, hz, rfl⟩
    have hzU : z - b ∈ Ioo l u := by constructor <;> linarith [hz.1, hz.2]
    have hnot : ((b + (z - b) : ℝ) : AddCircle p) ∉ K := (hsub hzU).2
    apply hnot
    simpa only [show b + (z - b) = z by ring] using hy

end AddCircle
