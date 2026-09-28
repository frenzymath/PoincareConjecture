import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.Mathlib.ShiftedCircleClosedArc



set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem compl_interior_shifted_phase_arc
    (p : ℝ) [Fact (0 < p)] {c a b : ℝ}
    (ha : c < a) (hab : a < b) (hb : b < c + p) :
    (interior (AddCircle.closedIntervalArc p a b))ᶜ = AddCircle.closedIntervalArc p b (a + p) := by
  rw [AddCircle.interior_closedIntervalArc_shifted p ha hb]
  ext z
  constructor
  · intro hz
    let t := AddCircle.equivIco p a z
    have ht : (t : ℝ) ∈ Ico a (a + p) := t.property
    have htz : ((t : ℝ) : AddCircle p) = z := AddCircle.coe_equivIco
    by_cases hbt : b ≤ (t : ℝ)
    · exact ⟨t, ⟨hbt, ht.2.le⟩, htz⟩
    · have hta : (t : ℝ) = a := by
        apply le_antisymm _ ht.1
        by_contra! hat
        exact hz ⟨t, ⟨hat, lt_of_not_ge hbt⟩, htz⟩
      exact ⟨a + p, ⟨by linarith, le_rfl⟩,
        (AddCircle.coe_add_period p a).trans (hta ▸ htz)⟩
  · rintro ⟨t, ht, rfl⟩ ⟨u, hu, hut⟩
    have htI : t ∈ Ioc a (a + p) := ⟨hab.trans_le ht.1, ht.2⟩
    have huI : u ∈ Ioc a (a + p) := ⟨hu.1, by linarith [hu.2]⟩
    have hEq : u = t := (AddCircle.coe_eq_coe_iff_of_mem_Ioc huI htI).mp hut
    linarith [hu.2, ht.1]

end PoincareConjecture.M76.HamiltonIntervalTorus
