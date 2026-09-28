import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusImage

set_option autoImplicit false

open Set

namespace PLAnnularStrip

theorem coordinate_mem_Icc {L s t : ℝ}
    (ht : 4 * |t| < L) (hs : s ∈ Icc 0 L) :
    coordinate L s t ∈ Icc t (L - t) := by
  rw [← coordinate_image_Icc ht]
  exact mem_image_of_mem _ hs

theorem stripRotation_transverse_injective {L d : ℝ} (hwidth : 4 * d < L)
    {p q : ℝ × ℝ} (hp : p ∈ rectangle L d) (hq : q ∈ rectangle L d)
    (i j : Fin 4) (he : stripRotation L i (stripMap L p) =
      stripRotation L j (stripMap L q)) : p.2 = q.2 := by
  have htp : 4 * |p.2| < L :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr hp.2) (by norm_num)) hwidth
  have htq : 4 * |q.2| < L :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr hq.2) (by norm_num)) hwidth
  have hu := coordinate_mem_Icc htp hp.1
  have hv := coordinate_mem_Icc htq hq.1
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  fin_cases i <;> fin_cases j <;> dsimp [stripRotation, stripMap] at h₁ h₂ <;>
    linarith [hu.1, hu.2, hv.1, hv.2, hp.2.1, hp.2.2, hq.2.1, hq.2.2]

theorem coordinate_eq_initial_iff {L s t : ℝ}
    (ht : 4 * |t| < L) (hs : s ∈ Icc 0 L) :
    coordinate L s t = t ↔ s = 0 := by
  have hL : 0 ≤ L := by linarith [abs_nonneg t]
  constructor
  · intro h
    apply (strictMonoOn_coordinate ht).injOn hs ⟨le_rfl, hL⟩
    change coordinate L s t = coordinate L 0 t
    rw [(coordinate_endpoints ht).1]
    exact h
  · rintro rfl
    exact (coordinate_endpoints ht).1

theorem coordinate_eq_terminal_iff {L s t : ℝ}
    (ht : 4 * |t| < L) (hs : s ∈ Icc 0 L) :
    coordinate L s t = L - t ↔ s = L := by
  have hL : 0 ≤ L := by linarith [abs_nonneg t]
  constructor
  · intro h
    apply (strictMonoOn_coordinate ht).injOn hs ⟨hL, le_rfl⟩
    change coordinate L s t = coordinate L L t
    rw [(coordinate_endpoints ht).2]
    exact h
  · rintro rfl
    exact (coordinate_endpoints ht).2

end PLAnnularStrip
