import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusFiber











set_option autoImplicit false

open Set

namespace PLAnnularStrip





theorem stripRotation_circle_coordinate {L d : ℝ} (hwidth : 4 * d < L)
    {p q : ℝ × ℝ} (hp : p ∈ rectangle L d) (hq : q ∈ rectangle L d)
    (i j : Fin 4) (he : stripRotation L i (stripMap L p) =
      stripRotation L j (stripMap L q)) :
    ((p.1 + (i.val : ℝ) * L : ℝ) : AddCircle (4 * L)) =
      ((q.1 + (j.val : ℝ) * L : ℝ) : AddCircle (4 * L)) := by
  have ht := stripRotation_transverse_injective hwidth hp hq i j he
  have htp : 4 * |p.2| < L :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr hp.2) (by norm_num)) hwidth
  have hp₀ := (coordinate_eq_initial_iff htp hp.1).mp
  have hpL := (coordinate_eq_terminal_iff htp hp.1).mp
  have hq₀ := (coordinate_eq_initial_iff htp hq.1).mp
  have hqL := (coordinate_eq_terminal_iff htp hq.1).mp
  have hsame : coordinate L p.1 p.2 = coordinate L q.1 p.2 → p.1 = q.1 :=
    (strictMonoOn_coordinate htp).injOn hp.1 hq.1
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  fin_cases i <;> fin_cases j <;> dsimp [stripRotation, stripMap] at h₁ h₂ <;>
    rw [← ht] at h₁ h₂
  · congr 1
    simpa using hsame h₁
  · have hp' := hpL h₁
    have hq' := hq₀ h₂.symm
    congr 1
    norm_num [hp', hq']
  · exfalso
    linarith [le_abs_self p.2, abs_nonneg p.2]
  · have hp' := hp₀ h₁
    have hq' := hqL (by linarith)
    simpa [hp', hq', show L + 3 * L = 4 * L by ring, AddCircle.coe_zero] using
      (AddCircle.coe_period (4 * L)).symm
  · have hp' := hp₀ h₂
    have hq' := hqL h₁.symm
    congr 1
    norm_num [hp', hq']
  · congr 1
    have h := hsame h₂
    norm_num [h]
  · have hp' := hpL h₂
    have hq' := hq₀ (by linarith)
    congr 1
    norm_num [hp', hq']; ring
  · exfalso
    linarith [le_abs_self p.2, abs_nonneg p.2]
  · exfalso
    linarith [le_abs_self p.2, abs_nonneg p.2]
  · have hp' := hp₀ (by linarith)
    have hq' := hqL h₂.symm
    congr 1
    norm_num [hp', hq']; ring
  · congr 1
    have h := hsame (by linarith)
    norm_num [h]
  · have hp' := hpL (by linarith)
    have hq' := hq₀ (by linarith)
    congr 1
    norm_num [hp', hq']; ring
  · have hp' := hpL (by linarith)
    have hq' := hq₀ h₁.symm
    simp [hp', hq', show L + 3 * L = 4 * L by ring]
  · exfalso
    linarith [le_abs_self p.2, abs_nonneg p.2]
  · have hp' := hp₀ (by linarith)
    have hq' := hqL (by linarith)
    congr 1
    norm_num [hp', hq']; ring
  · congr 1
    have h := hsame (by linarith)
    norm_num [h]





theorem injective_annulusMap {L d : ℝ} (hL : 0 < L) (hwidth : 4 * d < L) :
    Function.Injective (fun p : AddCircle (4 * L) × Icc (-d) d =>
      annulusMap L hL (p.1, p.2)) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  have hrep (z : AddCircle (4 * L)) :
      ∃ s ∈ Icc (0 : ℝ) (4 * L), (s : AddCircle (4 * L)) = z := by
    let s := AddCircle.equivIco (4 * L) 0 z
    exact ⟨s, ⟨s.property.1, by simpa only [zero_add] using s.property.2.le⟩,
      AddCircle.coe_equivIco⟩
  intro p q he
  obtain ⟨s, hs, hsp⟩ := hrep p.1
  obtain ⟨t, ht, htq⟩ := hrep q.1
  have htp : 4 * |(p.2 : ℝ)| < L :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr p.2.property) (by norm_num)) hwidth
  have htq' : 4 * |(q.2 : ℝ)| < L :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr q.2.property) (by norm_num)) hwidth
  have hraw : wrappedStripMap L (s, p.2) = wrappedStripMap L (t, q.2) := by
    rw [← annulusMap_coe hL htp hs, ← annulusMap_coe hL htq' ht, hsp, htq]
    exact he
  obtain ⟨i, a, ha, hsval⟩ := exists_period_block hs
  obtain ⟨j, b, hb, htval⟩ := exists_period_block ht
  have hp' : (a, (p.2 : ℝ)) ∈ rectangle L d := ⟨ha, p.2.property⟩
  have hq' : (b, (q.2 : ℝ)) ∈ rectangle L d := ⟨hb, q.2.property⟩
  have hrot : stripRotation L i (stripMap L (a, p.2)) =
      stripRotation L j (stripMap L (b, q.2)) := by
    rw [← wrappedStripMap_block htp ha i, ← wrappedStripMap_block htq' hb j,
      ← hsval, ← htval]
    exact hraw
  have hcircle := stripRotation_circle_coordinate hwidth hp' hq' i j hrot
  change ((a + (i.val : ℝ) * L : ℝ) : AddCircle (4 * L)) =
    ((b + (j.val : ℝ) * L : ℝ) : AddCircle (4 * L)) at hcircle
  rw [← hsval, ← htval, hsp, htq] at hcircle
  exact Prod.ext hcircle (Subtype.ext
    (stripRotation_transverse_injective hwidth hp' hq' i j hrot))

end PLAnnularStrip
