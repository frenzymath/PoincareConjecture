import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnularStripCharts
import PoincareConjecture.Proofs.M76.Mathlib.AddCircleParametricLift

set_option autoImplicit false

open Set

namespace PLAnnularStrip

noncomputable def wrappedStripMap (L : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if p.1 ≤ L then (coordinate L p.1 p.2, p.2)
  else if p.1 ≤ 2 * L then (L - p.2, coordinate L (p.1 - L) p.2)
  else if p.1 ≤ 3 * L then (L - coordinate L (p.1 - 2 * L) p.2, L - p.2)
  else (p.2, L - coordinate L (p.1 - 3 * L) p.2)

theorem continuous_wrappedStripMap {L d : ℝ} (hd : 0 ≤ d) (hwidth : 4 * d < L) :
    Continuous (fun p : ℝ × Icc (-d) d => wrappedStripMap L (p.1, p.2)) := by
  have hL : 0 < L := by linarith
  have ht (p : ℝ × Icc (-d) d) : 4 * |(p.2 : ℝ)| < L :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr p.2.property) (by norm_num)) hwidth
  let f₀ : ℝ × Icc (-d) d → ℝ × ℝ := fun p => (coordinate L p.1 p.2, p.2)
  let f₁ : ℝ × Icc (-d) d → ℝ × ℝ := fun p => (L - p.2, coordinate L (p.1 - L) p.2)
  let f₂ : ℝ × Icc (-d) d → ℝ × ℝ :=
    fun p => (L - coordinate L (p.1 - 2 * L) p.2, L - p.2)
  let f₃ : ℝ × Icc (-d) d → ℝ × ℝ :=
    fun p => (p.2, L - coordinate L (p.1 - 3 * L) p.2)
  have hc₀ : Continuous f₀ := by unfold f₀ coordinate cornerCorrection; fun_prop
  have hc₁ : Continuous f₁ := by unfold f₁ coordinate cornerCorrection; fun_prop
  have hc₂ : Continuous f₂ := by unfold f₂ coordinate cornerCorrection; fun_prop
  have hc₃ : Continuous f₃ := by unfold f₃ coordinate cornerCorrection; fun_prop
  have hc₂₃ : Continuous (fun p : ℝ × Icc (-d) d => if p.1 ≤ 3 * L then f₂ p else f₃ p) := by
    apply hc₂.if_le hc₃ continuous_fst continuous_const
    intro p hp
    have h₁ : p.1 - 2 * L = L := by linarith
    have h₂ : p.1 - 3 * L = 0 := by linarith
    simp only [f₂, f₃, h₁, h₂, (coordinate_endpoints (ht p)).1,
      (coordinate_endpoints (ht p)).2, sub_sub_cancel]
  have hc₁₂₃ : Continuous (fun p : ℝ × Icc (-d) d => if p.1 ≤ 2 * L then f₁ p
      else if p.1 ≤ 3 * L then f₂ p else f₃ p) := by
    apply hc₁.if_le hc₂₃ continuous_fst continuous_const
    intro p hp
    rw [if_pos (show p.1 ≤ 3 * L by linarith)]
    have h₁ : p.1 - L = L := by linarith
    have h₂ : p.1 - 2 * L = 0 := by linarith
    simp only [f₁, f₂, h₁, h₂, (coordinate_endpoints (ht p)).1,
      (coordinate_endpoints (ht p)).2]
  apply hc₀.if_le hc₁₂₃ continuous_fst continuous_const
  intro p hp
  rw [if_pos (show p.1 ≤ 2 * L by linarith)]
  simp only [f₀, f₁, hp, sub_self, (coordinate_endpoints (ht p)).1,
    (coordinate_endpoints (ht p)).2]

theorem wrappedStripMap_endpoints {L t : ℝ} (ht : 4 * |t| < L) :
    wrappedStripMap L (0, t) = wrappedStripMap L (4 * L, t) := by
  have hL : 0 < L := by linarith [abs_nonneg t]
  have h₀ : (0 : ℝ) ≤ L := hL.le
  have h₁ : ¬ 4 * L ≤ L := by linarith
  have h₂ : ¬ 4 * L ≤ 2 * L := by linarith
  have h₃ : ¬ 4 * L ≤ 3 * L := by linarith
  have hsub : 4 * L - 3 * L = L := by ring
  simp only [wrappedStripMap, h₀, h₁, h₂, h₃, if_true, if_false,
    hsub, (coordinate_endpoints ht).1, (coordinate_endpoints ht).2, sub_sub_cancel]

noncomputable def annulusMap (L : ℝ) (hL : 0 < L)
    (p : AddCircle (4 * L) × ℝ) : ℝ × ℝ :=
  letI : Fact (0 < 4 * L) := ⟨by linarith⟩
  AddCircle.liftIco (4 * L) 0 (fun s => wrappedStripMap L (s, p.2)) p.1

theorem annulusMap_coe {L t s : ℝ} (hL : 0 < L) (ht : 4 * |t| < L)
    (hs : s ∈ Icc 0 (4 * L)) :
    annulusMap L hL ((s : AddCircle (4 * L)), t) = wrappedStripMap L (s, t) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  exact AddCircle.liftIco_zero_coe_apply_Icc (f := fun u => wrappedStripMap L (u, t))
    (wrappedStripMap_endpoints ht) hs

theorem continuous_annulusMap {L d : ℝ} (hd : 0 ≤ d) (hwidth : 4 * d < L) :
    Continuous (fun p : AddCircle (4 * L) × Icc (-d) d =>
      annulusMap L (by linarith) (p.1, p.2)) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  apply AddCircle.continuous_parametric_liftIco (fun p : ℝ × Icc (-d) d =>
    wrappedStripMap L (p.1, p.2))
  · exact (continuous_wrappedStripMap hd hwidth).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  · intro t
    exact wrappedStripMap_endpoints
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr t.property) (by norm_num)) hwidth)

theorem annulusMap_middle {L s t : ℝ} (hL : 0 < L) (ht : 4 * |t| < L)
    (hleft : 2 * |t| ≤ s) (hright : 2 * |t| ≤ L - s) :
    annulusMap L hL ((s : AddCircle (4 * L)), t) = (s, t) := by
  have hs : s ∈ Icc 0 L := by constructor <;> linarith [abs_nonneg t]
  rw [annulusMap_coe hL ht ⟨hs.1, by linarith [hs.2]⟩]
  simp only [wrappedStripMap, hs.2, if_true, coordinate_eq_self hleft hright]

end PLAnnularStrip
