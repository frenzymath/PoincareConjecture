import PoincareConjecture.Proofs.M25.Topology3D.Plane.SmoothAbsolute









set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D



theorem exists_smooth_curve_transport_times
    {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∃ n : ℕ, 1 ≤ n ∧
      let h : ℝ := (b - a) / n
      0 < h ∧ 2 * h < ε ∧
      (∀ i : ℕ, i ≤ n → a + (i : ℝ) * h ∈ Icc a b) ∧
      ∃ β : ℕ → ℝ → ℝ,
        (∀ k, ContDiff ℝ ∞ (β k)) ∧
        (∀ z, β 0 z = a) ∧
        (∀ k, β k a = a) ∧
        (∀ z ∈ Icc a b, β (n + 1) z = z) ∧
        ∀ i : ℕ, i ≤ n → ∀ z ∈ Icc a b,
          β i z = β (i + 1) z ∨
          (|β i z - (a + (i : ℝ) * h)| < ε ∧
           |β (i + 1) z - (a + (i : ℝ) * h)| < ε) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 : ℝ) (2 * (b - a) / ε))
  have hnR : (0 : ℝ) < n := (zero_lt_one.trans_le (le_max_left _ _)).trans hn
  have hn0 : 0 < n := by exact_mod_cast hnR
  let h : ℝ := (b - a) / n
  have hh : 0 < h := div_pos (sub_pos.mpr hab) hnR
  have hnh : (n : ℝ) * h = b - a := mul_div_cancel₀ _ (ne_of_gt hnR)
  have hmesh : 2 * h < ε := by
    have hx := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hn)
    dsimp [h]
    rw [← mul_div_assoc, div_lt_iff₀ hnR]
    nlinarith
  have hpoints (i : ℕ) (hi : i ≤ n) : a + (i : ℝ) * h ∈ Icc a b := by
    have hiR : (i : ℝ) ≤ n := by exact_mod_cast hi
    have hlow := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hh.le
    have hupp := mul_le_mul_of_nonneg_right hiR hh.le
    constructor <;> linarith
  let δ : ℝ := h / 4
  have hδ : 0 < δ := div_pos hh (by norm_num)
  obtain ⟨ρ, hρ, _, _, htail, hbound, _⟩ := exists_smooth_absolute_rounding hδ
  let cap : ℝ → ℝ → ℝ := fun u z => (z + u - ρ (z - u)) / 2
  have hcap (u : ℝ) : ContDiff ℝ ∞ (cap u) :=
    ((contDiff_id.add contDiff_const).sub
      (hρ.comp (contDiff_id.sub contDiff_const))).div_const 2
  have hcapbounds (u z : ℝ) : min z u - δ / 2 ≤ cap u z ∧ cap u z ≤ min z u := by
    have hb := hbound (z - u)
    dsimp only [cap]
    by_cases hz : z ≤ u
    · rw [min_eq_left hz, abs_of_nonpos (sub_nonpos.mpr hz)] at *
      constructor <;> linarith
    · have huz := (lt_of_not_ge hz).le
      rw [min_eq_right huz, abs_of_nonneg (sub_nonneg.mpr huz)] at *
      constructor <;> linarith
  have hcapleft (u z : ℝ) (hz : z ≤ u - δ) : cap u z = z := by
    have hzu : z - u ≤ 0 := by linarith
    have he := htail (z - u) (by rw [abs_of_nonpos hzu]; linarith)
    dsimp only [cap]
    rw [he, abs_of_nonpos hzu]
    ring
  let β : ℕ → ℝ → ℝ := fun k z => if k = 0 then a else cap (a + (k : ℝ) * h) z
  have hβ (k : ℕ) : ContDiff ℝ ∞ (β k) := by
    by_cases hk : k = 0
    · simpa only [β, if_pos hk] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => a))
    · simpa only [β, if_neg hk] using hcap (a + (k : ℝ) * h)
  have hβzero (z : ℝ) : β 0 z = a := by simp only [β, if_pos rfl]
  have hβa (k : ℕ) : β k a = a := by
    by_cases hk : k = 0
    · simp only [β, if_pos hk]
    · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      have hkh := mul_le_mul_of_nonneg_right hkR hh.le
      simp only [β, if_neg hk]
      apply hcapleft
      dsimp only [δ]
      linarith
  have hβlast (z : ℝ) (hz : z ∈ Icc a b) : β (n + 1) z = z := by
    simp only [β, Nat.add_one_ne_zero, if_false]
    apply hcapleft
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp only [δ]
    nlinarith [hz.2]
  refine ⟨n, by omega, hh, hmesh, hpoints, β, hβ, hβzero, hβa, hβlast, ?_⟩
  intro i _ z hz
  by_cases hi : i = 0
  · subst i
    right
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.zero_add, hβzero]
    constructor
    · simpa only [sub_self, abs_zero] using hε
    · have hb := hcapbounds (a + h) z
      have hlo : a ≤ min z (a + h) := le_min hz.1 (by linarith)
      have hup := min_le_right z (a + h)
      simp only [β, Nat.one_ne_zero, if_false, Nat.cast_one, one_mul]
      apply (abs_lt.mpr ⟨?_, ?_⟩).trans hmesh
      · dsimp only [δ] at hb
        linarith [hb.1]
      · linarith [hb.2]
  · let u : ℝ := a + (i : ℝ) * h
    have hbi : β i z = cap u z := by simp only [β, if_neg hi, u]
    have hbs : β (i + 1) z = cap (u + h) z := by
      simp only [β, Nat.add_one_ne_zero, if_false, Nat.cast_add, Nat.cast_one, u]
      congr 1
      ring
    rw [hbi, hbs]
    by_cases hzu : z ≤ u - δ
    · left
      rw [hcapleft u z hzu, hcapleft (u + h) z (by linarith)]
    · right
      have hzlow : u - δ ≤ z := (lt_of_not_ge hzu).le
      have hbounds (v : ℝ) (hvl : u ≤ v) (hvu : v ≤ u + h) :
          |cap v z - u| < ε := by
        have hb := hcapbounds v z
        have hlow : u - δ ≤ min z v := le_min hzlow (by linarith)
        have hupp := (min_le_right z v).trans hvu
        apply (abs_lt.mpr ⟨?_, ?_⟩).trans hmesh
        · dsimp only [δ] at hb hlow
          linarith [hb.1]
        · linarith [hb.2]
      exact ⟨hbounds u le_rfl (by linarith), hbounds (u + h) (by linarith) le_rfl⟩

end PoincareConjecture.M25.Topology3D
