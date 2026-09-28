import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundarySubdivision






noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators

namespace PoincareConjecture.M64






theorem exists_subordinate_scaled_subdivision {a b r : ℝ} (hab : a < b) (hr : 0 < r)
    (e : ℝ → ℝ) (he : ∀ x, 0 < e x) :
    ∃ N : ℕ, 0 < N ∧ ∃ tag : Fin N → ℝ, ∀ i : Fin N,
      Icc ((a + (b - a) * (i : ℝ) / N - tag i) / r)
        ((a + (b - a) * ((i : ℝ) + 1) / N - tag i) / r) ⊆
          Icc (-(e (tag i))) (e (tag i)) := by
  let U := fun x => Ioo (x - r * e x) (x + r * e x)
  have hcover : Icc a b ⊆ ⋃ x, U x := by
    intro x _hx
    exact mem_iUnion.mpr ⟨x, sub_lt_self _ (mul_pos hr (he x)),
      lt_add_of_pos_right _ (mul_pos hr (he x))⟩
  obtain ⟨N, hN, tag, htag⟩ := M65Gauss.exists_subordinate_uniform_subdivision
    hab U (fun _ => isOpen_Ioo) hcover
  refine ⟨N, hN, tag, ?_⟩
  intro i t ht
  have hlow := (div_le_iff₀ hr).mp ht.1
  have hupp := (le_div_iff₀ hr).mp ht.2
  have hh := htag i (show tag i + r * t ∈
      Icc (a + (b - a) * (i : ℝ) / N)
        (a + (b - a) * ((i : ℝ) + 1) / N) by
    constructor <;> nlinarith only [hlow, hupp])
  change tag i - r * e (tag i) < tag i + r * t ∧
    tag i + r * t < tag i + r * e (tag i) at hh
  constructor <;> nlinarith only [hh.1, hh.2, hr]






theorem scaled_subdivision_integral {N : ℕ} (v : ℕ → ℝ) (tag : Fin N → ℝ)
    {r : ℝ} (hr : r ≠ 0) (f : ℝ → ℝ)
    (hf : ∀ k < N, IntervalIntegrable f volume (v k) (v (k + 1))) :
    (∑ i : Fin N, ∫ t in ((v i - tag i) / r)..((v (i.val + 1) - tag i) / r),
      r * f (tag i + r * t)) = ∫ t in v 0..v N, f t := by
  have hcell (i : Fin N) :
      (∫ t in ((v i - tag i) / r)..((v (i.val + 1) - tag i) / r),
        r * f (tag i + r * t)) = ∫ t in v i..v (i.val + 1), f t := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_mul f hr]
    simp only [smul_eq_mul, mul_div_cancel₀ _ hr, add_sub_cancel,
      ← mul_assoc, mul_inv_cancel₀ hr, one_mul]
  simp_rw [hcell]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∫ t in v k..v (k + 1), f t) N]
  exact intervalIntegral.sum_integral_adjacent_intervals hf

end PoincareConjecture.M64
