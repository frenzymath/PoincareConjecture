import Mathlib.Analysis.Normed.Module.Basic






set_option autoImplicit false

open Set

namespace PoincareConjecture





theorem m64_radial_injOn_of_positive_rescale
    {E X : Type*} [AddCommGroup E] [Module ℝ E]
    (e : E → X) {theta : E} {B : ℝ} (hB : 0 < B)
    (hi : InjOn (fun t : ℝ => e (t • B • theta)) (Icc (0 : ℝ) 1)) :
    InjOn (fun s : ℝ => e (s • theta)) (Icc 0 B) := by
  intro s hs t ht heq
  have hscaled := hi
    ⟨div_nonneg hs.1 hB.le, (div_le_one hB).mpr hs.2⟩
    ⟨div_nonneg ht.1 hB.le, (div_le_one hB).mpr ht.2⟩
    (by simpa only [smul_smul, div_mul_cancel₀ _ hB.ne'] using heq)
  exact (div_left_inj' hB.ne').mp hscaled





theorem m64_radial_same_direction_endpoint_eq
    {E X : Type*} [AddCommGroup E] [Module ℝ E]
    (e : E → X) {theta v : E} {B s c : ℝ}
    (hs : s ∈ Icc 0 B) (hc : 0 < c) (hv : v = c • theta)
    (hi : InjOn (fun t : ℝ => e (t • v)) (Icc (0 : ℝ) 1))
    (hj : InjOn (fun t : ℝ => e (t • theta)) (Icc (0 : ℝ) B))
    (he : e v = e (s • theta)) : v = s • theta := by
  rcases le_total c s with hcs | hsc
  · have h : c = s := hj ⟨hc.le, hcs.trans hs.2⟩ hs (by simpa only [← hv] using he)
    simpa only [h] using hv
  · have ht : s / c ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hs.1 hc.le, (div_le_one hc).mpr hsc⟩
    have hscaled : (s / c) • v = s • theta := by
      rw [hv, smul_smul, div_mul_cancel₀ _ hc.ne']
    have heq : s / c = 1 := hi ht ⟨zero_le_one, le_rfl⟩ (by
      simpa only [hscaled, one_smul] using he.symm)
    have h : s = c := (div_eq_one_iff_eq hc.ne').mp heq
    simpa only [h] using hv





theorem m64_radial_noncanonical_prefix_ne
    {E X : Type*} [AddCommGroup E] [Module ℝ E]
    (e : E → X) {theta v : E} {B s t u : ℝ}
    (hs : s ∈ Icc 0 B) (ht : 0 < t) (hu : 0 < u)
    (hi : InjOn (fun a : ℝ => e (a • v)) (Icc (0 : ℝ) 1))
    (hj : InjOn (fun a : ℝ => e (a • theta)) (Icc (0 : ℝ) B))
    (he : e v = e (s • theta)) (hne : v ≠ s • theta) : t • v ≠ u • theta := by
  intro heq
  have hv : v = (u / t) • theta := by
    have h := congrArg (fun w : E => t⁻¹ • w) heq
    simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul,
      div_eq_mul_inv, mul_comm] using h
  exact hne (m64_radial_same_direction_endpoint_eq e hs (div_pos hu ht) hv hi hj he)

end PoincareConjecture
