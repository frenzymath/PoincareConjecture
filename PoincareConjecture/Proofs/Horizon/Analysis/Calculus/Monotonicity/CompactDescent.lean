import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare

theorem lower_bound_of_stationary_descent
    {X : Type*} [TopologicalSpace X] {f b : X → ℝ} {m C : ℝ}
    (hf : LowerSemicontinuous f) (hb : Continuous b) (hbnonneg : ∀ x, 0 ≤ b x)
    (hcompact : ∀ t : ℝ, IsCompact {x | b x ≤ t})
    (hzero : ∀ x, b x = 0 → m ≤ f x)
    (hdescent : ∀ x, f x < min m C → 0 < b x →
      ∃ y : X, b y ≤ b x ∧
        ∃ H δ : ℝ, 0 < H ∧ 0 < δ ∧
          ∃ F : ℝ → ℝ, ∃ c : ℝ → X,
            F 0 = f x ∧ HasDerivAt F 0 0 ∧
              ∀ s ∈ Ioo 0 δ, f (c s) ≤ F s ∧ b (c s) ≤ b y - H * s) :
    ∀ x, min m C ≤ f x := by
  intro q
  by_contra hnot
  have hgap : 0 < min m C - f q := sub_pos.mpr (lt_of_not_ge hnot)
  let ε := (min m C - f q) / (2 * (b q + 1))
  have hε : 0 < ε := div_pos hgap (by linarith [hbnonneg q])
  have hεeq : ε * (b q + 1) = (min m C - f q) / 2 := by
    dsimp [ε]
    field_simp [ne_of_gt (show 0 < b q + 1 by linarith [hbnonneg q])]
  let G : X → ℝ := fun x => f x + ε * b x
  have hG : LowerSemicontinuous G :=
    hf.add ((continuous_const.mul hb).lowerSemicontinuous)
  have hGq : G q < min m C := by dsimp [G]; nlinarith
  obtain ⟨x, hx, hmin⟩ := (hG.lowerSemicontinuousOn _).exists_isMinOn
    (show ({x | b x ≤ b q} : Set X).Nonempty from ⟨q, show b q ≤ b q from le_rfl⟩)
    (hcompact (b q))
  have hGx : G x < min m C := (hmin (show b q ≤ b q from le_rfl)).trans_lt hGq
  have hfx : f x < min m C := by
    exact (le_add_of_nonneg_right (mul_nonneg hε.le (hbnonneg x))).trans_lt hGx
  have hbx : 0 < b x := by
    apply lt_of_le_of_ne (hbnonneg x)
    intro hzero'
    have h := hzero x hzero'.symm
    exact (not_lt_of_ge h) (hfx.trans_le (min_le_left _ _))
  obtain ⟨y, hby, H, δ, hH, hδ, F, c, hF0, hFd, hbound⟩ :=
    hdescent x hfx hbx
  have hslope : ∀ᶠ s in 𝓝[>] (0 : ℝ), slope F 0 s < ε * H :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hFd).2
      (Iio_mem_nhds (mul_pos hε hH))
  have hnear : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδ
  obtain ⟨s, hslope, hs⟩ := (hslope.and hnear).exists
  obtain ⟨hfs, hbs⟩ := hbound s hs
  have hcs : b (c s) ≤ b q := hbs.trans
    ((sub_le_self _ (mul_pos hH hs.1).le).trans (hby.trans hx))
  have hminimal := hmin hcs
  have hchange : F s - f x < ε * H * s := by
    rw [slope_def_field, sub_zero, hF0, div_lt_iff₀ hs.1] at hslope
    exact hslope
  have hbs' := mul_le_mul_of_nonneg_left hbs hε.le
  have hby' := mul_le_mul_of_nonneg_left hby hε.le
  dsimp [G] at hminimal
  nlinarith

end Poincare
