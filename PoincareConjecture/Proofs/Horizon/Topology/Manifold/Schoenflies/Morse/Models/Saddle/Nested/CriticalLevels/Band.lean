import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.CriticalLevels.Bounds

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem saddle_height_lt_fortyone_fortieths {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8)) :
    height p < (41 / 40 : Real) := by
  obtain ⟨hy, hc⟩ := critical_point_coordinates hp
  have hn : ((p : E3) 0)^2 + ((p : E3) 2)^2 = 1 := by
    have hn := EuclideanSpace.norm_sq_eq (p : E3)
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hy] at hn
    exact hn.symm
  have hx : (p : E3) 0 < 0 := by
    by_contra hh
    have hmul : 0 ≤ (p : E3) 0 * (2 * (p : E3) 2 - 1) :=
      mul_nonneg (le_of_not_gt hh) (by linarith [hz.1])
    nlinarith [hz.1]
  have hxb : (p : E3) 0 < -(3 / 4 : Real) := by nlinarith [hz.1, hz.2]
  rw [height_apply, hy]
  nlinarith [sq_nonneg ((p : E3) 2 - 1 / 2)]

theorem critical_in_height_band_iff_eq_saddle {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    (q : S2) (hq : height q ∈ Icc (1 : Real) (13 / 10)) :
    mfderiv (𝓡 2) 𝓘(Real, Real) height q = 0 ↔ q = p := by
  constructor
  · intro hqcrit
    exact critical_latitude_unique_in_saddle_interval hqcrit hp
      (Ioo_subset_Icc_self (critical_latitude_in_saddle_interval_of_height_band hqcrit hq))
      (Ioo_subset_Icc_self hpz)
  · rintro rfl
    exact hp

theorem exists_unique_critical_point_in_height_band :
    ∃ p : S2,
      (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8) ∧
      height p ∈ Ioo (1 : Real) (41 / 40) ∧
      mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0 ∧
      ∀ q : S2, height q ∈ Icc (1 : Real) (13 / 10) →
        (mfderiv (𝓡 2) 𝓘(Real, Real) height q = 0 ↔ q = p) := by
  obtain ⟨p, hl, hu, _, _, hp, hh⟩ := exists_critical_point_above_nested_cut
  exact ⟨p, ⟨hl, hu⟩, ⟨hh, saddle_height_lt_fortyone_fortieths hp ⟨hl, hu⟩⟩,
    hp, critical_in_height_band_iff_eq_saddle hp ⟨hl, hu⟩⟩

theorem nested_cutting_heights_regular (q : S2) (hq : height q = 1 ∨ height q = 13 / 10) :
    mfderiv (𝓡 2) 𝓘(Real, Real) height q ≠ 0 := by
  obtain ⟨p, _, hh, _, hunique⟩ := exists_unique_critical_point_in_height_band
  intro hcrit
  have hband : height q ∈ Icc (1 : Real) (13 / 10) := by
    rcases hq with hq | hq <;> rw [hq] <;> constructor <;> norm_num
  have he := (hunique q hband).mp hcrit
  subst q
  rcases hq with hq | hq <;> linarith [hh.1, hh.2]

end Poincare.Manifold.Schoenflies.Saddle.Nested
