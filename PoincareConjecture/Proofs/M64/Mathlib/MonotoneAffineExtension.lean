import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set

namespace PoincareConjecture

theorem m64Monotone_affine_periodic_extension
    {P D : ℝ} (hP : 0 < P) (f : ℝ → ℝ)
    (hc : ContinuousOn f (Icc 0 P)) (hm : MonotoneOn f (Icc 0 P))
    (hends : f P = f 0 + D) :
    ∃ F : ℝ → ℝ, Continuous F ∧ Monotone F ∧
      (∀ x, F (x + P) = F x + D) ∧ EqOn F f (Icc 0 P) := by
  let : Fact (0 < P) := ⟨hP⟩
  let g := fun x => f x - D / P * x
  have hgend : g 0 = g P := by
    dsimp only [g]
    rw [hends, div_mul_cancel₀ _ hP.ne']
    ring
  have hgc : ContinuousOn g (Icc 0 P) := hc.sub (by fun_prop)
  let U := fun x : ℝ => AddCircle.liftIco P 0 g (x : AddCircle P)
  have hUc : Continuous U := (AddCircle.liftIco_zero_continuous hgend hgc).comp
    (AddCircle.continuous_mk' P)
  have hUp : Function.Periodic U P := fun x =>
    congrArg (AddCircle.liftIco P 0 g) (AddCircle.coe_add_period P x)
  have hUeq : EqOn U g (Icc 0 P) := by
    intro x hx
    by_cases hxp : x = P
    · subst x
      change AddCircle.liftIco P 0 g (P : AddCircle P) = g P
      rw [AddCircle.coe_period, ← hgend]
      exact AddCircle.liftIco_zero_coe_apply ⟨le_rfl, hP⟩
    · exact AddCircle.liftIco_zero_coe_apply ⟨hx.1, lt_of_le_of_ne hx.2 hxp⟩
  let F := fun x => U x + D / P * x
  have hFeq : EqOn F f (Icc 0 P) := by
    intro x hx
    dsimp only [F]
    rw [hUeq hx]
    dsimp only [g]
    ring
  have hFp (x : ℝ) : F (x + P) = F x + D := by
    dsimp only [F]
    rw [hUp x, mul_add, div_mul_cancel₀ _ hP.ne']
    ring
  have hshift (x : ℝ) (z : ℤ) : F (x + (z : ℝ) * P) = F x + (z : ℝ) * D := by
    dsimp only [F]
    rw [hUp.int_mul z x]
    field_simp
    ring
  have hD : 0 ≤ D := by
    have h := hm ⟨le_rfl, hP.le⟩ ⟨hP.le, le_rfl⟩ hP.le
    linarith
  refine ⟨F, hUc.add (by fun_prop), ?_, hFp, hFeq⟩
  intro x y hxy
  let ix : ℤ := ⌊x / P⌋
  let iy : ℤ := ⌊y / P⌋
  let rx := x - (ix : ℝ) * P
  let ry := y - (iy : ℝ) * P
  have hrem (z : ℝ) : z - (⌊z / P⌋ : ℤ) * P ∈ Icc (0 : ℝ) P := by
    have hlo := (le_div_iff₀ hP).mp (Int.floor_le (z / P))
    have hhi := (div_lt_iff₀ hP).mp (Int.lt_floor_add_one (z / P))
    constructor <;> linarith
  have hrx : rx ∈ Icc 0 P := hrem x
  have hry : ry ∈ Icc 0 P := hrem y
  have hFx : F x = f rx + (ix : ℝ) * D := by
    have h := hshift rx ix
    rw [hFeq hrx] at h
    simpa only [rx, sub_add_cancel] using h
  have hFy : F y = f ry + (iy : ℝ) * D := by
    have h := hshift ry iy
    rw [hFeq hry] at h
    simpa only [ry, sub_add_cancel] using h
  rw [hFx, hFy]
  have hij : ix ≤ iy := Int.floor_mono (div_le_div_of_nonneg_right hxy hP.le)
  rcases eq_or_lt_of_le hij with heq | hlt
  · have hrxy : rx ≤ ry := by dsimp only [rx, ry]; rw [heq]; linarith
    rw [heq]
    linarith [hm hrx hry hrxy]
  · have hij' : (ix : ℝ) + 1 ≤ (iy : ℝ) := by
      exact_mod_cast (show ix + 1 ≤ iy by omega)
    have hxP := hm hrx ⟨hP.le, le_rfl⟩ hrx.2
    have h0y := hm ⟨le_rfl, hP.le⟩ hry hry.1
    have hmul := mul_le_mul_of_nonneg_right hij' hD
    rw [hends] at hxP
    nlinarith

end PoincareConjecture
