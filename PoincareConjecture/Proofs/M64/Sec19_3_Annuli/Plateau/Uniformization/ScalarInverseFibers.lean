import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarInverseConformal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

theorem scalarCoverMap_fiber {z w : Cover}
    (hz : z ∈ scalarCoverStrip) (hw : w ∈ scalarCoverStrip)
    (heq : scalarCoverMap z = scalarCoverMap w) :
    ∃ k : ℤ, z = w + (0, (k : ℝ)) := by
  have hzpos : 0 < z.1 := zero_lt_one.trans hz.1
  have hwpos : 0 < w.1 := zero_lt_one.trans hw.1
  have hr : z.1 = w.1 := by
    have h := congrArg norm heq
    simpa only [scalarCoverMap, scalarCirclePoint_norm,
      abs_of_pos hzpos, abs_of_pos hwpos] using h
  have hcos : Real.cos (2 * Real.pi * z.2) = Real.cos (2 * Real.pi * w.2) := by
    apply mul_left_cancel₀ hwpos.ne'
    have h := congrArg (fun p : Plane => p 0) heq
    simpa [scalarCoverMap, scalarCirclePoint, EuclideanSpace.basisFun_apply, hr] using h
  have hsin : Real.sin (2 * Real.pi * z.2) = Real.sin (2 * Real.pi * w.2) := by
    apply mul_left_cancel₀ hwpos.ne'
    have h := congrArg (fun p : Plane => p 1) heq
    simpa [scalarCoverMap, scalarCirclePoint, EuclideanSpace.basisFun_apply, hr] using h
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
    (Real.Angle.cos_sin_inj hcos hsin)
  refine ⟨k, Prod.ext (by simpa using hr) ?_⟩
  change z.2 = w.2 + (k : ℝ)
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  linear_combination hk

theorem scalarCoverChart_int_deck (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (hdeck : ∀ z ∈ e.source, e (z + (0, 1)) = e z + (0, 1))
    {z : Cover} (hz : z ∈ e.source) (k : ℤ) :
    e (z + (0, (k : ℝ))) = e z + (0, (k : ℝ)) := by
  have hdefect : Function.Periodic (fun t : ℝ => e (z.1, t) - (0, t)) 1 := by
    intro t
    have hzt : (z.1, t) ∈ e.source := by
      rw [hsource] at hz ⊢
      exact hz
    have h := hdeck (z.1, t) hzt
    simp only [Prod.mk_add_mk, add_zero] at h
    change e (z.1, t + 1) - (0, t + 1) = e (z.1, t) - (0, t)
    rw [h]
    ext <;> simp
  have h := (hdefect.int_mul k) z.2
  simp only [mul_one] at h
  change e (z.1, z.2 + (k : ℝ)) - (0, z.2 + (k : ℝ)) =
    e (z.1, z.2) - (0, z.2) at h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  have hzadd : z + (0, (k : ℝ)) = (z.1, z.2 + (k : ℝ)) := by
    ext <;> simp
  rw [hzadd]
  apply Prod.ext
  · simpa only [Prod.fst_sub, Prod.fst_add, Prod.fst_zero, sub_zero,
      add_zero, Prod.eta] using h0
  · change (e (z.1, z.2 + (k : ℝ))).2 = (e z).2 + (k : ℝ)
    simp only [Prod.snd_sub] at h1
    change (e (z.1, z.2 + (k : ℝ))).2 = (e (z.1, z.2)).2 + (k : ℝ)
    linarith

theorem scalarInverseCoverMap_fiber (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (hdeck : ∀ z ∈ e.source, e (z + (0, 1)) = e z + (0, 1))
    {y z : Cover} (hy : y ∈ e.target) (hz : z ∈ e.target)
    (heq : scalarInverseCoverMap e y = scalarInverseCoverMap e z) :
    ∃ k : ℤ, y = z + (0, (k : ℝ)) := by
  have hys := e.map_target hy
  have hzs := e.map_target hz
  obtain ⟨k, hk⟩ := scalarCoverMap_fiber (hsource ▸ hys) (hsource ▸ hzs) heq
  refine ⟨k, ?_⟩
  have h := congrArg e hk
  rw [e.right_inv hy, scalarCoverChart_int_deck e hsource hdeck hzs k,
    e.right_inv hz] at h
  exact h

theorem scalarInverseCoverMap_injOn_fundamental (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (hdeck : ∀ z ∈ e.source, e (z + (0, 1)) = e z + (0, 1)) (a : ℝ) :
    InjOn (scalarInverseCoverMap e) (e.target ∩ {y | y.2 ∈ Ico a (a + 1)}) := by
  intro y hy z hz heq
  obtain ⟨k, hk⟩ := scalarInverseCoverMap_fiber e hsource hdeck hy.1 hz.1 heq
  have hk2 : y.2 = z.2 + (k : ℝ) := congrArg Prod.snd hk
  have hlo : (-1 : ℝ) < (k : ℝ) := by linarith [hy.2.1, hz.2.2]
  have hhi : (k : ℝ) < 1 := by linarith [hy.2.2, hz.2.1]
  have hlo' : (-1 : ℤ) < k := by exact_mod_cast hlo
  have hhi' : k < 1 := by exact_mod_cast hhi
  have hk0 : k = 0 := by omega
  simpa only [hk0, Int.cast_zero, Prod.mk_zero_zero, add_zero] using hk

theorem scalarInverseCoverMap_image_fundamental (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (htarget : e.target = scalarPotentialStrip)
    (hdeck : ∀ z ∈ e.source, e (z + (0, 1)) = e z + (0, 1)) (a : ℝ) :
    scalarInverseCoverMap e '' (e.target ∩ {y | y.2 ∈ Ico a (a + 1)}) =
      scalarAnnulus := by
  apply Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact scalarCoverMap_mem (hsource ▸ e.map_target hy.1)
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := scalarCoverMap_surjOn hx
    have hzs : z ∈ e.source := hsource ▸ hz
    have hzt : e z ∈ e.target := e.map_source hzs
    let k : ℤ := ⌊(e z).2 - a⌋
    let y : Cover := ((e z).1, (e z).2 - (k : ℝ))
    have hyt : y ∈ e.target := by
      rw [htarget] at hzt ⊢
      exact hzt
    have hyfund : y.2 ∈ Ico a (a + 1) := by
      have hlo := Int.fract_nonneg ((e z).2 - a)
      have hhi := Int.fract_lt_one ((e z).2 - a)
      dsimp only [Int.fract] at hlo hhi
      change a ≤ (e z).2 - (k : ℝ) ∧ (e z).2 - (k : ℝ) < a + 1
      dsimp only [k]
      constructor <;> linarith
    have hperiod : Function.Periodic
        (fun t : ℝ => scalarInverseCoverMap e ((e z).1, t)) 1 := by
      intro t
      have ht : ((e z).1, t) ∈ e.target := by
        rw [htarget] at hzt ⊢
        exact hzt
      simpa only [Prod.mk_add_mk, add_zero] using
        scalarInverseCoverMap_periodic e hsource htarget hdeck ht
    refine ⟨y, ⟨hyt, hyfund⟩, ?_⟩
    have h := hperiod.sub_int_mul_eq (x := (e z).2) k
    change scalarInverseCoverMap e y = scalarCoverMap z
    calc
      scalarInverseCoverMap e y = scalarInverseCoverMap e (e z) := by
        simpa only [y, mul_one, Prod.eta] using h
      _ = scalarCoverMap z := by
        simp only [scalarInverseCoverMap, Function.comp_apply, e.left_inv hzs]

end PoincareConjecture.M64Uniformization
