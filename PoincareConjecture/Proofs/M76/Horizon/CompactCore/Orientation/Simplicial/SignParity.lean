import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Simplicial.OrderedTriangleBoundary
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace Geometry

def orientationSignParity (s : SignType) : ZMod 2 := if s = 1 then 0 else 1

theorem orientationSignParity_boundary_cancellation
    (a b : SignType) (ha : a ≠ 0) (hb : b ≠ 0) (i j : Fin 3)
    (h : (((-1 : SignType) ^ i.val) * a) * (((-1 : SignType) ^ j.val) * b) = -1) :
    (orientationSignParity a + (i.val : ZMod 2)) +
      (orientationSignParity b + (j.val : ZMod 2)) = 1 := by
  cases a <;> cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [orientationSignParity, pow_two] at * <;> decide

theorem orientationSignParity_of_opposite_determinants
    (a b c : SignType) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (x y : ℝ) (hA : a = c * SignType.sign x) (hB : b = c * SignType.sign y)
    (i j : Fin 3)
    (hprod : ((-1 : ℝ) ^ i.val * x) * ((-1 : ℝ) ^ j.val * y) < 0) :
    (orientationSignParity a + (i.val : ZMod 2)) +
      (orientationSignParity b + (j.val : ZMod 2)) = 1 := by
  have hcc : c * c = 1 := by cases c <;> simp_all
  have hs := sign_neg hprod
  have hm : SignType.sign (-1 : ℝ) = -1 := sign_neg (by norm_num)
  simp only [sign_mul, sign_pow, hm] at hs
  apply orientationSignParity_boundary_cancellation a b ha hb i j
  rw [hA, hB]
  calc
    _ = (c * c) * (((-1 : SignType) ^ i.val * SignType.sign x) *
        ((-1 : SignType) ^ j.val * SignType.sign y)) := by ac_rfl
    _ = -1 := by rw [hcc, one_mul, hs]

theorem orientationSignParity_of_common_label
    (x y : ℝ) (c : SignType) (hc : c ≠ 0) (i j : Fin 3)
    (hprod : ((-1 : ℝ) ^ i.val * x) * ((-1 : ℝ) ^ j.val * y) < 0) :
    (orientationSignParity (c * SignType.sign x) + (i.val : ZMod 2)) +
      (orientationSignParity (c * SignType.sign y) + (j.val : ZMod 2)) = 1 := by
  have hx : x ≠ 0 := by intro he; simp [he] at hprod
  have hy : y ≠ 0 := by intro he; simp [he] at hprod
  exact orientationSignParity_of_opposite_determinants _ _ c
    (mul_ne_zero hc (sign_ne_zero.mpr hx)) (mul_ne_zero hc (sign_ne_zero.mpr hy))
    hc x y rfl rfl i j hprod

end Geometry
