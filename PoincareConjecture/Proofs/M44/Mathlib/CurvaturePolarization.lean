import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

set_option maxSynthPendingDepth 8

namespace PoincareConjecture.M44

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem curvatureForm_eq_zero_of_planes
    (R : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hcyclic : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (hplane : ∀ a b, R a b a b = 0) (a b c d : E) : R a b c d = 0 := by
  have hone (u v w : E) : R u v u w = 0 := by
    have h := hplane u (v + w)
    simp only [map_add, LinearMap.add_apply] at h
    rw [hplane, hplane, hpair u w u v] at h
    linarith only [h]
  have htwo (u v w z : E) : R u v w z + R w v u z = 0 := by
    have h := hone (u + w) v z
    simp only [map_add, LinearMap.add_apply] at h
    rw [hone, hone] at h
    linarith only [h]
  linarith only [htwo a b c d, htwo b a c d,
    hfirst b a c d, hfirst c b a d, hcyclic a b c d]

theorem curvatureForm_eq_of_planes
    (R S : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hRfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hRpair : ∀ a b c d, R a b c d = R c d a b)
    (hRcyclic : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (hSfirst : ∀ a b c d, S a b c d = -S b a c d)
    (hSpair : ∀ a b c d, S a b c d = S c d a b)
    (hScyclic : ∀ a b c d, S a b c d + S b c a d + S c a b d = 0)
    (hplane : ∀ a b, R a b a b = S a b a b) : R = S := by
  ext a b c d
  apply sub_eq_zero.mp
  apply curvatureForm_eq_zero_of_planes
    (R - S : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
  · intro u v w z
    simp only [LinearMap.sub_apply]
    rw [hRfirst, hSfirst]
    ring
  · intro u v w z
    simp only [LinearMap.sub_apply]
    rw [hRpair, hSpair]
  · intro u v w z
    simp only [LinearMap.sub_apply]
    linarith only [hRcyclic u v w z, hScyclic u v w z]
  · intro u v
    simp only [LinearMap.sub_apply, hplane, sub_self]

end PoincareConjecture.M44
