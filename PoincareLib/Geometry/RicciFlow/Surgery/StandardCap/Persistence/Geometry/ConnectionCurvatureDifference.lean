import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Tactic.Abel

/-!
# Algebra of a connection change

The curvature of a connection changed by a symmetric bilinear tensor is
the old curvature plus its covariant derivative and quadratic correction.
This is the algebraic step in the perturbation calculation on Morgan--Tian,
pp. 3-7; see M44 derivation 31.
-/

set_option autoImplicit false

namespace PoincareMT.M44

/-- The curvature change identity for bilinear coefficients and their
derivatives. The only torsion hypothesis needed is symmetry of the
background coefficients in the two curvature directions. Source:
Morgan--Tian, pp. 3-7, in M44 derivation 31. -/
theorem connection_curvature_difference_algebra
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : V →L[ℝ] V →L[ℝ] V)
    (DA DB : V →L[ℝ] V →L[ℝ] V →L[ℝ] V)
    (u v w : V) (hA : A u v = A v u) :
    DB u v w - DB v u w + B u (B v w) - B v (B u w) =
      (DA u v w - DA v u w + A u (A v w) - A v (A u w)) +
      (((DB - DA) u v w + A u ((B - A) v w) -
          (B - A) (A u v) w - (B - A) v (A u w)) -
        ((DB - DA) v u w + A v ((B - A) u w) -
          (B - A) (A v u) w - (B - A) u (A v w))) +
      ((B - A) u ((B - A) v w) - (B - A) v ((B - A) u w)) := by
  simp only [sub_apply, map_sub, hA]
  abel

end PoincareMT.M44
