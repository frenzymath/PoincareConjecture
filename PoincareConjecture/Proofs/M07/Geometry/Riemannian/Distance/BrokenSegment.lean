import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith












set_option autoImplicit false

open scoped ENNReal

namespace Poincare.MetricCurves

variable {X : Type*} [PseudoEMetricSpace X]



theorem edist_eq_of_broken_segment
    {a b c x y : X} {A B s t : ℝ}
    (hs : 0 ≤ s) (hsA : s ≤ A) (ht : 0 ≤ t) (htB : t ≤ B)
    (hab : edist a b = ENNReal.ofReal (A + B))
    (hax : edist a x ≤ ENNReal.ofReal (A - s))
    (hxc : edist x c ≤ ENNReal.ofReal s)
    (hcy : edist c y ≤ ENNReal.ofReal t)
    (hyb : edist y b ≤ ENNReal.ofReal (B - t)) :
    edist x y = ENNReal.ofReal (s + t) := by
  apply le_antisymm
  · calc
      edist x y ≤ edist x c + edist c y := edist_triangle _ _ _
      _ ≤ ENNReal.ofReal s + ENNReal.ofReal t := add_le_add hxc hcy
      _ = ENNReal.ofReal (s + t) := (ENNReal.ofReal_add hs ht).symm
  · have h := (edist_triangle a x b).trans
      (add_le_add hax ((edist_triangle x y b).trans (add_le_add_right hyb _)))
    rw [hab] at h
    have heq : ENNReal.ofReal (A + B) =
        ENNReal.ofReal (A - s) +
          (ENNReal.ofReal (s + t) + ENNReal.ofReal (B - t)) := by
      rw [← ENNReal.ofReal_add (add_nonneg hs ht) (sub_nonneg.mpr htB),
        ← ENNReal.ofReal_add (sub_nonneg.mpr hsA)
          (by linarith : 0 ≤ s + t + (B - t))]
      congr 1
      ring
    rw [heq] at h
    exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top
      (ENNReal.le_of_add_le_add_left ENNReal.ofReal_ne_top h)



theorem edist_add_eq_of_add_eq
    {p x z q : X}
    (hfinite : edist z q ≠ ⊤)
    (hpxq : edist p x + edist x q = edist p q)
    (hxzq : edist x z + edist z q = edist x q) :
    edist p x + edist x z = edist p z := by
  apply le_antisymm
  · apply ENNReal.le_of_add_le_add_right hfinite
    calc
      (edist p x + edist x z) + edist z q = edist p q := by
        rw [add_assoc, hxzq, hpxq]
      _ ≤ edist p z + edist z q := edist_triangle _ _ _
  · exact edist_triangle _ _ _

end Poincare.MetricCurves
