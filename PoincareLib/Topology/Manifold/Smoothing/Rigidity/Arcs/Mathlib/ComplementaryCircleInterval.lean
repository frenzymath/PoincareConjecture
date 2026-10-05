import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Tactic.Linarith

/-!
# The complete circle interval outside a short open arc

Both endpoints are retained and remain distinct. The exact image
uses the original quotient, with no change of boundary marking.
See rigidity041, section1.
-/

set_option autoImplicit false

open Set

namespace AddCircle

variable {p : ℝ} [Fact (0 < p)]

/-- The whole complementary closed interval lies in one injective
period range. See rigidity041, section1. -/
theorem injOn_coe_complementaryInterval {a : ℝ} (ha : 0 < a) :
    InjOn (fun t : ℝ => (t : AddCircle p)) (Icc a (p - a)) := by
  intro t ht u hu heq
  apply (coe_eq_coe_iff_of_mem_Ico (a := 0) (p := p) ?_ ?_).mp heq
  · exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- The full closed complementary interval is exactly the
complement of the removed open quotient arc. See rigidity041. -/
theorem image_coe_complementaryInterval {a : ℝ}
    (ha : 0 < a) (hap : a < p / 2) :
    (fun t : ℝ => (t : AddCircle p)) '' Icc a (p - a) =
      ((fun t : ℝ => (t : AddCircle p)) '' Ioo (-a) a)ᶜ := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩ ⟨u, hu, heq⟩
    have htI : t ∈ Ico (0 : ℝ) (0 + p) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    by_cases hu0 : 0 ≤ u
    · have huI : u ∈ Ico (0 : ℝ) (0 + p) :=
        ⟨hu0, by linarith [hu.2]⟩
      have hut : u = t := (coe_eq_coe_iff_of_mem_Ico huI htI).mp heq
      linarith [hu.2, ht.1]
    · have huI : u + p ∈ Ico (0 : ℝ) (0 + p) :=
        ⟨by linarith [hu.1], by linarith⟩
      have heq' : ((u + p : ℝ) : AddCircle p) = (t : AddCircle p) :=
        (coe_add_period p u).trans heq
      have hut : u + p = t := (coe_eq_coe_iff_of_mem_Ico huI htI).mp heq'
      linarith [hu.1, ht.2]
  · intro hz
    obtain ⟨t, ht, htz⟩ := eq_coe_Ico z
    have hat : a ≤ t := by
      by_contra! hta
      exact hz ⟨t, ⟨by linarith [ht.1], hta⟩, htz⟩
    have hta : t ≤ p - a := by
      by_contra! hat
      apply hz
      refine ⟨t - p, ⟨by linarith, by linarith [ht.2]⟩, ?_⟩
      change ((t - p : ℝ) : AddCircle p) = z
      rw [coe_sub, coe_period, sub_zero]
      exact htz
    exact ⟨t, ⟨hat, hta⟩, htz⟩

omit [Fact (0 < p)] in
/-- The upper retained endpoint has the literal negative lower
endpoint value in the original quotient. See rigidity041. -/
theorem coe_period_sub (a : ℝ) :
    ((p - a : ℝ) : AddCircle p) = ((-a : ℝ) : AddCircle p) := by
  rw [coe_sub, coe_period, zero_sub, coe_neg]

end AddCircle
