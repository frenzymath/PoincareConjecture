import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.FunProp








set_option autoImplicit false

namespace PoincareConjecture.M65



theorem closedInterval_difference_bound {a b K : ℝ} (hab : a < b)
    (f : Set.Icc a b → ℝ) (hf : Continuous f)
    (hbound : ∀ (s t : ℝ) (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b), s ≤ t →
      |f ⟨t, Set.Ioo_subset_Icc_self ht⟩ - f ⟨s, Set.Ioo_subset_Icc_self hs⟩| ≤ K * (t - s))
    (s t : Set.Icc a b) : |f t - f s| ≤ K * |(t : ℝ) - s| := by
  let f' : ℝ → ℝ := fun r => f (Set.projIcc a b hab.le r)
  have hf' : Continuous f' := hf.comp continuous_projIcc
  have hlocal : ∀ p ∈ (Set.Ioo a b).prod (Set.Ioo a b),
      |f' p.2 - f' p.1| ≤ K * |p.2 - p.1| := by
    intro p hp
    dsimp only [f']
    rw [Set.projIcc_of_mem hab.le (Set.Ioo_subset_Icc_self hp.2),
      Set.projIcc_of_mem hab.le (Set.Ioo_subset_Icc_self hp.1)]
    rcases le_total p.1 p.2 with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      exact hbound p.1 p.2 hp.1 hp.2 h
    · rw [abs_sub_comm (f _), abs_sub_comm p.2,
        abs_of_nonneg (sub_nonneg.mpr h)]
      exact hbound p.2 p.1 hp.2 hp.1 h
  have hclosed := le_on_closure hlocal
    (((hf'.comp continuous_snd).sub (hf'.comp continuous_fst)).abs.continuousOn)
    ((continuous_const.mul ((continuous_snd.sub continuous_fst).abs)).continuousOn)
  have hp : ((s : ℝ), (t : ℝ)) ∈ closure ((Set.Ioo a b).prod (Set.Ioo a b)) := by
    have hs : (s : ℝ) ∈ closure (Set.Ioo a b) := by rw [closure_Ioo hab.ne]; exact s.2
    have ht : (t : ℝ) ∈ closure (Set.Ioo a b) := by rw [closure_Ioo hab.ne]; exact t.2
    exact (closure_prod_eq (s := Set.Ioo a b) (t := Set.Ioo a b)).symm ▸ ⟨hs, ht⟩
  simpa only [f', Set.projIcc_val] using hclosed hp

end PoincareConjecture.M65
