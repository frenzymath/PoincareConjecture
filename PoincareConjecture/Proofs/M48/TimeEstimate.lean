import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Separation.Basic










set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M48

theorem time_estimate_extend {J E : Set ℝ} {f : ℝ → ℝ} {q A : ℝ}
    (hJ : Convex ℝ J) (hne : J.Nontrivial) (hE : E.Finite)
    (hf : ContDiffOn ℝ ∞ f J)
    (ordinary : ∀ s ∈ interior J \ E, q < f s →
      ∃ d, HasDerivAt f d s ∧ |d| ≤ A * f s ^ 2)
    (t : ℝ) (ht : t ∈ J) (hq : q < f t) :
    ∃ d, HasDerivWithinAt f d J t ∧ |d| ≤ A * f t ^ 2 := by
  have hi : (interior J).Nonempty := hJ.nontrivial_iff_nonempty_interior.mp hne
  have hu : UniqueDiffOn ℝ J := uniqueDiffOn_convex hJ hi
  let U := interior J \ E
  have hUJ : U ⊆ J := fun _ hs => interior_subset hs.1
  have hdense : J ⊆ closure U := by
    have hEc : Dense Eᶜ := by
      simpa only [sdiff_eq, univ_inter] using
        (dense_univ : Dense (univ : Set ℝ)).sdiff_finite hE
    have hsub : interior J ⊆ closure U :=
      hEc.open_subset_closure_inter isOpen_interior
    have hclose : closure (interior J) ⊆ closure U :=
      closure_minimal hsub isClosed_closure
    rw [hJ.closure_interior_eq_closure_of_nonempty_interior hi] at hclose
    exact subset_closure.trans hclose
  have : NeBot (𝓝[U] t) := mem_closure_iff_nhdsWithin_neBot.mp (hdense ht)
  have hc := (hf.continuousOn t ht).mono hUJ
  have hd := (hf.continuousOn_derivWithin hu (by simp) t ht).mono hUJ
  refine ⟨derivWithin f J t, ((hf t ht).differentiableWithinAt (by simp)).hasDerivWithinAt, ?_⟩
  apply le_of_tendsto_of_tendsto hd.abs (continuousWithinAt_const.mul (hc.pow 2))
  have hhigh : ∀ᶠ s in 𝓝[U] t, q < f s := hc.eventually (Ioi_mem_nhds hq)
  filter_upwards [self_mem_nhdsWithin, hhigh] with s hs hqs
  obtain ⟨d, hd, hb⟩ := ordinary s hs hqs
  change |derivWithin f J s| ≤ A * f s ^ 2
  simpa only [hd.hasDerivWithinAt.derivWithin (hu s (hUJ hs))] using hb

end PoincareConjecture.M48
